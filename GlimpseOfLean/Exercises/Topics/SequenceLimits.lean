import GlimpseOfLean.Library.Basic

/-
In this file we manipulate the elementary definition of limits of
sequences of real numbers.
mathlib has a much more general definition of limits, but here
we want to practice using the logical operators and relations
covered in the previous files.
-/

/-
Before we start on, let us make sure Lean doesn't need so much help to
prove equalities or inequalities that linearly follow from known
equalities and inequalities. This is the job of the linear arithmetic
tactic: `linarith`.
-/

example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith

/-
Let's prove some exercises using `linarith`.
-/

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by {
  linarith
}

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by {
  linarith
}

/-
A sequence `u` is a function from `ℕ` to `ℝ`, hence Lean says
`u : ℕ → ℝ`
The definition we'll be using is:

-- Definition of « u tends to l »
`def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

Note the use of `∀ ε > 0, _` which is an abbreviation of
`∀ ε, ε > 0 → _ `

In particular, a statement like `h : ∀ ε > 0, _`
can be specialized to a given `ε₀` by
  `specialize h ε₀ hε₀`
where `hε₀` is a proof of `ε₀ > 0`.

Also note that, wherever Lean expects some proof term, we can
start a tactic mode proof using the keyword `by`.
For instance, if the local context contains:

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

then we can specialize h to the real number δ/2 using:
  `specialize h (δ/2) (by linarith)`
where `by linarith` will provide the proof of `δ/2 > 0` expected by Lean.
-/

/- If u is constant with value l then u tends to l.
Hint: `simp` can rewrite `|1 - 1|` to `0` -/
example (h : ∀ n, u n = l) : seq_limit u l := by {
  intro ε hε
  use 0
  intro n _
  rw [h]
  simp
  linarith
}

/- When dealing with absolute values, we'll use lemmas:

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

We will also use variants of the triangle inequality

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
or
`abs_sub_le  (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
or the primed version:
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`
-/

-- Assume `l > 0`. Then `u` ts to `l` implies `u n ≥ l/2` for large enough `n`
example (h : seq_limit u l) (hl : l > 0) :
    ∃ N, ∀ n ≥ N, u n ≥ l/2 := by {
  unfold seq_limit at h
  have h2 : (l/2) > 0 := by linarith
  specialize h (l/2) h2
  rcases h with ⟨N, hN⟩
  use N
  intro n hn
  specialize hN n hn
  rw [abs_le] at hN
  linarith
}

/-
When dealing with max, you can use

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

Let's see an example.
-/

-- If `u` tends to `l` and `v` tends `l'` then `u+v` tends to `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
    seq_limit (u + v) (l + l') := by {
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨_hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2 := hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2 := hN₂ n (by linarith)

  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]
}


/- Let's do something similar: the squeezing theorem. -/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  intro ε hε
  have h2 : (ε/3) > 0 := by linarith
  specialize hu (ε/3) h2
  specialize hw (ε/3) h2
  rcases hu with ⟨Nu, hNu⟩
  rcases hw with ⟨Nw, hNw⟩
  use (max Nu Nw)
  intro n hmax
  rw [ge_max_iff] at hmax
  rcases hmax with ⟨hnNu, hnNw⟩
  specialize hNu n hnNu
  specialize hNw n hnNw
  have huw : |u n - w n| ≤ 2*ε/3 := by {
    calc
    |u n - w n| ≤ |u n - l| + |w n - l| := by { apply abs_sub_le' (u n) l (w n) }
              _ ≤ ε/3 + ε/3 := by { linarith }
              _ = 2*ε/3 := by { ring }
  }
  have hvw : |v n - w n| ≤ 2*ε/3 := by {
    specialize h n
    specialize h' n
    rw [abs_le] at huw
    rcases huw with ⟨huw1, _⟩
    rw [abs_le]
    constructor
    . linarith
    . linarith
  }
  calc
    |v n - l| ≤ |v n - w n| + |w n - l| := by { apply abs_sub_le (v n) (w n) l }
            _ ≤ 2*ε/3 + ε/3 := by { linarith }
            _ = ε := by { ring }
}

/- An alternative proof of the squeezing theorem suggested by Pascalin Amabegnon. -/
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  intro ε hε
  specialize hu ε hε
  specialize hw ε hε
  rcases hu with ⟨Nu, hNu⟩
  rcases hw with ⟨Nw, hNw⟩
  use (max Nu Nw)
  intro n hmax
  have hw' : w n - l ≤ ε := by {
    have hnw : n ≥ Nw := by { exact le_of_max_le_right hmax }
    specialize hNw n hnw
    rw [abs_le] at hNw
    linarith
  }
  have hu' : u n - l ≥ -ε := by {
    have hnu : n ≥ Nu := by { exact le_of_max_le_left hmax }
    specialize hNu n hnu
    rw [abs_le] at hNu
    linarith
  }
  have hvw : v n - l ≤ ε := by {
    specialize h' n
    linarith
  }
  have hvu : v n - l ≥ -ε := by {
    specialize h n
    linarith
  }
  rw [abs_le]
  constructor
  . linarith
  . linarith
}

/- In the next exercise, we'll use

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

Recall we listed three variations on the triangle inequality at the beginning of this file.
-/

-- A sequence admits at most one limit. You will be able to use that lemma in the following
-- exercises.
lemma uniq_limit : seq_limit u l → seq_limit u l' → l = l' := by {
  intro h h'
  have lem : ∀ ε > 0, |l - l'| ≤ ε := by {
    intro ε hε
    have hε2 : ε/2 > 0 := by {linarith }
    specialize h (ε/2) hε2
    specialize h' (ε/2) hε2
    rcases h with ⟨N, hN⟩
    rcases h' with ⟨N', hN'⟩
    have hmaxN : max N N' ≥ N := by { apply le_max_left }
    have hmaxN' : max N N' ≥ N' := by { apply le_max_right }
    specialize hN (max N N') hmaxN
    specialize hN' (max N N') hmaxN'
    calc
      |l - l'| ≤ |l - u (max N N')| + |u (max N N') - l'| := by {
        apply abs_sub_le l (u (max N N')) l'
      }
             _ = |u (max N N') - l| + |u (max N N') - l'| := by { rw [abs_sub_comm] }
             _ ≤ ε := by { linarith }
  }
  apply eq_of_abs_sub_le_all
  exact lem
}


/-
Let's now practice deciphering definitions before proving.
-/

def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by {
  intro ε hε
  rcases h with ⟨h1, h2⟩
  specialize h2 ε hε
  rcases h2 with ⟨n₀, hn₀⟩
  use n₀
  intro n hn
  unfold non_decreasing at h'
  have hn1 : u n₀ ≤ u n := by { apply h' ; linarith }
  have hn2 : u n ≤ M := by { apply h1 }
  rw [abs_le]
  constructor
  . linarith
  . linarith
}

/-
We will now play with subsequences.

The new definition we will use is that `φ : ℕ → ℕ` is an extraction
if it is (strictly) increasing.

`def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`

In the following, `φ` will always denote a function from `ℕ` to `ℕ`.

The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by {
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])
}


/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
-/

/-- Extractions take arbitrarily large values for arbitrarily large
inputs. -/
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by {
  intro hyp N N'
  use (max N N')
  constructor
  . apply le_max_right
  . calc
    φ (max N N') ≥ max N N' := by { apply id_le_extraction' ; exact hyp }
               _ ≥ N := by { apply le_max_left }
}

/- A real number `a` is a cluster point of a sequence `u`
if `u` has a subsequence converging to `a`.

`def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a`
-/

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by {
  intro hcp ε hε N
  unfold cluster_point at hcp
  rcases hcp with ⟨e, ⟨he, hsl⟩⟩
  specialize hsl ε hε
  rcases hsl with ⟨N1, h1⟩
  have h2 : ∃ n ≥ N1, e n ≥ N := by { apply (extraction_ge he N N1) }
  rcases h2 with ⟨n, ⟨hn2, he2⟩⟩
  specialize h1 n hn2
  use (e n)
  tauto
}

/-- If `u` tends to `l` then its subsequences tend to `l`. -/
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by {
  intro ε hε
  specialize h ε hε
  rcases h with ⟨N, hN⟩
  use N
  intro n hn
  have h1 : φ n ≥ n := by {
    apply id_le_extraction'
    apply hφ
  }
  have h2 : φ n ≥ N := by { linarith }
  specialize hN (φ n) h2
  tauto
}

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by {
  unfold cluster_point at ha
  rcases ha with ⟨e, ⟨he, hsl⟩⟩
  have hsl' : seq_limit (u ∘ e) l := by {
    apply (subseq_tendsto_of_tendsto' hl he)
  }
  apply (uniq_limit hsl hsl')
}

/-- Cauchy_sequence sequence -/
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by {
  sorry
}

/-
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/

example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  sorry
