/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Probability.DTMCReachability

/-!
# Exact-rational checking for next and bounded until

A computable rational recursion evaluates the horizon probabilities of
`DTMCReachability` exactly; it agrees with the first-hit path-sum
definition on every genuine chain. The next-step probability is, by
definition, the one-step sum of transition probabilities into the
target set. Threshold comparisons (five directions, against rational
thresholds) are decided on those values. Guarded entry points first
validate that a raw matrix is stochastic and reject it otherwise: a
guarded `false` means the matrix was rejected or the formula fails;
call `stochastic` to tell the two apart. Background: C. Baier and J.-P. Katoen,
*Principles of Model Checking*, MIT Press, 2008, Chapter 10.
-/

@[expose] public section

namespace Cslib.Probability

variable {S : Type*} [Fintype S] [DecidableEq S] (A B : Finset S)

/-- A computable rational evaluation of the horizon probabilities, by
the Bellman recursion. Its agreement with the path-sum definition is
`hitProbC_eq`. This is the reference recursion: it recomputes
sub-horizons for every state, so its cost is exponential in the
horizon; it is not memoized. -/
def hitProbC (P : S → S → ℚ) (A B : Finset S) : ℕ → S → ℚ
  | 0 => fun s => if s ∈ B then 1 else 0
  | (n + 1) => fun s =>
      if s ∈ B then 1 else if s ∉ A then 0
        else ∑ t, P s t * hitProbC P A B n t

/-- Threshold comparisons for probabilistic formulae. -/
inductive Cmp where
  | le | lt | eq | ge | gt
deriving DecidableEq, Repr

/-- The proposition a comparison expresses. -/
def Cmp.holds : Cmp → ℚ → ℚ → Prop
  | .le, x, q => x ≤ q
  | .lt, x, q => x < q
  | .eq, x, q => x = q
  | .ge, x, q => x ≥ q
  | .gt, x, q => x > q

/-- The decision procedure for a comparison. -/
def Cmp.eval : Cmp → ℚ → ℚ → Bool
  | .le, x, q => decide (x ≤ q)
  | .lt, x, q => decide (x < q)
  | .eq, x, q => decide (x = q)
  | .ge, x, q => decide (x ≥ q)
  | .gt, x, q => decide (x > q)

/-- The decision procedure agrees with the expressed comparison, for
every comparison and all rationals. -/
theorem cmp_eval_correct (c : Cmp) (x q : ℚ) :
    c.eval x q = true ↔ c.holds x q := by
  cases c <;> simp [Cmp.eval, Cmp.holds]

/-- Exact-rational check of a next-step threshold formula: the
probability of being in `A` after one step, compared against `q`. -/
def checkNext (P : S → S → ℚ) (A : Finset S) (s : S) (c : Cmp) (q : ℚ) :
    Bool :=
  c.eval (∑ t ∈ A, P s t) q

/-- Exact-rational check of a bounded-until threshold formula over
horizon `k`. -/
def checkBoundedUntil (P : S → S → ℚ) (A B : Finset S) (k : ℕ) (s : S)
    (c : Cmp) (q : ℚ) : Bool :=
  c.eval (hitProbC P A B k s) q

/-- Decidable validation of a raw rational matrix: nonnegative entries
and every row summing to `1`. -/
def stochastic (P : S → S → ℚ) : Bool :=
  decide (∀ s t, 0 ≤ P s t) && decide (∀ s, ∑ t, P s t = 1)

omit [DecidableEq S] in
/-- Every genuine chain passes validation. -/
theorem stochastic_complete (D : DTMC S) : stochastic D.P = true := by
  simp only [stochastic, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨D.nonneg, D.row_sum⟩

/-- The computable evaluation agrees with the path-sum definition on
every genuine chain. -/
theorem hitProbC_eq (D : DTMC S) (n : ℕ) (s : S) :
    hitProbC D.P A B n s = D.hitProb A B n s := by
  induction n generalizing s with
  | zero =>
    by_cases hs : s ∈ B <;> simp only [hitProbC, hs, hitProb_zero]
  | succ n ih =>
    simp only [hitProbC]
    rw [hitProb_succ]
    by_cases hsB : s ∈ B
    · rw [ite_eq_left hsB, ite_eq_left hsB]
    · rw [ite_eq_right hsB, ite_eq_right hsB]
      by_cases hsA : s ∉ A
      · rw [ite_eq_left hsA, ite_eq_left hsA]
      · rw [ite_eq_right hsA, ite_eq_right hsA]
        exact Finset.sum_congr rfl (fun t _ => by rw [ih t])

omit [DecidableEq S] in
/-- The next-step checker is exact: it returns `true` exactly when the
one-step probability satisfies the comparison. -/
theorem checkNext_correct (D : DTMC S) (A : Finset S) (s : S) (c : Cmp)
    (q : ℚ) :
    checkNext D.P A s c q = true ↔ c.holds (∑ t ∈ A, D.P s t) q := by
  simp only [checkNext]
  exact cmp_eval_correct _ _ _

/-- The bounded-until checker is exact against the path-sum
semantics. -/
theorem checkBoundedUntil_correct (D : DTMC S) (k : ℕ) (s : S) (c : Cmp)
    (q : ℚ) :
    checkBoundedUntil D.P A B k s c q = true ↔
      c.holds (D.hitProb A B k s) q := by
  simp only [checkBoundedUntil, hitProbC_eq]
  exact cmp_eval_correct _ _ _

/-- Guarded next-step checker: invalid matrices are rejected. -/
def checkNextG (P : S → S → ℚ) (A : Finset S) (s : S) (c : Cmp) (q : ℚ) :
    Bool :=
  stochastic P && checkNext P A s c q

/-- Guarded bounded-until checker: invalid matrices are rejected. -/
def checkBoundedUntilG (P : S → S → ℚ) (A B : Finset S) (k : ℕ) (s : S)
    (c : Cmp) (q : ℚ) : Bool :=
  stochastic P && checkBoundedUntil P A B k s c q

omit [DecidableEq S] in
/-- The guarded next-step checker rejects every invalid matrix. -/
theorem checkNextG_invalid (P : S → S → ℚ) (h : stochastic P = false)
    (A : Finset S) (s : S) (c : Cmp) (q : ℚ) :
    checkNextG P A s c q = false := by
  simp only [checkNextG, h, Bool.false_and]

/-- The guarded bounded-until checker rejects every invalid matrix. -/
theorem checkBoundedUntilG_invalid (P : S → S → ℚ)
    (h : stochastic P = false) (k : ℕ) (s : S) (c : Cmp) (q : ℚ) :
    checkBoundedUntilG P A B k s c q = false := by
  simp only [checkBoundedUntilG, h, Bool.false_and]

omit [DecidableEq S] in
/-- On a genuine chain the guarded next-step checker agrees with the
unguarded one, hence with the semantics. -/
theorem checkNextG_correct (D : DTMC S) (A : Finset S) (s : S) (c : Cmp)
    (q : ℚ) :
    checkNextG D.P A s c q = true ↔ c.holds (∑ t ∈ A, D.P s t) q := by
  simp only [checkNextG, stochastic_complete, Bool.true_and]
  exact checkNext_correct _ _ _ _ _

/-- On a genuine chain the guarded bounded-until checker agrees with
the unguarded one, hence with the path-sum semantics. -/
theorem checkBoundedUntilG_correct (D : DTMC S) (k : ℕ) (s : S) (c : Cmp)
    (q : ℚ) :
    checkBoundedUntilG D.P A B k s c q = true ↔
      c.holds (D.hitProb A B k s) q := by
  simp only [checkBoundedUntilG, stochastic_complete, Bool.true_and]
  exact checkBoundedUntil_correct _ _ _ _ _ _ _

omit [DecidableEq S] in
/-- A matrix passing validation is the transition matrix of a genuine
chain. -/
theorem stochastic_sound (P : S → S → ℚ) (h : stochastic P = true) :
    ∃ D : DTMC S, D.P = P := by
  simp only [stochastic, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hnn, hrs⟩ := h
  exact ⟨⟨P, hnn, hrs⟩, rfl⟩

end Cslib.Probability
