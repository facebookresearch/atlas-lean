/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Decision.ValueOfInformation
public import Domains.Economics.Finance.RealOptionValue

/-!
# Expected value of information

For a finite one-shot decision with nonnegative (unnormalized) joint weights
`w ω e` over states and evidence outcomes, the expected value of imperfect
information `evii` is the value of acting after seeing the evidence minus the
best committed value. It is nonnegative (`evii_nonneg`), and it is zero
exactly when some single action is optimal under every evidence outcome in
the support (`evii_eq_zero_iff`). Perfect information is the diagonal special
case (`evii_diagonal_eq_optionValue_sub`), identifying EVPI with the real
option value of `RealOptionValue.optionValue` minus the best commitment; in
particular EVPI is nonnegative (`evpi_nonneg`).

## References

* H. Raiffa and R. Schlaifer, *Applied Statistical Decision Theory*, Harvard
  University (1961), Chapter 4, Section 5.
* S. Russell and P. Norvig, *Artificial Intelligence: A Modern Approach*,
  4th ed., Chapter 16 (value of information).
-/

@[expose] public section

namespace MathlibExt.Economics.Finance.ValueOfInformation

open MathlibExt.Probability.Decision.ValueOfInformation
open MathlibExt.Probability.FiniteProbability
open MathlibExt.Economics.Finance.RealOptionValue

private theorem sup'_mul_nonneg {α : Type*} {actions : Finset α} {hne : actions.Nonempty}
    {c : ℝ} (hc : 0 ≤ c) (f : α → ℝ) :
    actions.sup' hne (fun a => c * f a) = c * actions.sup' hne f := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' f ha) hc
  · obtain ⟨a_star, ha_mem, ha_eq⟩ := Finset.exists_mem_eq_sup' hne f
    have h_le : c * f a_star ≤ actions.sup' hne (fun a => c * f a) :=
      Finset.le_sup' (fun a => c * f a) ha_mem
    rw [ha_eq]
    exact h_le

private theorem diag_post_eq {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {α : Type*} (p : Ω → ℝ) (U : α → Ω → ℝ) (a : α) (e : Ω) :
    (∑ ω, (if e = ω then p ω else 0) * U a ω) = p e * U a e := by
  have h1 : ∀ b ∈ Finset.univ, b ≠ e → ((if e = b then p b else 0) * U a b) = 0 := by
    intro b _ hb_ne
    have h_not : ¬ e = b := fun h_eq => hb_ne (Eq.symm h_eq)
    simp [h_not]
  have h2 : e ∉ Finset.univ → ((if e = e then p e else 0) * U a e) = 0 := by
    intro h_contra
    exact False.elim (h_contra (Finset.mem_univ e))
  have h_eq := Finset.sum_eq_single (s := Finset.univ)
    (f := fun ω => (if e = ω then p ω else 0) * U a ω) e h1 h2
  simp only at h_eq
  rw [h_eq]
  simp

private theorem diag_commit_inner {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {α : Type*} (p : Ω → ℝ) (U : α → Ω → ℝ) (a : α) (ω : Ω) :
    (∑ e : Ω, (if e = ω then p ω else 0) * U a ω) = p ω * U a ω := by
  have h1 : ∀ b ∈ Finset.univ, b ≠ ω → ((if b = ω then p ω else 0) * U a ω) = 0 := by
    intro b _ hb_ne
    simp [hb_ne]
  have h2 : ω ∉ Finset.univ → ((if ω = ω then p ω else 0) * U a ω) = 0 := by
    intro h_contra
    exact False.elim (h_contra (Finset.mem_univ ω))
  have h_eq := Finset.sum_eq_single (s := Finset.univ)
    (f := fun e => (if e = ω then p ω else 0) * U a ω) ω h1 h2
  simp only at h_eq
  rw [h_eq]
  simp

/-- With nonnegative state weights `p` and diagonal evidence weights, the gain from information is
the real option value minus the best commitment. -/
theorem evii_diagonal_eq_optionValue_sub {α Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {actions : Finset α} {hne : actions.Nonempty}
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (U : α → Ω → ℝ) :
    evii actions hne (fun ω e => if e = ω then p ω else 0) U =
      optionValue actions hne p U -
        actions.sup' hne (fun a => expectation p (U a)) := by
  have h_commit : ∀ a,
    commitValue (fun ω e => if e = ω then p ω else 0) U a = expectation p (U a) := by
    intro a
    simp only [commitValue, expectation]
    apply Finset.sum_congr rfl
    intro ω _
    exact diag_commit_inner p U a ω
  have h_informed : informedValue actions hne (fun ω e => if e = ω then p ω else 0) U =
    optionValue actions hne p U := by
    simp only [informedValue, optionValue, expectation]
    apply Finset.sum_congr rfl
    intro e _
    have h_sup_congr :
      actions.sup' hne (fun a => ∑ ω, (if e = ω then p ω else 0) * U a ω) =
        actions.sup' hne (fun a => p e * U a e) := by
      apply Finset.sup'_congr hne rfl
      intro a _
      exact diag_post_eq p U a e
    rw [h_sup_congr]
    rw [sup'_mul_nonneg (hp e) (fun a => U a e)]
  simp only [evii]
  rw [h_informed]
  congr 1
  apply Finset.sup'_congr hne rfl
  intro a _
  exact h_commit a

/-- **Expected value of perfect information is nonnegative** (Raiffa and
Schlaifer, Chapter 4, Section 5) for nonnegative state weights `p`, as the diagonal special case. -/
theorem evpi_nonneg {α Ω : Type*} [Fintype Ω]
    {actions : Finset α} {hne : actions.Nonempty}
    {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {U : α → Ω → ℝ} :
    0 ≤ optionValue actions hne p U -
      actions.sup' hne (fun a => expectation p (U a)) := by
  apply sub_nonneg.mpr
  exact maxCommitment_le_optionValue hp

end MathlibExt.Economics.Finance.ValueOfInformation
