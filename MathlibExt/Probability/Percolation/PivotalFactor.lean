/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.CorrelationInequalities.Russo

/-!
# Russo's formula with the pivotal factor `(ω_e - p) / (p(1 - p))`

For an increasing event `A` on a finite set `E`, the probability that `e` is pivotal equals
`(p(1 - p))⁻¹ 𝔼_p[1_A (ω_e - p)]`. Summing over `e` gives Russo's formula in the form
`d/dp ℙ_p(A) = (p(1 - p))⁻¹ ∑_e 𝔼_p[1_A (ω_e - p)]`, the form used in the Duminil-Copin–Tassion
argument for the Ising model and in Aizenman–Barsky type differential inequalities.

## Main definitions

* `StatMech.Sharpness.openInd`: the indicator `ω_e ∈ {0, 1}` that the edge `e` is open.

## Main results

* `StatMech.Sharpness.pivotalProb_eq`: `ℙ_p(e pivotal for A) = (p(1 - p))⁻¹ 𝔼_p[1_A (ω_e - p)]`.
* `StatMech.Sharpness.hasDerivAt_prob_eq_pivotalFactor`,
  `StatMech.Sharpness.deriv_prob_eq_pivotalFactor`: Russo's formula in this form.
* `StatMech.Sharpness.deriv_prob_nonneg`: `p ↦ ℙ_p(A)` is nondecreasing for increasing `A`.

## References

* L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981),
  229–237.
-/

@[expose] public section

namespace StatMech

namespace Sharpness

open ConfigSpace Function Finset StatMech

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The indicator `ω_e ∈ {0, 1}` (as a real number) that the edge `e` is open in `ω`. -/
noncomputable def openInd (ω : ConfigSpace E) (e : E) : ℝ := if ω e then 1 else 0

omit [Fintype E] [DecidableEq E] in
lemma sign_eq_pivotalFactor_mul_edgeWeight (ω : ConfigSpace E) (e : E) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    (if ω e then (1 : ℝ) else -1)
      = ((openInd ω e - p) / (p * (1 - p))) * edgeWeight p ω e := by
  unfold openInd edgeWeight
  have hp0' : p ≠ 0 := ne_of_gt hp0
  have hp1' : (1 : ℝ) - p ≠ 0 := by linarith
  by_cases h : ω e = true
  · simp only [h, ite_true]; field_simp
  · simp only [h, ite_false, Bool.false_eq_true]; field_simp; ring

lemma weightOff_mul_sign_eq_pivotalFactor (ω : ConfigSpace E) (e : E) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    weightOff p e ω * (if ω e then (1 : ℝ) else -1)
      = ((openInd ω e - p) / (p * (1 - p))) * configWeight p ω := by
  rw [sign_eq_pivotalFactor_mul_edgeWeight ω e hp0 hp1, configWeight_eq p e ω]
  ring

theorem pivotalProb_eq (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    pivotalProb p A e
      = (1 / (p * (1 - p))) *
          ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
            ((openInd ω e - p) * configWeight p ω) := by
  rw [← russo_per_edge p A hA e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [weightOff_mul_sign_eq_pivotalFactor ω e hp0 hp1]; ring

/-- **Russo's formula** in pivotal-factor form: for increasing `A` and `0 < p < 1`,
`d/dp ℙ_p(A) = (p(1 - p))⁻¹ ∑_e 𝔼_p[1_A (ω_e - p)]`. -/
theorem hasDerivAt_prob_eq_pivotalFactor (A : Set (ConfigSpace E))
    (hA : IsIncreasing A) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun p => prob p A)
      ((1 / (p * (1 - p))) *
        ∑ e, ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
          ((openInd ω e - p) * configWeight p ω)) p := by
  have h := hasDerivAt_prob_eq_sum_pivotalProb A hA p
  rw [show (1 / (p * (1 - p))) *
        ∑ e, ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
          ((openInd ω e - p) * configWeight p ω)
      = ∑ e, pivotalProb p A e from ?_]
  · exact h
  · rw [Finset.mul_sum]
    refine (Finset.sum_congr rfl (fun e _ => ?_)).symm
    exact pivotalProb_eq A hA e hp0 hp1

theorem deriv_prob_eq_pivotalFactor (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    deriv (fun p => prob p A) p
      = (1 / (p * (1 - p))) *
          ∑ e, ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
            ((openInd ω e - p) * configWeight p ω) :=
  (hasDerivAt_prob_eq_pivotalFactor A hA hp0 hp1).deriv

theorem deriv_prob_nonneg (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ deriv (fun p => prob p A) p := by
  rw [deriv_prob_eq_sum_pivotalProb A hA p]
  exact Finset.sum_nonneg (fun e _ => pivotalProb_nonneg hp0 hp1 A e)

end Sharpness

end StatMech
