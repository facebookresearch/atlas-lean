/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.MeanValue

public import MathlibExt.Probability.Percolation.SharpThreshold

/-!
# Sharp thresholds from a KKL-type influence inequality

Conditional sharp-threshold bounds: if the total influence of an increasing event `A` satisfies a
Kahn–Kalai–Linial / Talagrand-type inequality `∑_e I_e^p(A) ≥ C · Var_p(1_A) · L(p)` on
`(1/2, q)`, the variance stays above `v₀`, and `L(p) ≥ L`, then `ℙ_q(A) ≥ 1/2 + C v₀ L (q - 1/2)`.
This is the step that turns the influence inequality into a sharp threshold in Kesten-type
proofs of `p_c = 1/2` for bond percolation on `ℤ²`. The influence inequality is a hypothesis
here; neither it nor `p_c(ℤ²) = 1/2` is proved in this file.

## Main results

* `StatMech.TwoDim.ktr_totalInfluence_lb_of_window`: if `ℙ_p(A)` grows by more than `Δ` over
  `[1/2, q]`, some `p` in between has total influence at least `Δ / (q - 1/2)`.
* `StatMech.TwoDim.ktr_sharpThreshold_via_kkl`,
  `StatMech.TwoDim.ktr_sharpThreshold_window_via_kkl`: the sharp-threshold bound and window bound
  from a KKL-type hypothesis.

## References

* J. Kahn, G. Kalai, N. Linial, *The influence of variables on Boolean functions*, FOCS 1988.
* H. Kesten, *The critical probability of bond percolation on the square lattice equals 1/2*,
  Comm. Math. Phys. 74 (1980), 41–59.
* B. Bollobás, O. Riordan, *A short proof of the Harris–Kesten theorem*, Bull. London Math.
  Soc. 38 (2006), 470–484.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace StatMech

namespace TwoDim

open ConfigSpace Function Finset StatMech StatMech.Sharpness StatMech.BeffaraDC

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem ktr_variance_lb_of_crossing {x δ : ℝ}
    (hl : δ ≤ x) (hr : x ≤ 1 - δ) :
    δ * (1 - δ) ≤ x * (1 - x) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)]

theorem ktr_prob_variance_lb (A : Set (ConfigSpace E)) {p δ : ℝ}
    (hl : δ ≤ prob p A) (hr : prob p A ≤ 1 - δ) :
    δ * (1 - δ) ≤ prob p A * (1 - prob p A) :=
  ktr_variance_lb_of_crossing hl hr

theorem ktr_totalInfluence_eq_card_mul_of_symmetric (A : Set (ConfigSpace E)) {p ι : ℝ}
    (hsym : ∀ e : E, influence p A e = ι) :
    ∑ e, influence p A e = (Fintype.card E : ℝ) * ι := by
  rw [Finset.sum_congr rfl (fun e _ => hsym e)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem ktr_totalInfluence_lb_of_window (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {q Δ : ℝ} (hq : (1 : ℝ) / 2 < q) (hΔ : prob (1 / 2) A + Δ < prob q A) :
    ∃ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), Δ / (q - 1 / 2) ≤ ∑ e, influence p A e := by
  by_contra hcon
  push Not at hcon
  have hpos : (0 : ℝ) < q - 1 / 2 := by linarith
  set M : ℝ := Δ / (q - 1 / 2) with hM
  have hge : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      deriv (fun p => prob p A) p ≤ M := by
    intro p hp
    rw [deriv_eq_total_influence p A hA]
    exact le_of_lt (hcon p hp)
  have hdiff : Differentiable ℝ (fun p => prob p A) := sth_prob_differentiable A
  have hub : prob q A - prob (1 / 2) A ≤ M * (q - 1 / 2) :=
    (convex_Icc (1 / 2 : ℝ) q).image_sub_le_mul_sub_of_deriv_le
      hdiff.continuous.continuousOn hdiff.differentiableOn hge
      (1 / 2) (Set.left_mem_Icc.mpr hq.le) q (Set.right_mem_Icc.mpr hq.le) hq.le
  rw [hM, div_mul_cancel₀ Δ (ne_of_gt hpos)] at hub
  linarith

theorem ktr_totalInfluence_lb_of_kkl (A : Set (ConfigSpace E)) {p C v₀ L L' : ℝ}
    (hC : 0 < C) (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hkkl : C * (prob p A * (1 - prob p A)) * L' ≤ ∑ e, influence p A e)
    (hvar : v₀ ≤ prob p A * (1 - prob p A))
    (hLL' : L ≤ L') :
    C * v₀ * L ≤ ∑ e, influence p A e := by
  refine le_trans ?_ hkkl
  have hVarnn : 0 ≤ prob p A * (1 - prob p A) := le_trans hv0 hvar
  have h1 : C * v₀ * L ≤ C * (prob p A * (1 - prob p A)) * L := by
    apply mul_le_mul_of_nonneg_right _ hL
    exact mul_le_mul_of_nonneg_left hvar hC.le
  have h2 : C * (prob p A * (1 - prob p A)) * L ≤ C * (prob p A * (1 - prob p A)) * L' := by
    apply mul_le_mul_of_nonneg_left hLL'
    exact mul_nonneg hC.le hVarnn
  linarith

theorem ktr_hinfl_of_kkl (A : Set (ConfigSpace E)) {q C v₀ L : ℝ}
    (hC : 0 < C) (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (L' : ℝ → ℝ)
    (hkkl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      C * (prob p A * (1 - prob p A)) * L' p ≤ ∑ e, influence p A e)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ prob p A * (1 - prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ L' p) :
    ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), C * v₀ * L ≤ ∑ e, influence p A e := by
  intro p hp
  exact ktr_totalInfluence_lb_of_kkl A hC hv0 hL (hkkl p hp) (hvar p hp) (hLL' p hp)

/-- Sharp threshold from a KKL-type inequality: if `ℙ_{1/2}(A) = 1/2` and for all `p ∈ (1/2, q)`
`∑_e I_e^p(A) ≥ C · ℙ_p(A)(1 - ℙ_p(A)) · L'(p)`, `ℙ_p(A)(1 - ℙ_p(A)) ≥ v₀` and `L'(p) ≥ L`, then
`ℙ_q(A) ≥ 1/2 + C v₀ L (q - 1/2)`. The KKL-type inequality is a hypothesis. -/
theorem ktr_sharpThreshold_via_kkl (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {q C v₀ L : ℝ} (hq : (1 : ℝ) / 2 ≤ q)
    (hC : 0 < C) (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (hhalf : prob (1 / 2) A = 1 / 2)
    (L' : ℝ → ℝ)
    (hkkl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      C * (prob p A * (1 - prob p A)) * L' p ≤ ∑ e, influence p A e)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ prob p A * (1 - prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ L' p) :
    1 / 2 + (C * v₀ * L) * (q - 1 / 2) ≤ prob q A :=
  sth_sharpThreshold A hA hq hhalf
    (ktr_hinfl_of_kkl A hC hv0 hL L' hkkl hvar hLL')

theorem ktr_sharpThreshold_window_via_kkl (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {q C v₀ L ε : ℝ} (hq : (1 : ℝ) / 2 ≤ q)
    (hM : 0 < C * v₀ * L)
    (hhalf : prob (1 / 2) A = 1 / 2)
    (hC : 0 < C) (hv0 : 0 ≤ v₀) (hL : 0 ≤ L)
    (L' : ℝ → ℝ)
    (hkkl : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q),
      C * (prob p A * (1 - prob p A)) * L' p ≤ ∑ e, influence p A e)
    (hvar : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), v₀ ≤ prob p A * (1 - prob p A))
    (hLL' : ∀ p ∈ interior (Set.Icc (1 / 2 : ℝ) q), L ≤ L' p)
    (hnotyet : prob q A ≤ 1 - ε) :
    q - 1 / 2 ≤ (1 / 2 - ε) / (C * v₀ * L) :=
  sth_sharpThreshold_window A hA hM hq hhalf
    (ktr_hinfl_of_kkl A hC hv0 hL L' hkkl hvar hLL') hnotyet

end TwoDim

end StatMech
