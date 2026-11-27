/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Externalities.PublicGood
public import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv

/-!
# Demand for a public-good total at a per-unit price

At unit price `p`, the relevant objective for the total `G` is `v G - p * G`. At price
`c / n` this is per-capita surplus, whereas at price `c` it measures the change in a
contributor's own payoff, holding the others' contributions fixed. All shape and derivative
assumptions concern nonnegative totals only. In particular `d 0` is a right derivative.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace MathlibExt.Economics.PublicGood

/-- A common public-good benefit `v` is increasing (in the weak sense) and strictly concave
on feasible totals `G ≥ 0`. Its marginal benefit `d` is its derivative on that half-line,
one-sided at zero, and tends to zero as `G` tends to infinity. -/
structure CommonBenefit (v d : ℝ → ℝ) : Prop where
  /-- Increasing a feasible total cannot reduce benefit. -/
  increasing : MonotoneOn v (Ici 0)
  /-- A convex mixture of distinct feasible totals with both weights positive gives strictly
  greater benefit than the same mixture of the two benefits. -/
  concave : StrictConcaveOn ℝ (Ici 0) v
  /-- `d` gives the derivative within the feasible half-line, including its endpoint. -/
  marginal : ∀ G ∈ Ici 0, HasDerivWithinAt v (d G) (Ici 0) G
  /-- The marginal benefit of further provision vanishes at infinity. -/
  vanishing : Tendsto d atTop (𝓝 0)

variable {v d : ℝ → ℝ}

/-- For an increasing, differentiable and strictly concave common benefit on nonnegative
totals with vanishing marginal benefit, its marginal benefit strictly decreases there,
including comparisons with the right derivative at zero. -/
theorem CommonBenefit.strictAntiOn_marginal (h : CommonBenefit v d) : StrictAntiOn d (Ici 0) := by
  have hd := h.concave.strictAntiOn_derivWithin
    (fun x hx => (h.marginal x hx).differentiableWithinAt)
  intro x hx y hy hxy
  simpa only [(h.marginal x hx).derivWithin (uniqueDiffOn_Ici _ _ hx),
    (h.marginal y hy).derivWithin (uniqueDiffOn_Ici _ _ hy)] using hd hx hy hxy

/-- If an increasing, strictly concave common benefit is differentiable on nonnegative totals
and its marginal benefit tends to zero, then every positive unit price `p` below its right
derivative at zero is attained by marginal benefit at a positive total `G`. At every other
feasible total, benefit net of `p` times provision is strictly smaller. -/
theorem CommonBenefit.exists_peak (h : CommonBenefit v d) {p : ℝ} (hp : 0 < p) (h0 : p < d 0) :
    ∃ G : ℝ, 0 < G ∧ d G = p ∧ ∀ x ∈ Ici (0 : ℝ), x ≠ G → v x - p * x < v G - p * G := by
  obtain ⟨b, hb, hbp⟩ :=
    ((eventually_ge_atTop (0 : ℝ)).and (h.vanishing.eventually_lt_const hp)).exists
  obtain ⟨G, hG, hpG⟩ := exists_hasDerivWithinAt_eq_of_lt_of_gt hb
    (fun x hx => (h.marginal x hx.1).mono Icc_subset_Ici_self) h0 hbp
  refine ⟨G, hG.1, hpG, ?_⟩
  intro x hx hne
  have hd : HasDerivWithinAt v p (Ici 0) G := hpG ▸ h.marginal G hG.1.le
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs := h.concave.lt_slope_of_hasDerivWithinAt hx hG.1.le hlt hd
    rw [slope_def_field, lt_div_iff₀ (sub_pos.mpr hlt)] at hs
    linarith
  · have hs := h.concave.slope_lt_of_hasDerivWithinAt hG.1.le hx hgt hd
    rw [slope_def_field, div_lt_iff₀ (sub_pos.mpr hgt)] at hs
    linarith

/-- For `n > 0` consumers with a common increasing, differentiable and strictly concave benefit
on nonnegative totals, suppose marginal benefit vanishes at infinity, cost `c` is positive
and `c / n` is below the right derivative at zero. There is a positive total `E` with marginal
benefit `c / n`. Among nonnegative totals, `E` alone solves the Samuelson equation and `E`
alone maximizes total surplus at production cost `c` per unit. -/
theorem CommonBenefit.exists_efficientTotal (h : CommonBenefit v d) {n : ℕ} (hn : 0 < n)
    {c : ℝ} (hc : 0 < c) (h0 : c / n < d 0) :
    ∃ E : ℝ, 0 < E ∧ d E = c / n ∧
      (∀ x ∈ Ici (0 : ℝ), (n : ℝ) * d x = c ↔ x = E) ∧
      ∀ x ∈ Ici (0 : ℝ), IsMaxOn (surplus (fun _ : Fin n => v) (c * ·)) (Ici 0) x ↔ x = E := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨E, hE, hdE, hpeak⟩ := h.exists_peak (div_pos hc hn') h0
  have root (x : ℝ) (hx : 0 ≤ x) : (n : ℝ) * d x = c ↔ x = E := by
    rw [mul_comm, ← eq_div_iff hn'.ne', ← hdE]
    exact ⟨h.strictAntiOn_marginal.injOn hx hE.le, congrArg d⟩
  let W := surplus (fun _ : Fin n => v) (c * ·)
  have scale (x : ℝ) : W x = n * (v x - (c / n) * x) := by
    simp only [W, surplus, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have below {x : ℝ} (hx : 0 ≤ x) (hne : x ≠ E) : W x < W E := by
    rw [scale, scale]
    exact mul_lt_mul_of_pos_left (hpeak x hx hne) hn'
  refine ⟨E, hE, hdE, root, ?_⟩
  intro x hx
  change IsMaxOn W (Ici 0) x ↔ x = E
  constructor
  · intro hm
    have hx' : 0 < x := lt_of_le_of_ne hx fun he =>
      (not_lt_of_ge (hm hE.le)) (below hx (he ▸ hE.ne))
    have sam := sum_marginalBenefit_eq_marginalCost_of_isLocalMaxOn hx' hm.isLocalMaxOn
      (fun _ => (h.marginal x hx).hasDerivAt (Ici_mem_nhds hx'))
      (by simpa using (hasDerivAt_id' x).const_mul c : HasDerivAt (c * ·) c x)
    exact (root x hx).mp (by simpa using sam)
  · rintro rfl y hy
    rcases eq_or_ne y x with rfl | hne
    · exact le_rfl
    · exact (below hy hne).le

end MathlibExt.Economics.PublicGood
