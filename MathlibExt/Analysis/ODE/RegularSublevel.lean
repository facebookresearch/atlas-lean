/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.Analysis.ODE.Nagumo
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Regular sublevel invariance

A nonzero derivative at a boundary point supplies a strictly inward direction.
Perturbing any weakly inward vector in that direction gives feasible points at
positive times, proving membership in the positive tangent cone. Nagumo's
theorem then gives invariance along existing solutions in finite dimensions.

Regularity is essential: the sublevel of x³ can be left by x'=1 even though
its Lie derivative vanishes on the zero set. For intersections, apply the rule
to each constraint with its own boundary hypotheses.

Source: Ghorbal–Sogokon–Platzer, *A Hierarchy of Proof Rules for Checking
Positive Invariance of Algebraic and Semi-Algebraic Sets*, §5.3, p.14,
https://logic.kastel.kit.edu/pub/alginv-bench-long.pdf. Their nonnegative
superlevel convention is converted here to nonpositive sublevels.
-/

@[expose] public section

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem eventually_neg_on_ray {h : E → ℝ} {L : E →L[ℝ] ℝ} {x u : E}
    (hd : HasFDerivAt h L x) (hx : h x = 0) (hu : L u < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), h (x + t • u) < 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add x
  have hc : HasDerivAt (fun t : ℝ => h (x + t • u)) (L u) 0 := by
    simpa using! hd.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hs := hc.tendsto_slope_zero_right.eventually (gt_mem_nhds hu)
  filter_upwards [hs, self_mem_nhdsWithin] with t ht htpos
  have ht' : t⁻¹ * h (x + t • u) < 0 := by simpa [hx, smul_eq_mul] using ht
  by_contra hn
  exact (not_lt_of_ge (mul_nonneg (inv_nonneg.mpr (le_of_lt htpos))
    (not_lt.mp hn))) ht'

/-- At a regular zero of a differentiable scalar function, every vector with
nonpositive derivative belongs to the positive tangent cone of its sublevel.
Only differentiability at this point and a nonzero derivative are required. -/
theorem HasFDerivAt.mem_posTangentConeAt_sublevel {h : E → ℝ} {L : E →L[ℝ] ℝ} {x v : E}
    (hd : HasFDerivAt h L x) (hx : h x = 0) (hL : L ≠ 0) (hv : L v ≤ 0) :
    v ∈ posTangentConeAt {y | h y ≤ 0} x := by
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hL
  have hz' : L z ≠ 0 := by simpa using hz
  have hw : ∃ w, L w < 0 := by
    rcases lt_or_gt_of_ne hz' with hn | hp
    · exact ⟨z, hn⟩
    · exact ⟨-z, by simpa using neg_neg_of_pos hp⟩
  obtain ⟨w, hw⟩ := hw
  rw [Nagumo.mem_posTangentConeAt_iff]
  intro ε hε δ hδ
  let η := ε / (‖w‖ + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hηsum : η * (‖w‖ + 1) = ε := div_mul_cancel₀ _ (by positivity)
  have hηbound : η * ‖w‖ ≤ ε := by nlinarith
  have hu : L (v + η • w) < 0 := by
    simp only [map_add, map_smul, smul_eq_mul]
    exact add_neg_of_nonpos_of_neg hv (mul_neg_of_pos_of_neg hη hw)
  obtain ⟨t, htin, ht⟩ := ((eventually_neg_on_ray hd hx hu).and (Ioo_mem_nhdsGT hδ)).exists
  refine ⟨t, ht.1, ht.2, x + t • (v + η • w), htin.le, ?_⟩
  have heq : x + t • (v + η • w) - x - t • v = t • (η • w) := by module
  rw [heq, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ht.1, abs_of_pos hη]
  nlinarith

/-- In a finite-dimensional real normed space, let `h` be everywhere
differentiable and let the vector field `f` be locally Lipschitz. Suppose
`fderiv ℝ h x` is nonzero and `fderiv ℝ h x (f x) ≤ 0` at every zero of `h`.
A supplied solution with `HasDerivWithinAt u (f (u t)) (Icc a b) t` throughout
`Icc a b`, initially satisfying `h (u a) ≤ 0`, stays in `{x | h x ≤ 0}`
on that closed interval. -/
theorem Nagumo.mapsTo_sublevel_of_fderiv_nonpos [FiniteDimensional ℝ E]
    {f : E → E} (hf : LocallyLipschitz f) {h : E → ℝ} (hh : Differentiable ℝ h)
    (hreg : ∀ x, h x = 0 → fderiv ℝ h x ≠ 0)
    (hin : ∀ x, h x = 0 → fderiv ℝ h x (f x) ≤ 0)
    {a b : ℝ} {u : ℝ → E}
    (hu : ∀ t ∈ Icc a b, HasDerivWithinAt u (f (u t)) (Icc a b) t)
    (hu₀ : h (u a) ≤ 0) : MapsTo u (Icc a b) {x | h x ≤ 0} := by
  apply Nagumo.mapsTo_of_mem_posTangentConeAt hf
    (isClosed_le hh.continuous continuous_const) _ hu hu₀
  intro x hx
  change h x ≤ 0 at hx
  rcases hx.eq_or_lt with hx | hx
  · exact HasFDerivAt.mem_posTangentConeAt_sublevel (hh x).hasFDerivAt hx (hreg x hx) (hin x hx)
  · have hn : {y | h y < 0} ∈ 𝓝 x :=
      (isOpen_lt hh.continuous continuous_const).mem_nhds hx
    have hn' : {y | h y ≤ 0} ∈ 𝓝 x :=
      Filter.mem_of_superset hn (by
        intro y hy
        change h y ≤ 0
        exact (show h y < 0 from hy).le)
    rw [posTangentConeAt, tangentConeAt_of_mem_nhds hn']
    exact mem_univ _
