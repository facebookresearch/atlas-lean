/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.KarushKuhnTucker
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The resource multiplier is the marginal value

For the resource problem "maximize `u y` subject to `g y ≤ b`" with `u` concave and `g` convex,
a feasible point `x₀` at level `b₀` with a KKT multiplier `lam ≥ 0` (complementary slackness and
stationarity `fderiv ℝ u x₀ = lam • fderiv ℝ g x₀`, the conditions of
`MathlibExt.Analysis.Convex.KarushKuhnTucker.karush_kuhn_tucker_inequality` for `-u` and
`g - b₀`) gives:

* `le_add_multiplier_mul_of_kkt`: global sensitivity. Every `y` feasible at any level `b`
  satisfies `u y ≤ u x₀ + lam * (b - b₀)`. Hence `V b ≤ V b₀ + lam * (b - b₀)` for the value
  `V b = sSup (u '' {y | g y ≤ b})` at every level `b` whose feasible set is nonempty (on an
  empty feasible set `sSup ∅ = 0` is a junk value and the inequality can fail). No
  differentiability of the value function or of an optimizer path is assumed.
* `hasDerivAt_value_eq_multiplier`: local sensitivity. Under Slater's condition, if the value
  function `b ↦ sSup (u '' {y | g y ≤ b})` is differentiable at `b₀`, its derivative is `lam`.

A positive multiplier `lam > 0` forces the constraint to bind (`g x₀ = b₀`) by complementary
slackness; an active constraint may still have multiplier `0`.

## References

* S. Boyd and L. Vandenberghe, *Convex Optimization* (2004), §5.6.2 (global sensitivity,
  inequality (5.57)) and §5.6.3 (local sensitivity), stated there in minimization form.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.ValueFunctionMultiplier

/--
Shadow-price bound for a concave resource problem. Maximize `u y` subject to the resource
constraint `g y ≤ b`. Let `u` be concave and `g` convex on the whole space, both differentiable
at `x₀`, with `x₀` feasible at level `b₀` and a multiplier `lam ≥ 0` satisfying complementary
slackness `lam * (g x₀ - b₀) = 0` and stationarity `fderiv ℝ u x₀ = lam • fderiv ℝ g x₀`
(the KKT conditions of `karush_kuhn_tucker_inequality` for `-u` and `g - b₀`). Then every
`y` feasible at any level `b` satisfies `u y ≤ u x₀ + lam * (b - b₀)`. So `lam` is a
supergradient of the value function at `b₀` on the levels whose feasible set is nonempty, with no
differentiability of the value assumed.
-/
theorem le_add_multiplier_mul_of_kkt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u g : E → ℝ} {x₀ : E} {b₀ lam : ℝ}
    (hu : ConcaveOn ℝ Set.univ u) (hg : ConvexOn ℝ Set.univ g)
    (hu_diff : DifferentiableAt ℝ u x₀) (hg_diff : DifferentiableAt ℝ g x₀)
    (hfeas : g x₀ ≤ b₀) (hlam : 0 ≤ lam) (hcs : lam * (g x₀ - b₀) = 0)
    (hstat : fderiv ℝ u x₀ = lam • fderiv ℝ g x₀) :
    ∀ b y, g y ≤ b → u y ≤ u x₀ + lam * (b - b₀) := by
  intro b y hyb
  have hgle := hg.add_fderiv_sub_le (Set.mem_univ x₀) (Set.mem_univ y) hg_diff
  have huneg : ConvexOn ℝ Set.univ (-u) := hu.neg
  have hu_diff_neg : DifferentiableAt ℝ (-u) x₀ := hu_diff.neg
  have hule := huneg.add_fderiv_sub_le (Set.mem_univ x₀) (Set.mem_univ y) hu_diff_neg
  have hfneg : fderiv ℝ (-u) x₀ = -fderiv ℝ u x₀ := hu_diff.hasFDerivAt.neg.fderiv
  rw [hfneg] at hule
  simp only [Pi.neg_apply, neg_apply] at hule
  have hu_ineq : u y ≤ u x₀ + fderiv ℝ u x₀ (y - x₀) := by linarith
  have hstatapp : fderiv ℝ u x₀ (y - x₀) = lam * fderiv ℝ g x₀ (y - x₀) := by
    rw [hstat, smul_apply, smul_eq_mul]
  have hg_ineq : fderiv ℝ g x₀ (y - x₀) ≤ g y - g x₀ := by linarith
  have hmul : lam * fderiv ℝ g x₀ (y - x₀) ≤ lam * (g y - g x₀) :=
    mul_le_mul_of_nonneg_left hg_ineq hlam
  have hgb : lam * g y ≤ lam * b := mul_le_mul_of_nonneg_left hyb hlam
  have hlam_feas : lam * g x₀ ≤ lam * b₀ := mul_le_mul_of_nonneg_left hfeas hlam
  have e1 : lam * (g y - g x₀) = lam * g y - lam * b₀ := by linear_combination -hcs
  have e2 : lam * (b - b₀) = lam * b - lam * b₀ := by ring
  rw [hstatapp] at hu_ineq
  linarith

/--
The multiplier is the marginal value of the resource. Under the hypotheses of
`le_add_multiplier_mul_of_kkt` and Slater's condition `∃ y, g y < b₀`, if the value function
`V b = sSup (u '' {y | g y ≤ b})` has derivative `V'` at `b₀`, then `V' = lam`.
-/
theorem hasDerivAt_value_eq_multiplier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u g : E → ℝ} {x₀ : E} {b₀ lam V' : ℝ}
    (hu : ConcaveOn ℝ Set.univ u) (hg : ConvexOn ℝ Set.univ g)
    (hu_diff : DifferentiableAt ℝ u x₀) (hg_diff : DifferentiableAt ℝ g x₀)
    (hfeas : g x₀ ≤ b₀) (hlam : 0 ≤ lam) (hcs : lam * (g x₀ - b₀) = 0)
    (hstat : fderiv ℝ u x₀ = lam • fderiv ℝ g x₀) (hslater : ∃ y, g y < b₀)
    (hV : HasDerivAt (fun b => sSup (u '' {y | g y ≤ b})) V' b₀) :
    V' = lam := by
  have hshadow := le_add_multiplier_mul_of_kkt hu hg hu_diff hg_diff hfeas hlam hcs hstat
  have hmem0 : u x₀ ∈ u '' {y | g y ≤ b₀} := ⟨x₀, hfeas, rfl⟩
  have hub0 : ∀ z ∈ u '' {y | g y ≤ b₀}, z ≤ u x₀ := by
    intro z hz
    obtain ⟨y, hyb, rfl⟩ := hz
    have h := hshadow b₀ y hyb
    simpa using h
  have hbdd0 : BddAbove (u '' {y | g y ≤ b₀}) := ⟨u x₀, hub0⟩
  have hne0 : (u '' {y | g y ≤ b₀}).Nonempty := ⟨u x₀, hmem0⟩
  have hVb0 : sSup (u '' {y | g y ≤ b₀}) = u x₀ :=
    le_antisymm (csSup_le hne0 hub0) (le_csSup hbdd0 hmem0)
  obtain ⟨ys, hys⟩ := hslater
  have hmax : IsLocalMax (fun b => sSup (u '' {y | g y ≤ b}) - lam * b) b₀ := by
    change ∀ᶠ b in nhds b₀, sSup (u '' {y | g y ≤ b}) - lam * b
      ≤ sSup (u '' {y | g y ≤ b₀}) - lam * b₀
    filter_upwards [eventually_gt_nhds hys] with b hb
    have hne : (u '' {y | g y ≤ b}).Nonempty :=
      Set.Nonempty.image u ⟨ys, le_of_lt hb⟩
    have hub : ∀ z ∈ u '' {y | g y ≤ b}, z ≤ u x₀ + lam * (b - b₀) := by
      intro z hz
      obtain ⟨y, hyb, rfl⟩ := hz
      exact hshadow b y hyb
    have hle : sSup (u '' {y | g y ≤ b}) ≤ u x₀ + lam * (b - b₀) := csSup_le hne hub
    have e : lam * (b - b₀) = lam * b - lam * b₀ := by ring
    rw [hVb0]
    linarith
  have hlin : HasDerivAt (fun b : ℝ => lam * b) lam b₀ := by
    simpa using (hasDerivAt_id b₀).const_mul lam
  have hW : HasDerivAt (fun b => sSup (u '' {y | g y ≤ b}) - lam * b) (V' - lam) b₀ :=
    hV.sub hlin
  have hzero := hmax.hasDerivAt_eq_zero hW
  linarith

end MathlibExt.Analysis.Convex.ValueFunctionMultiplier
