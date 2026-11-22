/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.ValueFunctionMultiplier
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Tests for the resource multiplier as marginal value

On `ℝ` with `u y = -(y - 2) ^ 2` and `g y = y`:

* binding constraint at `b₀ = 1`, `x₀ = 1`, multiplier `2`: the shadow-price bound;
* slack constraint at `b₀ = 3`, `x₀ = 2`, multiplier `0`: the bound with zero marginal value;
* binding case: the value function equals `-(b - 2) ^ 2` near `1`, has derivative `2` there, and
  `hasDerivAt_value_eq_multiplier` applies with all hypotheses discharged.
-/

@[expose] public section

open MathlibExt.Analysis.Convex.ValueFunctionMultiplier

namespace MathlibExtTest.Analysis.Convex.ValueFunctionMultiplier

private theorem m07t03_concave_neg_sq_sub (a : ℝ) :
    ConcaveOn ℝ Set.univ (fun y : ℝ => -(y - a) ^ 2) := by
  refine ⟨convex_univ, fun x _ y _ c d hc hd hcd => ?_⟩
  have hd' : d = 1 - c := by linarith
  subst hd'
  simp only [smul_eq_mul]
  nlinarith [mul_nonneg hc hd, sq_nonneg ((x : ℝ) - y)]

private theorem m07t03_convex_id : ConvexOn ℝ Set.univ (fun y : ℝ => y) :=
  convexOn_id convex_univ

private theorem m07t03_diff_ex (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => -(y - 2) ^ 2) x :=
  ((differentiableAt_id.sub_const 2).pow 2).neg

private theorem m07t03_diff_id (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => y) x :=
  differentiableAt_id

private theorem m07t03_hasDerivAt_ex1 :
    HasDerivAt (fun y : ℝ => -(y - 2) ^ 2) 2 (1 : ℝ) := by
  have h1 : HasDerivAt (fun y : ℝ => y - 2) 1 (1 : ℝ) := (hasDerivAt_id 1).sub_const 2
  have h2 := h1.pow 2
  norm_num at h2
  have h3 := h2.neg
  norm_num at h3
  exact h3

private theorem m07t03_hasDerivAt_ex2 :
    HasDerivAt (fun y : ℝ => -(y - 2) ^ 2) 0 (2 : ℝ) := by
  have h1 : HasDerivAt (fun y : ℝ => y - 2) 1 (2 : ℝ) := (hasDerivAt_id 2).sub_const 2
  have h2 := h1.pow 2
  norm_num at h2
  have h3 := h2.neg
  norm_num at h3
  exact h3

private theorem m07t03_hstat_ex1 :
    fderiv ℝ (fun y : ℝ => -(y - 2) ^ 2) 1
      = (2 : ℝ) • fderiv ℝ (fun y : ℝ => y) 1 := by
  have hF := m07t03_hasDerivAt_ex1.hasFDerivAt
  rw [hF.fderiv, fderiv_fun_id]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

private theorem m07t03_hstat_ex2 :
    fderiv ℝ (fun y : ℝ => -(y - 2) ^ 2) 2
      = (0 : ℝ) • fderiv ℝ (fun y : ℝ => y) 2 := by
  have hF := m07t03_hasDerivAt_ex2.hasFDerivAt
  rw [hF.fderiv, fderiv_fun_id]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

example : ∀ b y : ℝ, y ≤ b → -(y - 2) ^ 2 ≤ -(1 - 2) ^ 2 + 2 * (b - 1) := by
  have h := le_add_multiplier_mul_of_kkt (E := ℝ)
    (u := fun y : ℝ => -(y - 2) ^ 2) (g := fun y : ℝ => y)
    (x₀ := (1 : ℝ)) (b₀ := (1 : ℝ)) (lam := (2 : ℝ))
    (m07t03_concave_neg_sq_sub 2) m07t03_convex_id
    (m07t03_diff_ex 1) (m07t03_diff_id 1)
    (le_refl 1) (by norm_num) (by norm_num) m07t03_hstat_ex1
  simpa using h

example : ∀ b y : ℝ, y ≤ b → -(y - 2) ^ 2 ≤ -(2 - 2) ^ 2 + 0 * (b - 3) := by
  have h := le_add_multiplier_mul_of_kkt (E := ℝ)
    (u := fun y : ℝ => -(y - 2) ^ 2) (g := fun y : ℝ => y)
    (x₀ := (2 : ℝ)) (b₀ := (3 : ℝ)) (lam := (0 : ℝ))
    (m07t03_concave_neg_sq_sub 2) m07t03_convex_id
    (m07t03_diff_ex 2) (m07t03_diff_id 2)
    (by norm_num) (le_refl 0) (by norm_num) m07t03_hstat_ex2
  simpa using h

private theorem m07t03_value_eq (b : ℝ) (hb : b ≤ 2) :
    sSup ((fun y : ℝ => -(y - 2) ^ 2) '' {y | y ≤ b}) = -(b - 2) ^ 2 := by
  have hmem : -(b - 2) ^ 2 ∈ (fun y : ℝ => -(y - 2) ^ 2) '' {y | y ≤ b} :=
    ⟨b, le_refl b, rfl⟩
  have hub : ∀ z ∈ (fun y : ℝ => -(y - 2) ^ 2) '' {y | y ≤ b}, z ≤ -(b - 2) ^ 2 := by
    intro z hz
    obtain ⟨y, hyb, rfl⟩ := hz
    have hyb' : y ≤ b := hyb
    show -(y - 2) ^ 2 ≤ -(b - 2) ^ 2
    have h1 : y - 2 ≤ b - 2 := by linarith
    have h2 : b - 2 ≤ 0 := by linarith
    have h3 : y - 2 ≤ 0 := by linarith
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h1) (add_nonpos h3 h2)]
  have hbdd : BddAbove ((fun y : ℝ => -(y - 2) ^ 2) '' {y | y ≤ b}) := ⟨-(b - 2) ^ 2, hub⟩
  have hne : ((fun y : ℝ => -(y - 2) ^ 2) '' {y | y ≤ b}).Nonempty := ⟨_, hmem⟩
  exact le_antisymm (csSup_le hne hub) (le_csSup hbdd hmem)

private theorem m07t03_value_hasDerivAt :
    HasDerivAt (fun b : ℝ => sSup ((fun y : ℝ => -(y - 2) ^ 2) '' {y | y ≤ b})) 2 1 := by
  have heq : (fun b : ℝ => sSup ((fun y : ℝ => -(y - 2) ^ 2) '' {y | y ≤ b}))
      =ᶠ[nhds (1 : ℝ)] (fun b : ℝ => -(b - 2) ^ 2) := by
    filter_upwards [eventually_lt_nhds (show (1 : ℝ) < 2 by norm_num)] with b hb
    exact m07t03_value_eq b (le_of_lt hb)
  exact m07t03_hasDerivAt_ex1.congr_of_eventuallyEq heq

example : (2 : ℝ) = 2 :=
  hasDerivAt_value_eq_multiplier (E := ℝ)
    (u := fun y : ℝ => -(y - 2) ^ 2) (g := fun y : ℝ => y)
    (x₀ := (1 : ℝ)) (b₀ := (1 : ℝ)) (lam := (2 : ℝ)) (V' := (2 : ℝ))
    (m07t03_concave_neg_sq_sub 2) m07t03_convex_id
    (m07t03_diff_ex 1) (m07t03_diff_id 1)
    (le_refl 1) (by norm_num) (by norm_num) m07t03_hstat_ex1
    ⟨0, by norm_num⟩ m07t03_value_hasDerivAt

end MathlibExtTest.Analysis.Convex.ValueFunctionMultiplier
