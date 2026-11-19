/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.ODE.FiniteElement1D
public import MathlibExt.Analysis.ODE.SturmLiouvilleExistence
public import MathlibExt.Analysis.ODE.SturmLiouvilleUniqueness
public import PhyslibExt.Units.EngineeringQuantities

/-!
# Constant-rigidity fixed-fixed bar and shaft

## i. Overview

A prismatic member of length `L > 0` and constant positive rigidity `k` carries a distributed
load `f` and is fixed at both ends. The model is the scalar Dirichlet problem
`-(k * u'') = f` on `[0, L]` with `u 0 = 0` and `u L = 0` (`IsFixedFixedSolution`).

* Bar: `k = EA` (axial rigidity, a force), `f` the distributed axial load (force per length),
  `u` the axial displacement (a length); small-strain linear elastic bar.
* Circular shaft: `k = GJ` (torsional rigidity, force times length squared per radian), `f` the
  distributed torque (torque per length), `u` the twist angle (radians, dimensionless);
  prismatic circular-shaft Saint-Venant torsion.

The change of variables `x = L * ξ` turns the problem into the unit problem `-v'' = g` on
`[0, 1]` with `v 0 = v 1 = 0` and `g ξ = L ^ 2 / k * f (L * ξ)`, which is the existing
Sturm-Liouville Dirichlet problem with zero potential. Existence and uniqueness are transported
from `sturm_liouville_existence` and `sturm_liouville_uniqueness`. Under a uniform load `q` the
solution is `q * x * (L - x) / (2 * EA)`; the twist under a uniform torque `t` is the same
formula with `GJ` and `t`, and the dimension identities record that the first is a length and
the second a plane angle. The scaled uniform-load bar is a classical solution of the unit
Dirichlet problem treated by the one-dimensional finite element module.

Model inputs: the constitutive laws above, constant rigidity, zero end values at both ends.
Boundaries: a traction (free or loaded) end and a variable rigidity `k x` are not covered; the
operator is `-u''`, not `-(p u')'`.

## ii. Key results

- `isFixedFixedSolution_scale`, `exists_isFixedFixedSolution`, `IsFixedFixedSolution.eqOn`.
- `isFixedFixedSolution_axialDisplacement`, `IsFixedFixedSolution.eqOn_axialDisplacement`,
  `isFixedFixedSolution_twistAngle`, `IsFixedFixedSolution.eqOn_twistAngle`.
- `axialDisplacement_dimension`, `twistAngle_dimension`.
- `isClassicalSolution_axialDisplacement_scaled`.
- `fixedFreeDisplacement_not_isFixedFixedSolution`: a traction-free end is not covered.

## iii. Table of contents

- A. The fixed-fixed problem, scaling, existence and uniqueness
- B. Uniform axial load and uniform distributed torque
- C. Boundary example

## iv. References

- S. Timoshenko and J. M. Gere, *Mechanics of Materials*, 1972 (axially loaded bars, torsion of
  circular shafts).
- J. M. Gere and B. J. Goodno, *Mechanics of Materials*, 8th edition, 2013 (statically
  indeterminate bars and shafts under distributed loads).
-/

@[expose] public section

namespace Elasticity.PrismaticMembers

open Dimension Units.EngineeringQuantities

/-! ## A. The fixed-fixed problem, scaling, existence and uniqueness -/

/-- Fixed-fixed problem on `[0, L]` for rigidity `k` and distributed load `f`: `u` is `C²` on
`[0, L]`, satisfies `-(k * u'') = f` on `[0, L]` with derivatives taken within `[0, L]`, and
vanishes at both ends. -/
def IsFixedFixedSolution (k L : ℝ) (f u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Set.Icc 0 L) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) L, -(k * iteratedDerivWithin 2 u (Set.Icc 0 L) x) = f x) ∧
    u 0 = 0 ∧ u L = 0

/-- Chain rule for a linear change of variable between two sets: for `f` that is `Cⁿ` on `t`
and `(c * ·)` mapping `s` into `t`, the `n`-th derivative of `x ↦ f (c * x)` within `s` is
`c ^ n` times the `n`-th derivative of `f` within `t`. Adapted from Mathlib's
`iteratedDerivWithin_comp_const_smul`, which takes `s = t`. -/
private lemma iteratedDerivWithin_comp_mul {f : ℝ → ℝ} {s t : Set ℝ} {c : ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n f t) (hst : Set.MapsTo (c * ·) s t) (hs : UniqueDiffOn ℝ s)
    (ht : UniqueDiffOn ℝ t) {x : ℝ} (hx : x ∈ s) :
    iteratedDerivWithin n (fun x => f (c * x)) s x = c ^ n * iteratedDerivWithin n f t (c * x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hcx : c * x ∈ t := hst hx
    have h₀ : s.EqOn (iteratedDerivWithin n (fun x ↦ f (c * x)) s)
        (fun x => c ^ n * iteratedDerivWithin n f t (c * x)) :=
      fun y hy => ih hf.of_succ hy
    have h₁ : DifferentiableWithinAt ℝ (iteratedDerivWithin n f t) t (c * x) :=
      hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr n.lt_succ_self) ht _ hcx
    have h₂ : DifferentiableWithinAt ℝ (fun x => iteratedDerivWithin n f t (c * x)) s x := by
      rw [← Function.comp_def]
      exact DifferentiableWithinAt.comp _ h₁ (by fun_prop) hst
    rw [iteratedDerivWithin_succ, derivWithin_congr h₀ (ih hf.of_succ hx),
      derivWithin_const_mul (c ^ n) h₂, iteratedDerivWithin_succ,
      ← Function.comp_def, derivWithin.scomp x h₁ (by fun_prop) hst,
      derivWithin_const_mul _ differentiableWithinAt_id, derivWithin_id' _ _ (hs _ hx),
      smul_eq_mul, pow_succ]
    ring

/-- Multiplication by `L > 0` maps `[0, 1]` into `[0, L]`. -/
private lemma mapsTo_mul_Icc {L : ℝ} (hL : 0 < L) :
    Set.MapsTo (L * ·) (Set.Icc (0 : ℝ) 1) (Set.Icc 0 L) :=
  fun ξ hξ => ⟨mul_nonneg hL.le hξ.1, by nlinarith [hξ.2]⟩

/-- Multiplication by `1 / L` for `L > 0` maps `[0, L]` into `[0, 1]`. -/
private lemma mapsTo_div_Icc {L : ℝ} (hL : 0 < L) :
    Set.MapsTo ((1 / L) * ·) (Set.Icc (0 : ℝ) L) (Set.Icc 0 1) :=
  fun x hx => ⟨by have := hx.1; positivity, by
    rw [one_div, inv_mul_le_iff₀ hL, mul_one]; exact hx.2⟩

/-- Scaling `x = L * ξ`: `u` solves the problem on `[0, L]` exactly when `ξ ↦ u (L * ξ)` solves
the unit problem `-v'' = L ^ 2 / k * f (L * ξ)` on `[0, 1]`. -/
lemma isFixedFixedSolution_scale {k L : ℝ} (hL : 0 < L) (hk : k ≠ 0) (f u : ℝ → ℝ) :
    IsFixedFixedSolution k L f u ↔
      IsFixedFixedSolution 1 1 (fun ξ => L ^ 2 / k * f (L * ξ)) (fun ξ => u (L * ξ)) := by
  have hL0 : L ≠ 0 := hL.ne'
  have hs1 : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc one_pos
  have hsL : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) L) := uniqueDiffOn_Icc hL
  constructor
  · rintro ⟨hc, he, h0, h1⟩
    have hc' : ContDiffOn ℝ 2 (fun ξ => u (L * ξ)) (Set.Icc 0 1) :=
      hc.comp (by fun_prop) (mapsTo_mul_Icc hL)
    refine ⟨hc', fun ξ hξ => ?_, by simpa using h0, by simpa using h1⟩
    rw [iteratedDerivWithin_comp_mul hc (mapsTo_mul_Icc hL) hs1 hsL hξ]
    have := he (L * ξ) (mapsTo_mul_Icc hL hξ)
    change -(1 * (L ^ 2 * _)) = L ^ 2 / k * f (L * ξ)
    rw [← this]
    field_simp
  · rintro ⟨hc, he, h0, h1⟩
    have hx' : ∀ y : ℝ, L * (1 / L * y) = y := fun y => by field_simp
    have hfun : (fun x => (fun ξ => u (L * ξ)) (1 / L * x)) = u := by
      funext y
      change u (L * (1 / L * y)) = u y
      rw [hx']
    have hc' : ContDiffOn ℝ 2 u (Set.Icc 0 L) := by
      rw [← hfun]
      exact hc.comp (by fun_prop) (mapsTo_div_Icc hL)
    refine ⟨hc', fun x hx => ?_, by simpa using h0, by simpa using h1⟩
    have e := he ((1 / L) * x) (mapsTo_div_Icc hL hx)
    simp only [one_mul, hx'] at e
    have hcomp := iteratedDerivWithin_comp_mul (f := fun ξ => u (L * ξ)) hc (mapsTo_div_Icc hL)
      hsL hs1 hx
    rw [hfun] at hcomp
    rw [hcomp]
    have hD : iteratedDerivWithin 2 (fun ξ => u (L * ξ)) (Set.Icc 0 1) (1 / L * x) =
        -(L ^ 2 / k * f x) := by linarith
    rw [hD]
    field_simp
    rw [one_div, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hL0), one_mul]

/-- Existence for a load continuous on `[0, L]`. -/
lemma exists_isFixedFixedSolution {k L : ℝ} {f : ℝ → ℝ} (hL : 0 < L) (hk : 0 < k)
    (hf : ContinuousOn f (Set.Icc 0 L)) : ∃ u : ℝ → ℝ, IsFixedFixedSolution k L f u := by
  have hL0 : L ≠ 0 := hL.ne'
  have hfc : Continuous (fun ξ : Set.Icc (0 : ℝ) 1 => L ^ 2 / k * f (L * ξ)) := by
    have : ContinuousOn (fun ξ : ℝ => L ^ 2 / k * f (L * ξ)) (Set.Icc 0 1) :=
      continuousOn_const.mul (hf.comp (by fun_prop) (mapsTo_mul_Icc hL))
    exact continuousOn_iff_continuous_domRestrict.mp this
  obtain ⟨v, hvc, hve, hv0, hv1⟩ :=
    MathlibExt.Analysis.ODE.SturmLiouvilleExistence.sturm_liouville_existence 0 (fun _ => le_rfl)
      ⟨_, hfc⟩
  refine ⟨fun x => v ((1 / L) * x), (isFixedFixedSolution_scale hL hk.ne' f _).2 ?_⟩
  have hv : (fun ξ => (fun x => v ((1 / L) * x)) (L * ξ)) = v := by
    funext ξ; simp only; congr 1; field_simp
  rw [hv]
  refine ⟨hvc, fun ξ hξ => ?_, hv0, hv1⟩
  have := hve ξ hξ
  simp only [ContinuousMap.zero_apply, zero_mul, add_zero, ContinuousMap.coe_mk] at this
  rw [one_mul, this]

/-- Uniqueness: two solutions agree on `[0, L]`. -/
lemma IsFixedFixedSolution.eqOn {k L : ℝ} {f u v : ℝ → ℝ} (hk : 0 < k)
    (hu : IsFixedFixedSolution k L f u) (hv : IsFixedFixedSolution k L f v) :
    Set.EqOn u v (Set.Icc 0 L) := by
  intro x hx
  rcases (hx.1.trans hx.2).lt_or_eq with hL | hL
  · have su := (isFixedFixedSolution_scale hL hk.ne' f u).1 hu
    have sv := (isFixedFixedSolution_scale hL hk.ne' f v).1 hv
    have hs1 : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc one_pos
    have hcont : Continuous (fun ξ : Set.Icc (0 : ℝ) 1 =>
        -(iteratedDerivWithin 2 (fun ξ => u (L * ξ)) (Set.Icc 0 1) ξ)) :=
      continuousOn_iff_continuous_domRestrict.mp
        (su.1.continuousOn_iteratedDerivWithin le_rfl hs1).neg
    have key := MathlibExt.Analysis.ODE.SturmLiouvilleUniqueness.sturm_liouville_uniqueness 0
      (fun _ => le_rfl) ⟨_, hcont⟩ (fun ξ => u (L * ξ)) (fun ξ => v (L * ξ))
      ⟨su.1, fun ξ hξ => by simp, su.2.2.1, su.2.2.2⟩
      ⟨sv.1, fun ξ hξ => by
        simp only [ContinuousMap.zero_apply, zero_mul, add_zero, ContinuousMap.coe_mk]
        have h1 := su.2.1 ξ hξ
        have h2 := sv.2.1 ξ hξ
        linarith, sv.2.2.1, sv.2.2.2⟩
    have hξ : x / L ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hx.1 hL.le, (div_le_one hL).2 hx.2⟩
    have := key hξ
    simp only at this
    rwa [mul_div_cancel₀ x hL.ne'] at this
  · have hx0 : x = 0 := le_antisymm (hL ▸ hx.2) hx.1
    rw [hx0, hu.2.2.1, hv.2.2.1]

/-! ## B. Uniform axial load and uniform distributed torque -/

/-- Axial displacement of a fixed-fixed bar under the uniform load `q`:
`q * x * (L - x) / (2 * EA)`. -/
noncomputable def axialDisplacement (EA L q x : ℝ) : ℝ :=
  q * x * (L - x) / (2 * EA)

/-- Twist angle of a fixed-fixed circular shaft under the uniform distributed torque `t`:
`t * x * (L - x) / (2 * GJ)`. -/
noncomputable def twistAngle (GJ L t x : ℝ) : ℝ :=
  t * x * (L - x) / (2 * GJ)

/-- Derivative of the quadratic `a * y + b * y ^ 2`. -/
private lemma hasDerivAt_quad (a b x : ℝ) :
    HasDerivAt (fun y : ℝ => a * y + b * y ^ 2) (a + 2 * b * x) x := by
  have h1 := ((hasDerivAt_id' x).const_mul a).add ((hasDerivAt_pow 2 x).const_mul b)
  convert h1 using 1
  push_cast
  ring

/-- Derivative of the affine map `a + b * y`. -/
private lemma hasDerivAt_affine (a b x : ℝ) : HasDerivAt (fun y : ℝ => a + b * y) b x := by
  have h := ((hasDerivAt_id' x).const_mul b).const_add a
  convert h using 1
  ring

/-- Second derivative of the quadratic `a * x + b * x ^ 2`. -/
private lemma iteratedDeriv_two_quad (a b x : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => a * x + b * x ^ 2) x = 2 * b := by
  have hd : deriv (fun x : ℝ => a * x + b * x ^ 2) = fun x => a + 2 * b * x :=
    funext fun y => (hasDerivAt_quad a b y).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
  exact (hasDerivAt_affine a (2 * b) x).deriv

/-- Second derivative of the quadratic, as an iterated `deriv`. -/
private lemma deriv_deriv_quad (a b x : ℝ) :
    deriv (deriv (fun x : ℝ => a * x + b * x ^ 2)) x = 2 * b := by
  rw [← iteratedDeriv_two_quad a b x, iteratedDeriv_succ, iteratedDeriv_one]

/-- The uniform-load displacement solves the fixed-fixed bar problem. -/
lemma isFixedFixedSolution_axialDisplacement {EA L : ℝ} (hL : 0 < L) (hEA : 0 < EA) (q : ℝ) :
    IsFixedFixedSolution EA L (fun _ => q) (axialDisplacement EA L q) := by
  have axial_eq : axialDisplacement EA L q =
      fun x => q * L / (2 * EA) * x + (-(q / (2 * EA))) * x ^ 2 := by
    funext x
    unfold axialDisplacement
    ring
  have hpoly : ContDiff ℝ 2 (axialDisplacement EA L q) := by
    rw [axial_eq]; fun_prop
  refine ⟨hpoly.contDiffOn, fun x hx => ?_, by simp [axialDisplacement], by
    simp [axialDisplacement]⟩
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hL) hpoly.contDiffAt hx, axial_eq,
    iteratedDeriv_two_quad]
  field_simp

/-- Every solution of the uniform-load bar problem is the displacement
`q * x * (L - x) / (2 * EA)` on `[0, L]`. -/
lemma IsFixedFixedSolution.eqOn_axialDisplacement {EA L q : ℝ} {u : ℝ → ℝ} (hL : 0 < L)
    (hEA : 0 < EA) (hu : IsFixedFixedSolution EA L (fun _ => q) u) :
    Set.EqOn u (axialDisplacement EA L q) (Set.Icc 0 L) := by
  exact hu.eqOn hEA (isFixedFixedSolution_axialDisplacement hL hEA q)

/-- The same operator with `GJ` and the distributed torque `t`: the twist angle solves the
fixed-fixed shaft problem. -/
lemma isFixedFixedSolution_twistAngle {GJ L : ℝ} (hL : 0 < L) (hGJ : 0 < GJ) (t : ℝ) :
    IsFixedFixedSolution GJ L (fun _ => t) (twistAngle GJ L t) := by
  exact isFixedFixedSolution_axialDisplacement hL hGJ t

/-- Every solution of the uniform-torque shaft problem is the twist angle
`t * x * (L - x) / (2 * GJ)` on `[0, L]`. -/
lemma IsFixedFixedSolution.eqOn_twistAngle {GJ L t : ℝ} {φ : ℝ → ℝ} (hL : 0 < L)
    (hGJ : 0 < GJ) (hφ : IsFixedFixedSolution GJ L (fun _ => t) φ) :
    Set.EqOn φ (twistAngle GJ L t) (Set.Icc 0 L) := by
  exact hφ.eqOn hGJ (isFixedFixedSolution_twistAngle hL hGJ t)

/-- Units of the bar formula: a load per length `F L⁻¹` times two lengths over an axial
rigidity `F` is a length. -/
lemma axialDisplacement_dimension :
    forceDim / single ISQDimensionBase.length * single ISQDimensionBase.length *
        single ISQDimensionBase.length / forceDim = single ISQDimensionBase.length := by
  unfold forceDim
  decide

/-- Units of the shaft formula: a torque per length `(F L) L⁻¹` times two lengths over a
torsional rigidity `F L²` is dimensionless, a plane angle in radians. -/
lemma twistAngle_dimension :
    forceDim * single ISQDimensionBase.length / single ISQDimensionBase.length *
        single ISQDimensionBase.length * single ISQDimensionBase.length /
          (forceDim * single ISQDimensionBase.length * single ISQDimensionBase.length) = 1 := by
  unfold forceDim
  decide

/-- The scaled uniform-load displacement `ξ ↦ axialDisplacement EA L q (L * ξ)` is a classical
solution of the unit Dirichlet problem `-v'' = L ^ 2 / EA * q` of the finite element module. -/
lemma isClassicalSolution_axialDisplacement_scaled {EA : ℝ} (hEA : 0 < EA) (L q : ℝ) :
    MathlibExt.Analysis.ODE.FiniteElement1D.IsClassicalSolution (fun _ => L ^ 2 / EA * q)
      (fun ξ => axialDisplacement EA L q (L * ξ)) := by
  have hv : (fun ξ => axialDisplacement EA L q (L * ξ)) =
      fun ξ => q * L ^ 2 / (2 * EA) * ξ + (-(q * L ^ 2 / (2 * EA))) * ξ ^ 2 := by
    funext ξ; unfold axialDisplacement; ring
  rw [hv]
  refine ⟨by fun_prop, continuous_const, by simp, by ring, fun x _ => ?_⟩
  rw [deriv_deriv_quad]
  field_simp

/-! ## C. Boundary example -/

/-- Fixed-free bar under the uniform load `q`: `q * x * (2 * L - x) / (2 * EA)`. -/
noncomputable def fixedFreeDisplacement (EA L q x : ℝ) : ℝ :=
  q * x * (2 * L - x) / (2 * EA)

/-- A traction-free end is not covered: the fixed-free displacement satisfies the equation,
the fixed end and the traction-free end `EA * u' L = 0`, but for `q ≠ 0` it is not a solution
of the fixed-fixed problem. -/
lemma fixedFreeDisplacement_not_isFixedFixedSolution {EA L q : ℝ} (hL : 0 < L) (hEA : 0 < EA)
    (hq : q ≠ 0) :
    (∀ x : ℝ, -(EA * iteratedDeriv 2 (fixedFreeDisplacement EA L q) x) = q) ∧
      fixedFreeDisplacement EA L q 0 = 0 ∧
      EA * deriv (fixedFreeDisplacement EA L q) L = 0 ∧
      ¬ IsFixedFixedSolution EA L (fun _ => q) (fixedFreeDisplacement EA L q) := by
  have hff : fixedFreeDisplacement EA L q =
      fun x => q * L / EA * x + (-(q / (2 * EA))) * x ^ 2 := by
    funext x; unfold fixedFreeDisplacement; ring
  refine ⟨fun x => ?_, by simp [fixedFreeDisplacement], ?_, fun h => ?_⟩
  · rw [hff, iteratedDeriv_two_quad]
    field_simp
  · rw [hff, (hasDerivAt_quad _ _ L).deriv]
    field_simp
    ring
  · have hL' := h.2.2.2
    unfold fixedFreeDisplacement at hL'
    have : q * L * (2 * L - L) = 0 := by
      field_simp at hL'
      linarith
    have : q * L ^ 2 = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hq h1
    · exact hL.ne' (pow_eq_zero_iff two_ne_zero |>.mp h1)

end Elasticity.PrismaticMembers

end
