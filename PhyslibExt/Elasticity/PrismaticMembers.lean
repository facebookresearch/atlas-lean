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
public import PhyslibExt.Mechanics.EngineeringStatics
public import PhyslibExt.Mechanics.EulerBernoulliBeam
public import PhyslibExt.Units.EngineeringQuantities
import MathlibExt.Analysis.Calculus.ZeroFourthDerivative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prismatic members: bars and shafts, cantilever and simply supported beams, closed-cell torsion

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
Boundaries: the fixed-fixed problem has no traction (free or loaded) end; a member fixed at one
end and loaded at the other is the fixed-traction problem below. A variable rigidity `k x` is
not covered: the operator is `-u''`, not `-(p u')'`.

A prismatic Euler-Bernoulli beam of positive length `L` and constant bending stiffness `EI`,
clamped at `x = 0` and free at `x = L`, carries a constant distributed load `q` and a tip force
`P`; the deflection `w`, `q` and `P` are positive in the same transverse direction. The model is
`EI * w'''' = q` with `w 0 = 0`, `w' 0 = 0`, `EI * w'' L = 0` (zero moment at the free end)
and `-(EI * w''' L) = P` (the shear force at the free end balances the tip force); the
predicate `IsCantileverSolution` also records `0 < L`. The polynomial `cantileverDeflection`
satisfies the equation and the four conditions, and a solution is unique on `[0, L]`: the
difference of two solutions has zero fourth derivative, so it is a cubic on `[0, L]`, and the
four conditions force it to vanish. Model inputs: Euler-Bernoulli small deflection, constant
`EI > 0`, the stated shear sign. This is a finite clamped-free problem, not a periodic model:
the clamped-clamped profile `1 - cos (2 π x / L)` meets both clamped conditions but violates
the free-end moment condition.

A bar of length `L > 0` and constant rigidity `k = EA` fixed at `x = 0` and loaded at `x = L` by
an end force `P`, positive along the outward normal `+x` (tension positive), under a distributed
axial load `f` continuous on `[0, L]`, solves `-(k * u'') = f` on `[0, L]` with `u 0 = 0` and
`k * u' L = P` (`IsFixedTractionSolution`; derivatives within `[0, L]`). Integrating once from
`x` to the loaded end gives the load path `k * u' x = P + ∫ y in x..L, f y`: the internal axial
force is the end force plus the load carried between `x` and `L`. So
`u' x = (P + ∫ y in x..L, f y) / k` (`fixedTractionStrain`), `u` is its primitive from the fixed
end (`fixedTractionDisplacement`), this function solves the problem, and every solution equals
it on `[0, L]`. Under a uniform load `q` it is `P * x / k` plus `fixedFreeDisplacement`. A
circular shaft fixed at `x = 0` under a distributed torque `t` and an end torque `T` is the same
problem with `k = GJ`, handled by the same lemmas. With both ends free (end forces `P₀` at
`x = 0`, outward normal `-x`, and `P₁` at `x = L`) a solution can be shifted by a rigid
translation and exists only if the net load vanishes, `P₀ + P₁ + ∫₀ᴸ f = 0`.

A prismatic member whose cross-section is a single thin closed rectangular cell, with median sides
`a, b > 0` (the median rectangle `[-a/2, a/2] × [-b/2, b/2]` in the section plane), uniform wall
thickness `t > 0` and shear modulus `G > 0`, carries a uniform shear flow `q` (force per length of
median line) in torsion. On each straight wall the flow integrates to the resultant `q ℓ` along the
wall, with line of action through the wall midpoint; positive `q` circulates counterclockwise
about `+z`. The four wall resultants have zero sum, so they form a couple, and their moment
`Mechanics.EngineeringStatics.momentAbout` about every reference point is `(0, 0, 2 a b q)`: the
cell carries the torque `T = 2 a b q = 2 A q`, with `A = a b` the enclosed area. The stated
thin-wall compatibility law, the declared reduced model of the twist (Bredt's second formula),
equates the circulation `∑ walls (q / (G t)) ℓ` of the wall shear strain to `2 A θ'`; with the
median perimeter `2 (a + b)` it gives the twist rate `θ' = T (a + b) / (2 G a² b² t)`. The wall
shear stress is `τ = q / t = T / (2 a b t)`, and `T = G J θ'` with the torsion constant
`J = 4 A² t / (2 (a + b)) = 2 a² b² t / (a + b)`, so `G J` is the cell's effective torsional
rigidity, the `GJ` of the circular-shaft reading above. Not claimed: a convergence theorem from
three-dimensional elasticity, warping restraint, or the open-section formula. Cutting one wall
leaves wall resultants that do not sum to zero, so they are not a couple and no closed-cell torque
is carried; at zero thickness the torsion constant vanishes, so no twist rate carries a nonzero
torque.

A prismatic Euler-Bernoulli beam of positive length `L` and constant bending stiffness `EI > 0`
rests on a pin at `x = 0` and a pin (or roller) at `x = L` and carries a constant distributed load
`q`; the deflection `w` and `q` are positive in the same transverse direction, and a support
reaction is positive when it acts against the load. The model is `EI * w'''' = q` with
`w 0 = w L = 0` and `w'' 0 = w'' L = 0` (`IsSimplySupportedSolution`, which also records
`0 < L`); the pins constrain the deflection, not the slope. The existing quartic witness
`Mechanics.EulerBernoulli.uniformLoadDeflection q EI L` solves the problem, and every solution
agrees with it on `[0, L]`: the difference of two solutions is a cubic on `[0, L]` by the cubic
lemma, and the two deflection and two curvature conditions force it to vanish. So the solutions are
exactly the `C⁴` functions equal to the quartic on `[0, L]`; every solution has the support
reactions `-(EI * w''' 0) = EI * w''' L = q * L / 2` (shear force `-(EI * w''')`, as for the
cantilever) and the slopes `± q * L ^ 3 / (24 * EI)` at the pins. Replacing the two moment
conditions by clamped slopes gives the different solution `q * x ^ 2 * (L - x) ^ 2 / (24 * EI)`.

## ii. Key results

- `isFixedFixedSolution_scale`, `exists_isFixedFixedSolution`, `IsFixedFixedSolution.eqOn`.
- `isFixedFixedSolution_axialDisplacement`, `IsFixedFixedSolution.eqOn_axialDisplacement`,
  `isFixedFixedSolution_twistAngle`, `IsFixedFixedSolution.eqOn_twistAngle`.
- `axialDisplacement_dimension`, `twistAngle_dimension`.
- `isClassicalSolution_axialDisplacement_scaled`.
- `fixedFreeDisplacement_not_isFixedFixedSolution`: a traction-free end is not a fixed-fixed
  problem; with `P = 0` it is the fixed-traction problem of section G.
- `cantileverDeflection_iteratedDeriv_four`, `cantileverDeflection_zero`,
  `deriv_cantileverDeflection_zero`, `cantileverDeflection_moment_right`,
  `cantileverDeflection_shear_right`, `isCantileverSolution_cantileverDeflection`: the
  cantilever polynomial and its four boundary conditions.
- `IsCantileverSolution.eqOn`: uniqueness on `[0, L]`, through the cubic lemma
  `MathlibExt.Analysis.Calculus.ZeroFourthDerivative.exists_cubic_of_iteratedDeriv_four_eq_zero`.
- `cantileverDeflection_load_zero`, `cosine_profile_fails_moment`: the tip-force term and a
  periodic profile that is not a cantilever solution.
- `derivWithin_fixedTractionDisplacement`, `derivWithin_fixedTractionStrain`,
  `isFixedTractionSolution_fixedTractionDisplacement`: the constructed fixed-traction solution.
- `IsFixedTractionSolution.axialForce_eq`: the load path `k * u' x = P + ∫ y in x..L, f y`.
- `IsFixedTractionSolution.eqOn_fixedTractionDisplacement`, `IsFixedTractionSolution.eqOn`:
  uniqueness on `[0, L]`; `IsFixedTractionSolution.twist`: the circular-shaft reading.
- `fixedTractionDisplacement_const`: the uniform-load closed form.
- `IsFreeFreeSolution.add_const`, `IsFreeFreeSolution.net_load`: two free ends admit rigid
  translations and need zero net load.
- `resultantForce_cellWallForce`, `momentAbout_cellWall`: the four wall resultants of the thin
  closed cell form a couple of moment `(0, 0, 2 a b q)` about every reference point.
- `isClosedCellCompatible_iff`: under the compatibility law the twist rate is
  `T (a + b) / (2 G a² b² t)`.
- `wallShearStress_eq`, `closedCellTorsionConstant_eq`, `torque_eq_rigidity_mul_twistRate`:
  `τ = q / t = T / (2 a b t)` for `t > 0`, Bredt's torsion constant `J = 4 A² / ∑ ℓ / t`, and
  `T = G J θ'`.
- `isSimplySupportedSolution_uniformLoadDeflection`, `IsSimplySupportedSolution.eqOn`,
  `isSimplySupportedSolution_iff`: the simply supported beam under a uniform load, existence and
  uniqueness on `[0, L]`.
- `IsSimplySupportedSolution.reactions`, `IsSimplySupportedSolution.slopes`: the support reactions
  `q * L / 2` and the unconstrained slopes of every solution.
- `clampedSlopes_change_solution`: clamped slopes in place of the moment conditions give a
  different solution.

## iii. Table of contents

- A. The fixed-fixed problem, scaling, existence and uniqueness
- B. Uniform axial load and uniform distributed torque
- C. Boundary example
- D. Clamped-free cantilever: the polynomial solution
- E. Clamped-free cantilever: uniqueness
- F. Clamped-free cantilever: tip-force term and boundary example
- G. Fixed-traction bar and shaft: load path, existence and uniqueness
- H. Fixed-traction bar: uniform load
- I. Boundary example: two free ends
- J. Thin closed rectangular cell: wall resultants and torque
- K. Thin closed rectangular cell: compatibility, shear stress and rigidity
- L. Simply supported beam: existence and uniqueness
- M. Simply supported beam: support reactions and slopes
- N. Simply supported beam: clamped slopes change the solution

## iv. References

- S. Timoshenko and J. M. Gere, *Mechanics of Materials*, 1972 (axially loaded bars, torsion of
  circular shafts, cantilever deflections).
- J. M. Gere and B. J. Goodno, *Mechanics of Materials*, 8th edition, 2013 (statically
  indeterminate bars and shafts under distributed loads; bars with distributed axial loads and
  nonuniform torsion; differential equations of the deflection curve; thin-walled tubes in
  torsion: shear flow, `T = 2 q A_m`, `τ = T / (2 t A_m)`, `J = 4 A_m² / ∫ ds / t`; simply
  supported and fixed-end beams under a uniform load).
- S. Timoshenko and J. N. Goodier, *Theory of Elasticity*, 3rd edition, 1970 (torsion of thin
  tubular members: the twist condition `∮ τ ds = 2 G θ' A`).
-/

@[expose] public section

namespace Elasticity.PrismaticMembers

open Dimension Units.EngineeringQuantities MathlibExt.Analysis.Calculus.ZeroFourthDerivative

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

/-- A traction-free end is not a fixed-fixed problem: the fixed-free displacement satisfies the
equation, the fixed end and the traction-free end `EA * u' L = 0`, but for `q ≠ 0` it is not a
solution of the fixed-fixed problem. -/
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

/-! ## D. Clamped-free cantilever: the polynomial solution -/

/-- Cantilever deflection under the uniform load `q` and the tip force `P`:
`q * x ^ 2 * (6 * L ^ 2 - 4 * L * x + x ^ 2) / (24 * EI) + P * x ^ 2 * (3 * L - x) / (6 * EI)`. -/
noncomputable def cantileverDeflection (EI L q P x : ℝ) : ℝ :=
  q * x ^ 2 * (6 * L ^ 2 - 4 * L * x + x ^ 2) / (24 * EI) +
    P * x ^ 2 * (3 * L - x) / (6 * EI)

/-- The clamped-free cantilever problem on a beam of positive length `L`: `w` is `C⁴`,
satisfies `EI * w'''' = q` on `(0, L)`, and meets the clamped conditions at `0` and the free-end
moment and shear conditions at `L`. -/
structure IsCantileverSolution (EI L q P : ℝ) (w : ℝ → ℝ) : Prop where
  span_pos : 0 < L
  contDiff : ContDiff ℝ 4 w
  eq : ∀ x ∈ Set.Ioo (0 : ℝ) L, EI * iteratedDeriv 4 w x = q
  zero_left : w 0 = 0
  slope_left : deriv w 0 = 0
  moment_right : EI * iteratedDeriv 2 w L = 0
  shear_right : -(EI * iteratedDeriv 3 w L) = P

/-- Normal form of the cantilever polynomial in powers of `x`. -/
private lemma cd_eq (EI L q P : ℝ) : cantileverDeflection EI L q P = fun x =>
    q / (24 * EI) * x ^ 4 + (-(q * L) / (6 * EI) - P / (6 * EI)) * x ^ 3 +
      (q * L ^ 2 / (4 * EI) + P * L / (2 * EI)) * x ^ 2 := by
  funext x
  unfold cantileverDeflection
  ring

/-- The cantilever polynomial is `C⁴`. -/
private lemma cd_contDiff (EI L q P : ℝ) : ContDiff ℝ 4 (cantileverDeflection EI L q P) := by
  rw [cd_eq]
  fun_prop

/-- Iterated derivatives of the cantilever polynomial, term by term. -/
private lemma iteratedDeriv_cd (EI L q P : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (cantileverDeflection EI L q P) x =
      q / (24 * EI) * iteratedDeriv n (fun x : ℝ => x ^ 4) x +
      (-(q * L) / (6 * EI) - P / (6 * EI)) * iteratedDeriv n (fun x : ℝ => x ^ 3) x +
      (q * L ^ 2 / (4 * EI) + P * L / (2 * EI)) * iteratedDeriv n (fun x : ℝ => x ^ 2) x := by
  rw [cd_eq]
  have h1 : ContDiffAt ℝ n (fun x : ℝ => q / (24 * EI) * x ^ 4 +
      (-(q * L) / (6 * EI) - P / (6 * EI)) * x ^ 3) x := by fun_prop
  have h2 : ContDiffAt ℝ n (fun x : ℝ => (q * L ^ 2 / (4 * EI) + P * L / (2 * EI)) * x ^ 2) x := by
    fun_prop
  have h3 : ContDiffAt ℝ n (fun x : ℝ => q / (24 * EI) * x ^ 4) x := by fun_prop
  have h4 : ContDiffAt ℝ n (fun x : ℝ => (-(q * L) / (6 * EI) - P / (6 * EI)) * x ^ 3) x := by
    fun_prop
  rw [iteratedDeriv_fun_add h1 h2, iteratedDeriv_fun_add h3 h4]
  simp only [iteratedDeriv_const_mul_field]

/-- The polynomial satisfies `EI * w'''' = q` at every point. -/
lemma cantileverDeflection_iteratedDeriv_four {EI : ℝ} (hEI : EI ≠ 0) (L q P x : ℝ) :
    EI * iteratedDeriv 4 (cantileverDeflection EI L q P) x = q := by
  rw [iteratedDeriv_cd]
  simp [iteratedDeriv_pow]
  field_simp

/-- Clamped end: zero deflection. -/
lemma cantileverDeflection_zero (EI L q P : ℝ) : cantileverDeflection EI L q P 0 = 0 := by
  unfold cantileverDeflection
  ring

/-- Clamped end: zero slope. -/
lemma deriv_cantileverDeflection_zero (EI L q P : ℝ) :
    deriv (cantileverDeflection EI L q P) 0 = 0 := by
  rw [← iteratedDeriv_one, iteratedDeriv_cd]
  simp [iteratedDeriv_pow]

/-- Free end: zero bending moment. -/
lemma cantileverDeflection_moment_right (EI L q P : ℝ) :
    EI * iteratedDeriv 2 (cantileverDeflection EI L q P) L = 0 := by
  rw [iteratedDeriv_cd]
  have e4 : iteratedDeriv 2 (fun x : ℝ => x ^ 4) L = 12 * L ^ 2 := by
    simp [iteratedDeriv_pow]
  have e3 : iteratedDeriv 2 (fun x : ℝ => x ^ 3) L = 6 * L := by
    simp [iteratedDeriv_pow]
  have e2 : iteratedDeriv 2 (fun x : ℝ => x ^ 2) L = 2 := by
    simp [iteratedDeriv_pow]
  rw [e4, e3, e2]
  ring

/-- Free end: the shear force balances the tip force. -/
lemma cantileverDeflection_shear_right {EI : ℝ} (hEI : EI ≠ 0) (L q P : ℝ) :
    -(EI * iteratedDeriv 3 (cantileverDeflection EI L q P) L) = P := by
  rw [iteratedDeriv_cd]
  simp [iteratedDeriv_pow]
  field_simp
  ring

/-- Existence: for a positive span the polynomial solves the clamped-free problem. -/
lemma isCantileverSolution_cantileverDeflection {EI L : ℝ} (hEI : 0 < EI) (hL : 0 < L)
    (q P : ℝ) : IsCantileverSolution EI L q P (cantileverDeflection EI L q P) := by
  exact ⟨hL, cd_contDiff EI L q P,
    fun x _ => cantileverDeflection_iteratedDeriv_four hEI.ne' L q P x,
    cantileverDeflection_zero EI L q P, deriv_cantileverDeflection_zero EI L q P,
    cantileverDeflection_moment_right EI L q P, cantileverDeflection_shear_right hEI.ne' L q P⟩

/-! ## E. Clamped-free cantilever: uniqueness -/

/-- The first three derivatives of a cubic. -/
private lemma iteratedDeriv_cubic (c₀ c₁ c₂ c₃ x : ℝ) :
    iteratedDeriv 1 (fun y : ℝ => c₀ + c₁ * y + c₂ * y ^ 2 + c₃ * y ^ 3) x =
        c₁ + 2 * c₂ * x + 3 * c₃ * x ^ 2 ∧
      iteratedDeriv 2 (fun y : ℝ => c₀ + c₁ * y + c₂ * y ^ 2 + c₃ * y ^ 3) x =
        2 * c₂ + 6 * c₃ * x ∧
      iteratedDeriv 3 (fun y : ℝ => c₀ + c₁ * y + c₂ * y ^ 2 + c₃ * y ^ 3) x = 6 * c₃ := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp (disch := fun_prop) [iteratedDeriv_fun_add, iteratedDeriv_const_mul_field,
      iteratedDeriv_pow, iteratedDeriv_const, iteratedDeriv_const_mul_field c₁ (fun y : ℝ => y),
      iteratedDeriv_fun_id]
    ring

/-- Uniqueness: every solution of the clamped-free problem agrees with the polynomial on
`[0, L]`. -/
lemma IsCantileverSolution.eqOn {EI L q P : ℝ} {w : ℝ → ℝ} (hEI : 0 < EI)
    (hw : IsCantileverSolution EI L q P w) :
    Set.EqOn w (cantileverDeflection EI L q P) (Set.Icc 0 L) := by
  set d := fun y => w y - cantileverDeflection EI L q P y with hd_def
  have hdc : ContDiff ℝ 4 d := hw.contDiff.sub (cd_contDiff EI L q P)
  have hsub : ∀ (k : ℕ) (y : ℝ), k ≤ 4 → iteratedDeriv k d y =
      iteratedDeriv k w y - iteratedDeriv k (cantileverDeflection EI L q P) y := by
    intro k y hk
    have h1 : ContDiffAt ℝ k w y := (hw.contDiff.of_le (by exact_mod_cast hk)).contDiffAt
    have h2 : ContDiffAt ℝ k (cantileverDeflection EI L q P) y :=
      ((cd_contDiff EI L q P).of_le (by exact_mod_cast hk)).contDiffAt
    exact iteratedDeriv_fun_sub h1 h2
  have h4 : ∀ y ∈ Set.Ioo (0 : ℝ) L, iteratedDeriv 4 d y = 0 := by
    intro y hy
    rw [hsub 4 y le_rfl]
    have e1 := hw.eq y hy
    have e2 := cantileverDeflection_iteratedDeriv_four hEI.ne' L q P y
    have : EI * (iteratedDeriv 4 w y - iteratedDeriv 4 (cantileverDeflection EI L q P) y) = 0 := by
      rw [mul_sub, e1, e2, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hEI.ne'
  -- the difference is a cubic on `[0, L]`, so its derivatives on `[0, L]` are the cubic's
  obtain ⟨c₀, c₁, c₂, c₃, hc⟩ := exists_cubic_of_iteratedDeriv_four_eq_zero hdc h4
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) L) := uniqueDiffOn_Icc hw.span_pos
  have hcub : ∀ k ≤ 3, ∀ y ∈ Set.Icc (0 : ℝ) L, iteratedDeriv k d y =
      iteratedDeriv k (fun x : ℝ => c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3) y := by
    intro k hk y hy
    rw [← iteratedDerivWithin_eq_iteratedDeriv hU
        ((hdc.of_le (by exact_mod_cast (show k ≤ 4 by omega))).contDiffAt) hy,
      ← iteratedDerivWithin_eq_iteratedDeriv hU (by fun_prop) hy]
    exact iteratedDerivWithin_congr hc hy
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_rfl, hw.span_pos.le⟩
  have hLm : L ∈ Set.Icc (0 : ℝ) L := ⟨hw.span_pos.le, le_rfl⟩
  -- the four traces of the difference vanish: shear and moment at `L`, slope and deflection at `0`
  have t3 : iteratedDeriv 3 d L = 0 := by
    rw [hsub 3 L (by norm_num)]
    have e1 := hw.shear_right
    have e2 := cantileverDeflection_shear_right hEI.ne' L q P
    have : EI * (iteratedDeriv 3 w L - iteratedDeriv 3 (cantileverDeflection EI L q P) L) = 0 := by
      linarith [mul_sub EI (iteratedDeriv 3 w L)
        (iteratedDeriv 3 (cantileverDeflection EI L q P) L)]
    exact (mul_eq_zero.mp this).resolve_left hEI.ne'
  have t2 : iteratedDeriv 2 d L = 0 := by
    rw [hsub 2 L (by norm_num)]
    have e1 := hw.moment_right
    have e2 := cantileverDeflection_moment_right EI L q P
    have : EI * (iteratedDeriv 2 w L - iteratedDeriv 2 (cantileverDeflection EI L q P) L) = 0 := by
      rw [mul_sub, e1, e2, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hEI.ne'
  have t1 : iteratedDeriv 1 d 0 = 0 := by
    rw [hsub 1 0 (by norm_num), iteratedDeriv_one, iteratedDeriv_one, hw.slope_left,
      deriv_cantileverDeflection_zero, sub_self]
  have t0 : d 0 = 0 := by
    simp only [hd_def, hw.zero_left, cantileverDeflection_zero, sub_self]
  -- so the four coefficients of the cubic vanish
  obtain ⟨-, p2, p3⟩ := iteratedDeriv_cubic c₀ c₁ c₂ c₃ L
  obtain ⟨p1, -, -⟩ := iteratedDeriv_cubic c₀ c₁ c₂ c₃ 0
  have e3 : c₃ = 0 := by linarith [hcub 3 le_rfl L hLm]
  have e2 : c₂ = 0 := by
    have h6 : 6 * c₃ * L = 0 := by rw [e3]; ring
    linarith [hcub 2 (by norm_num) L hLm]
  have e1 : c₁ = 0 := by linarith [hcub 1 (by norm_num) 0 h0]
  have e0 : c₀ = 0 := by linarith [hc 0 h0]
  intro x hx
  simpa [hd_def, e0, e1, e2, e3, sub_eq_zero] using hc x hx

/-! ## F. Clamped-free cantilever: tip-force term and boundary example -/

/-- With no distributed load the deflection is the tip-force term
`P * x ^ 2 * (3 * L - x) / (6 * EI)`. -/
lemma cantileverDeflection_load_zero (EI L P x : ℝ) :
    cantileverDeflection EI L 0 P x = P * x ^ 2 * (3 * L - x) / (6 * EI) := by
  unfold cantileverDeflection
  ring

/-- The clamped-clamped profile `1 - cos (2 π x / L)` meets both clamped conditions at `0`,
but its free-end moment `EI * w'' L` is not zero, so it is not a cantilever solution. -/
lemma cosine_profile_fails_moment {EI L : ℝ} (hEI : 0 < EI) (hL : 0 < L) :
    (fun x : ℝ => 1 - Real.cos (2 * Real.pi * x / L)) 0 = 0 ∧
      deriv (fun x : ℝ => 1 - Real.cos (2 * Real.pi * x / L)) 0 = 0 ∧
      EI * iteratedDeriv 2 (fun x : ℝ => 1 - Real.cos (2 * Real.pi * x / L)) L ≠ 0 := by
  have hL' : L ≠ 0 := hL.ne'
  set c : ℝ := 2 * Real.pi / L with hc
  have hfun :
      (fun x : ℝ => 1 - Real.cos (2 * Real.pi * x / L)) = fun x => 1 - Real.cos (c * x) := by
    funext x
    rw [hc]
    ring_nf
  have hd1 : ∀ x, HasDerivAt (fun x : ℝ => 1 - Real.cos (c * x)) (c * Real.sin (c * x)) x := by
    intro x
    have h := ((hasDerivAt_id' x).const_mul c).cos.const_sub 1
    convert h using 1
    ring
  have hderiv : deriv (fun x : ℝ => 1 - Real.cos (c * x)) = fun x => c * Real.sin (c * x) :=
    funext fun x => (hd1 x).deriv
  have hd2 : ∀ x, HasDerivAt (fun x : ℝ => c * Real.sin (c * x)) (c * c * Real.cos (c * x)) x := by
    intro x
    have h := (((hasDerivAt_id' x).const_mul c).sin).const_mul c
    convert h using 1
    ring
  rw [hfun]
  refine ⟨by simp, by rw [hderiv]; simp, ?_⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv, (hd2 L).deriv]
  have hcL : c * L = 2 * Real.pi := by rw [hc]; field_simp
  rw [hcL, Real.cos_two_pi, mul_one]
  have hc0 : c ≠ 0 := by rw [hc]; exact div_ne_zero (by positivity) hL'
  exact mul_ne_zero hEI.ne' (mul_ne_zero hc0 hc0)

/-! ## G. Fixed-traction bar and shaft: load path, existence and uniqueness -/

/-- Fixed-traction problem on `[0, L]` for rigidity `k`, distributed load `f` and end force `P`:
`u` is `C²` on `[0, L]`, satisfies `-(k * u'') = f` on `[0, L]` with derivatives taken within
`[0, L]`, vanishes at the fixed end `x = 0`, and has end force `k * u' L = P` at `x = L`, where
the outward normal is `+x` and tension is positive. -/
def IsFixedTractionSolution (k L P : ℝ) (f u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Set.Icc 0 L) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) L, -(k * iteratedDerivWithin 2 u (Set.Icc 0 L) x) = f x) ∧
    u 0 = 0 ∧ k * derivWithin u (Set.Icc 0 L) L = P

/-- The strain of the load path, `u' x = (P + ∫ y in x..L, f y) / k`. -/
noncomputable def fixedTractionStrain (k L P : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (P + ∫ y in x..L, f y) / k

/-- The displacement, the primitive of `fixedTractionStrain` from the fixed end `x = 0`. -/
noncomputable def fixedTractionDisplacement (k L P : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in (0 : ℝ)..x, fixedTractionStrain k L P f y

/-- For a load continuous on `[0, L]`, the constructed strain is continuous on `[0, L]`. -/
private lemma continuousOn_fixedTractionStrain {k L P : ℝ} {f : ℝ → ℝ} (hL : 0 < L)
    (hf : ContinuousOn f (Set.Icc 0 L)) :
    ContinuousOn (fixedTractionStrain k L P f) (Set.Icc 0 L) := by
  have hL0 : (0 : ℝ) ≤ L := le_of_lt hL
  have huIcc : Set.uIcc (0 : ℝ) L = Set.Icc 0 L := Set.uIcc_of_le hL0
  have hf_uIcc : ContinuousOn f (Set.uIcc 0 L) := by simpa [huIcc] using hf
  have hint : MeasureTheory.IntegrableOn f (Set.uIcc 0 L) MeasureTheory.volume :=
    hf_uIcc.integrableOn_uIcc
  have hprim : ContinuousOn (fun x => ∫ y in x..L, f y) (Set.uIcc 0 L) :=
    intervalIntegral.continuousOn_primitive_interval_left hint
  have hprim' : ContinuousOn (fun x => ∫ y in x..L, f y) (Set.Icc 0 L) := by
    simpa [huIcc] using hprim
  have hadd : ContinuousOn (fun x => P + ∫ y in x..L, f y) (Set.Icc 0 L) :=
    hprim'.const_add P
  have hdiv : ContinuousOn (fun x => (P + ∫ y in x..L, f y) / k) (Set.Icc 0 L) :=
    hadd.div_const k
  change ContinuousOn (fun x => (P + ∫ y in x..L, f y) / k) (Set.Icc 0 L)
  exact hdiv

/-- The constructed displacement has derivative `fixedTractionStrain k L P f x` within `[0, L]`
at every `x ∈ [0, L]`. -/
private lemma hasDerivWithinAt_fixedTractionDisplacement {k L P : ℝ} {f : ℝ → ℝ} (hL : 0 < L)
    (hf : ContinuousOn f (Set.Icc 0 L)) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) L) :
    HasDerivWithinAt (fixedTractionDisplacement k L P f) (fixedTractionStrain k L P f x)
      (Set.Icc 0 L) x := by
  have : Fact (x ∈ Set.Icc (0 : ℝ) L) := Fact.mk hx
  have hstr : ContinuousOn (fixedTractionStrain k L P f) (Set.Icc 0 L) :=
    continuousOn_fixedTractionStrain hL hf
  have hcont : ContinuousWithinAt (fixedTractionStrain k L P f) (Set.Icc 0 L) x :=
    hstr.continuousWithinAt hx
  have hmeas := ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin
    (μ:=MeasureTheory.volume) hstr measurableSet_Icc x
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hxL : x ≤ L := hx.2
  have hsub : Set.Icc (0 : ℝ) x ⊆ Set.Icc 0 L := Set.Icc_subset_Icc_right hxL
  have hstr0 : ContinuousOn (fixedTractionStrain k L P f) (Set.Icc 0 x) := hstr.mono hsub
  have hint := ContinuousOn.intervalIntegrable_of_Icc (μ:=MeasureTheory.volume) hx0 hstr0
  have h : HasDerivWithinAt (fun u => ∫ y in (0 : ℝ)..u, fixedTractionStrain k L P f y)
      (fixedTractionStrain k L P f x) (Set.Icc 0 L) x :=
    intervalIntegral.integral_hasDerivWithinAt_right hint hmeas hcont
  change HasDerivWithinAt (fun u => ∫ y in (0 : ℝ)..u, fixedTractionStrain k L P f y)
    (fixedTractionStrain k L P f x) (Set.Icc 0 L) x
  exact h

/-- The constructed strain has derivative `-f x / k` within `[0, L]` at every `x ∈ [0, L]`. -/
private lemma hasDerivWithinAt_fixedTractionStrain {k L P : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 L)) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) L) :
    HasDerivWithinAt (fixedTractionStrain k L P f) (-f x / k) (Set.Icc 0 L) x := by
  have : Fact (x ∈ Set.Icc (0 : ℝ) L) := Fact.mk hx
  have hcont : ContinuousWithinAt f (Set.Icc 0 L) x := hf.continuousWithinAt hx
  have hmeas := ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin
    (μ:=MeasureTheory.volume) hf measurableSet_Icc x
  have hx0 : (0 : ℝ) ≤ x := hx.1
  have hxL : x ≤ L := hx.2
  have hsub : Set.Icc x L ⊆ Set.Icc (0 : ℝ) L := Set.Icc_subset_Icc_left hx0
  have hf0 : ContinuousOn f (Set.Icc x L) := hf.mono hsub
  have hint := ContinuousOn.intervalIntegrable_of_Icc (μ:=MeasureTheory.volume) hxL hf0
  have hG : HasDerivWithinAt (fun u => ∫ y in u..L, f y) (-f x) (Set.Icc 0 L) x :=
    intervalIntegral.integral_hasDerivWithinAt_left hint hmeas hcont
  have hPG : HasDerivWithinAt (fun u => P + ∫ y in u..L, f y) (-f x) (Set.Icc 0 L) x :=
    HasDerivWithinAt.const_add P hG
  have hstr : HasDerivWithinAt (fun u => (P + ∫ y in u..L, f y) / k) (-f x / k)
      (Set.Icc 0 L) x :=
    HasDerivWithinAt.div_const hPG k
  change HasDerivWithinAt (fun u => (P + ∫ y in u..L, f y) / k) (-f x / k) (Set.Icc 0 L) x
  exact hstr

/-- For a load continuous on `[0, L]`, the constructed strain is `C¹` on `[0, L]`. -/
private lemma contDiffOn_fixedTractionStrain {k L P : ℝ} {f : ℝ → ℝ} (hL : 0 < L)
    (hf : ContinuousOn f (Set.Icc 0 L)) :
    ContDiffOn ℝ 1 (fixedTractionStrain k L P f) (Set.Icc 0 L) := by
  have hU : UniqueDiffOn ℝ (Set.Icc 0 L) := uniqueDiffOn_Icc hL
  rw [contDiffOn_one_iff_derivWithin hU]
  constructor
  · intro x hx
    exact (hasDerivWithinAt_fixedTractionStrain hf x hx).differentiableWithinAt
  · have h2 : ∀ x ∈ Set.Icc (0 : ℝ) L,
        derivWithin (fixedTractionStrain k L P f) (Set.Icc 0 L) x = -f x / k := by
      intro x hx
      exact (hasDerivWithinAt_fixedTractionStrain hf x hx).derivWithin
        (hU.uniqueDiffWithinAt hx)
    have hfc : ContinuousOn (fun x => -f x / k) (Set.Icc 0 L) := hf.neg.div_const k
    exact hfc.congr h2

/-- For a load continuous on `[0, L]`, the constructed displacement is `C²` on `[0, L]`. -/
private lemma contDiffOn_two_fixedTractionDisplacement {k L P : ℝ} {f : ℝ → ℝ} (hL : 0 < L)
    (hf : ContinuousOn f (Set.Icc 0 L)) :
    ContDiffOn ℝ 2 (fixedTractionDisplacement k L P f) (Set.Icc 0 L) := by
  have hU : UniqueDiffOn ℝ (Set.Icc 0 L) := uniqueDiffOn_Icc hL
  have hstr1 : ContDiffOn ℝ 1 (fixedTractionStrain k L P f) (Set.Icc 0 L) :=
    contDiffOn_fixedTractionStrain hL hf
  have hEq : ∀ x ∈ Set.Icc (0 : ℝ) L,
      derivWithin (fixedTractionDisplacement k L P f) (Set.Icc 0 L) x =
        fixedTractionStrain k L P f x := by
    intro x hx
    exact (hasDerivWithinAt_fixedTractionDisplacement hL hf x hx).derivWithin
      (hU.uniqueDiffWithinAt hx)
  have hC1 : ContDiffOn ℝ 1
      (derivWithin (fixedTractionDisplacement k L P f) (Set.Icc 0 L)) (Set.Icc 0 L) :=
    hstr1.congr hEq
  have hdiff : DifferentiableOn ℝ (fixedTractionDisplacement k L P f) (Set.Icc 0 L) := by
    intro x hx
    exact (hasDerivWithinAt_fixedTractionDisplacement hL hf x hx).differentiableWithinAt
  change ContDiffOn ℝ (1 + 1) (fixedTractionDisplacement k L P f) (Set.Icc 0 L)
  rw [contDiffOn_succ_iff_derivWithin hU]
  exact ⟨hdiff, by simp, hC1⟩

/-- The constructed displacement has derivative `fixedTractionStrain` within `[0, L]`. -/
lemma derivWithin_fixedTractionDisplacement {k L P : ℝ} {f : ℝ → ℝ} (hL : 0 < L)
    (hf : ContinuousOn f (Set.Icc 0 L)) :
    ∀ x ∈ Set.Icc (0 : ℝ) L, derivWithin (fixedTractionDisplacement k L P f) (Set.Icc 0 L) x =
      fixedTractionStrain k L P f x := by
  intro x hx
  have hU : UniqueDiffOn ℝ (Set.Icc 0 L) := uniqueDiffOn_Icc hL
  have hU' : UniqueDiffWithinAt ℝ (Set.Icc 0 L) x := hU.uniqueDiffWithinAt hx
  exact (hasDerivWithinAt_fixedTractionDisplacement hL hf x hx).derivWithin hU'

/-- The strain decreases at the rate of the load: `(u')' = -f / k` within `[0, L]`. -/
lemma derivWithin_fixedTractionStrain {k L P : ℝ} {f : ℝ → ℝ} (hL : 0 < L)
    (hf : ContinuousOn f (Set.Icc 0 L)) :
    ∀ x ∈ Set.Icc (0 : ℝ) L, derivWithin (fixedTractionStrain k L P f) (Set.Icc 0 L) x =
      -f x / k := by
  intro x hx
  have hU : UniqueDiffOn ℝ (Set.Icc 0 L) := uniqueDiffOn_Icc hL
  have hU' : UniqueDiffWithinAt ℝ (Set.Icc 0 L) x := hU.uniqueDiffWithinAt hx
  exact (hasDerivWithinAt_fixedTractionStrain hf x hx).derivWithin hU'

/-- Existence: for a load continuous on `[0, L]` the constructed displacement solves the
fixed-traction problem. -/
lemma isFixedTractionSolution_fixedTractionDisplacement {k L P : ℝ} {f : ℝ → ℝ} (hL : 0 < L)
    (hk : k ≠ 0) (hf : ContinuousOn f (Set.Icc 0 L)) :
    IsFixedTractionSolution k L P f (fixedTractionDisplacement k L P f) := by
  have hC2 : ContDiffOn ℝ 2 (fixedTractionDisplacement k L P f) (Set.Icc 0 L) :=
    contDiffOn_two_fixedTractionDisplacement hL hf
  have hDu : ∀ x ∈ Set.Icc (0 : ℝ) L,
      derivWithin (fixedTractionDisplacement k L P f) (Set.Icc 0 L) x =
        fixedTractionStrain k L P f x :=
    derivWithin_fixedTractionDisplacement hL hf
  have hDs : ∀ x ∈ Set.Icc (0 : ℝ) L,
      derivWithin (fixedTractionStrain k L P f) (Set.Icc 0 L) x = -f x / k :=
    derivWithin_fixedTractionStrain hL hf
  have h2 : ∀ x ∈ Set.Icc (0 : ℝ) L,
      iteratedDerivWithin 2 (fixedTractionDisplacement k L P f) (Set.Icc 0 L) x =
        -f x / k := by
    intro x hx
    have hiter : iteratedDerivWithin 2 (fixedTractionDisplacement k L P f) (Set.Icc 0 L) x =
        derivWithin (derivWithin (fixedTractionDisplacement k L P f) (Set.Icc 0 L))
          (Set.Icc 0 L) x := by
      have h1 : iteratedDerivWithin (1 + 1) (fixedTractionDisplacement k L P f)
          (Set.Icc 0 L) x =
          derivWithin (derivWithin (fixedTractionDisplacement k L P f) (Set.Icc 0 L))
            (Set.Icc 0 L) x := by
        have hs := congrFun (iteratedDerivWithin_succ (n:=1)
          (f:=fixedTractionDisplacement k L P f) (s:=Set.Icc 0 L)) x
        have ho : iteratedDerivWithin 1 (fixedTractionDisplacement k L P f) (Set.Icc 0 L) =
            derivWithin (fixedTractionDisplacement k L P f) (Set.Icc 0 L) :=
          iteratedDerivWithin_one
        rw [ho] at hs
        exact hs
      exact h1
    rw [hiter]
    have hcongr : derivWithin (derivWithin (fixedTractionDisplacement k L P f) (Set.Icc 0 L))
        (Set.Icc 0 L) x =
        derivWithin (fixedTractionStrain k L P f) (Set.Icc 0 L) x :=
      derivWithin_congr hDu (hDu x hx)
    rw [hcongr]
    exact hDs x hx
  refine ⟨hC2, ?_, ?_, ?_⟩
  · intro x hx
    have hx2 := h2 x hx
    rw [hx2]
    field_simp
  · change (∫ y in (0 : ℝ)..(0 : ℝ), fixedTractionStrain k L P f y) = 0
    exact intervalIntegral.integral_same
  · have hLmem : L ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt hL, le_rfl⟩
    have hDL := hDu L hLmem
    rw [hDL]
    change k * ((P + ∫ y in L..L, f y) / k) = P
    rw [intervalIntegral.integral_same]
    field_simp
    ring

/-- The load of a fixed-traction solution is continuous on `[0, L]`, being `-(k * u'')`. -/
private lemma continuousOn_f_of_fixedTraction {k L P : ℝ} {f u : ℝ → ℝ} (hL : 0 < L)
    (hu : IsFixedTractionSolution k L P f u) : ContinuousOn f (Set.Icc 0 L) := by
  have hU : UniqueDiffOn ℝ (Set.Icc 0 L) := uniqueDiffOn_Icc hL
  obtain ⟨huC, heq, _hu0, _hend⟩ := hu
  have hiter : ContinuousOn (iteratedDerivWithin 2 u (Set.Icc 0 L)) (Set.Icc 0 L) :=
    huC.continuousOn_iteratedDerivWithin le_rfl hU
  have hkmul : ContinuousOn (fun x => k * iteratedDerivWithin 2 u (Set.Icc 0 L) x)
      (Set.Icc 0 L) :=
    hiter.const_mul k
  have hneg : ContinuousOn (fun x => -(k * iteratedDerivWithin 2 u (Set.Icc 0 L) x))
      (Set.Icc 0 L) :=
    hkmul.neg
  have hEq : ∀ x ∈ Set.Icc (0 : ℝ) L,
      f x = -(k * iteratedDerivWithin 2 u (Set.Icc 0 L) x) := by
    intro x hx
    exact (heq x hx).symm
  exact hneg.congr hEq

/-- Inside `(0, L)`, a function that is `C²` on `[0, L]` has its derivative within `[0, L]` as
its derivative. -/
private lemma hasDerivAt_of_contDiffOn_two {L : ℝ} {u : ℝ → ℝ}
    (huC : ContDiffOn ℝ 2 u (Set.Icc 0 L)) {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) L) :
    HasDerivAt u (derivWithin u (Set.Icc 0 L) y) y := by
  have hy_mem : y ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hdiff : DifferentiableOn ℝ u (Set.Icc 0 L) := huC.differentiableOn (by simp)
  have hwithin := (hdiff y hy_mem).hasDerivWithinAt
  exact hwithin.hasDerivAt (Icc_mem_nhds hy.1 hy.2)

/-- Inside `(0, L)`, the derivative within `[0, L]` of a function that is `C²` on `[0, L]` has
the second derivative within `[0, L]` as its derivative. -/
private lemma hasDerivAt_second_of_contDiffOn_two {L : ℝ} {u : ℝ → ℝ} (hL : 0 < L)
    (huC : ContDiffOn ℝ 2 u (Set.Icc 0 L)) {y : ℝ} (hy : y ∈ Set.Ioo (0 : ℝ) L) :
    HasDerivAt (derivWithin u (Set.Icc 0 L))
      (iteratedDerivWithin 2 u (Set.Icc 0 L) y) y := by
  have hU : UniqueDiffOn ℝ (Set.Icc 0 L) := uniqueDiffOn_Icc hL
  have hC1 : ContDiffOn ℝ 1 (derivWithin u (Set.Icc 0 L)) (Set.Icc 0 L) :=
    huC.derivWithin hU le_rfl
  have hy_mem : y ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hdiff : DifferentiableOn ℝ (derivWithin u (Set.Icc 0 L)) (Set.Icc 0 L) :=
    hC1.differentiableOn (by simp)
  have hwithin := (hdiff y hy_mem).hasDerivWithinAt
  have hat := hwithin.hasDerivAt (Icc_mem_nhds hy.1 hy.2)
  have hiter : derivWithin (derivWithin u (Set.Icc 0 L)) (Set.Icc 0 L) y =
      iteratedDerivWithin 2 u (Set.Icc 0 L) y := by
    have h1 : derivWithin (derivWithin u (Set.Icc 0 L)) (Set.Icc 0 L) y =
        iteratedDerivWithin (1 + 1) u (Set.Icc 0 L) y := by
      have hs := congrFun (iteratedDerivWithin_succ (n:=1) (f:=u) (s:=Set.Icc 0 L)) y
      have ho : iteratedDerivWithin 1 u (Set.Icc 0 L) = derivWithin u (Set.Icc 0 L) :=
        iteratedDerivWithin_one
      rw [ho] at hs
      exact hs.symm
    exact h1
  rw [hiter] at hat
  exact hat

/-- Load path: in every solution the internal axial force at `x` is the end force plus the load
carried between `x` and `L`, `k * u' x = P + ∫ y in x..L, f y`. -/
lemma IsFixedTractionSolution.axialForce_eq {k L P : ℝ} {f u : ℝ → ℝ}
    (hu : IsFixedTractionSolution k L P f u) :
    ∀ x ∈ Set.Icc (0 : ℝ) L, k * derivWithin u (Set.Icc 0 L) x = P + ∫ y in x..L, f y := by
  by_cases hLpos : 0 < L
  · have hU : UniqueDiffOn ℝ (Set.Icc 0 L) := uniqueDiffOn_Icc hLpos
    have hf : ContinuousOn f (Set.Icc 0 L) :=
      continuousOn_f_of_fixedTraction hLpos hu
    obtain ⟨huC, heq, _hu0, hend⟩ := hu
    have hC1 : ContDiffOn ℝ 1 (derivWithin u (Set.Icc 0 L)) (Set.Icc 0 L) :=
      huC.derivWithin hU le_rfl
    have hDu_cont : ContinuousOn (derivWithin u (Set.Icc 0 L)) (Set.Icc 0 L) :=
      hC1.continuousOn
    have hg_cont_full : ContinuousOn (fun y => k * derivWithin u (Set.Icc 0 L) y)
        (Set.Icc 0 L) :=
      hDu_cont.const_mul k
    have hneg_cont_full : ContinuousOn (fun y => -f y) (Set.Icc 0 L) := hf.neg
    intro x hx
    have hxL : x ≤ L := hx.2
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hsub : Set.Icc x L ⊆ Set.Icc (0 : ℝ) L := Set.Icc_subset_Icc_left hx0
    have hg_cont : ContinuousOn (fun y => k * derivWithin u (Set.Icc 0 L) y)
        (Set.Icc x L) :=
      hg_cont_full.mono hsub
    have hderiv : ∀ y ∈ Set.Ioo x L,
        HasDerivAt (fun y => k * derivWithin u (Set.Icc 0 L) y) (-f y) y := by
      intro y hy
      have hy0 : (0 : ℝ) < y := lt_of_le_of_lt hx0 hy.1
      have hyL : y < L := hy.2
      have hyIoo : y ∈ Set.Ioo (0 : ℝ) L := ⟨hy0, hyL⟩
      have hy_mem : y ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt hy0, le_of_lt hyL⟩
      have h2nd := hasDerivAt_second_of_contDiffOn_two hLpos huC hyIoo
      have hkmul := HasDerivAt.const_mul k h2nd
      have heqy := heq y hy_mem
      have hval : k * iteratedDerivWithin 2 u (Set.Icc 0 L) y = -f y := by linarith
      rw [hval] at hkmul
      exact hkmul
    have hneg_cont : ContinuousOn (fun y => -f y) (Set.Icc x L) :=
      hneg_cont_full.mono hsub
    have hint := ContinuousOn.intervalIntegrable_of_Icc (μ:=MeasureTheory.volume) hxL
      hneg_cont
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxL hg_cont hderiv hint
    have hneg_eq : (∫ y in x..L, -f y) = -(∫ y in x..L, f y) :=
      intervalIntegral.integral_neg
    rw [hneg_eq] at hFTC
    rw [hend] at hFTC
    linarith
  · have hLle : L ≤ 0 := le_of_not_gt hLpos
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hxL : x ≤ L := hx.2
    have h0L : (0 : ℝ) ≤ L := hx0.trans hxL
    have hL0 : L = 0 := le_antisymm hLle h0L
    have hxL0 : x ≤ 0 := by rw [hL0] at hxL; exact hxL
    have hx0' : x = 0 := le_antisymm hxL0 hx0
    subst hL0
    subst hx0'
    have hend : k * derivWithin u (Set.Icc 0 0) 0 = P := hu.2.2.2
    rw [intervalIntegral.integral_same]
    simpa using hend

/-- Every solution equals the constructed displacement on `[0, L]`. -/
lemma IsFixedTractionSolution.eqOn_fixedTractionDisplacement {k L P : ℝ} {f u : ℝ → ℝ}
    (hk : k ≠ 0) (hu : IsFixedTractionSolution k L P f u) :
    Set.EqOn u (fixedTractionDisplacement k L P f) (Set.Icc 0 L) := by
  by_cases hLpos : 0 < L
  · have hf : ContinuousOn f (Set.Icc 0 L) :=
      continuousOn_f_of_fixedTraction hLpos hu
    have haxial := hu.axialForce_eq
    obtain ⟨huC, _heq, hu0, _hend⟩ := hu
    have hconstr : IsFixedTractionSolution k L P f (fixedTractionDisplacement k L P f) :=
      isFixedTractionSolution_fixedTractionDisplacement hLpos hk hf
    obtain ⟨hcC, _heqC, hc0, _hendC⟩ := hconstr
    have hderiv_eq : ∀ x ∈ Set.Icc (0 : ℝ) L,
        derivWithin u (Set.Icc 0 L) x = fixedTractionStrain k L P f x := by
      intro x hx
      have hax := haxial x hx
      have hstr : k * fixedTractionStrain k L P f x = P + ∫ y in x..L, f y := by
        change k * ((P + ∫ y in x..L, f y) / k) = P + ∫ y in x..L, f y
        field_simp
      have hkk : k * derivWithin u (Set.Icc 0 L) x =
          k * fixedTractionStrain k L P f x := by
        rw [hax, hstr]
      exact mul_left_cancel₀ hk hkk
    intro x hx
    have hxL : x ≤ L := hx.2
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hsub_full : Set.Icc (0 : ℝ) x ⊆ Set.Icc 0 L := Set.Icc_subset_Icc_right hxL
    have hu_cont : ContinuousOn u (Set.Icc (0 : ℝ) x) := huC.continuousOn.mono hsub_full
    have hu_deriv : ∀ y ∈ Set.Ioo (0 : ℝ) x,
        HasDerivAt u (derivWithin u (Set.Icc 0 L) y) y := by
      intro y hy
      have hyL : y < L := lt_of_lt_of_le hy.2 hxL
      exact hasDerivAt_of_contDiffOn_two huC ⟨hy.1, hyL⟩
    have hC1u : ContDiffOn ℝ 1 (derivWithin u (Set.Icc 0 L)) (Set.Icc 0 L) :=
      huC.derivWithin (uniqueDiffOn_Icc hLpos) le_rfl
    have hu'_cont : ContinuousOn (derivWithin u (Set.Icc 0 L)) (Set.Icc (0 : ℝ) x) :=
      hC1u.continuousOn.mono hsub_full
    have hu'_int := ContinuousOn.intervalIntegrable_of_Icc (μ:=MeasureTheory.volume) hx0
      hu'_cont
    have huFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0 hu_cont hu_deriv
      hu'_int
    have hc_cont : ContinuousOn (fixedTractionDisplacement k L P f) (Set.Icc (0 : ℝ) x) :=
      hcC.continuousOn.mono hsub_full
    have hc_deriv : ∀ y ∈ Set.Ioo (0 : ℝ) x,
        HasDerivAt (fixedTractionDisplacement k L P f)
          (fixedTractionStrain k L P f y) y := by
      intro y hy
      have hyL : y < L := lt_of_lt_of_le hy.2 hxL
      have hy_mem : y ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt hy.1, le_of_lt hyL⟩
      have hat := hasDerivAt_of_contDiffOn_two hcC ⟨hy.1, hyL⟩
      have hdy : derivWithin (fixedTractionDisplacement k L P f) (Set.Icc 0 L) y =
          fixedTractionStrain k L P f y :=
        derivWithin_fixedTractionDisplacement hLpos hf y hy_mem
      rw [hdy] at hat
      exact hat
    have hstr_cont : ContinuousOn (fixedTractionStrain k L P f) (Set.Icc (0 : ℝ) x) :=
      (continuousOn_fixedTractionStrain hLpos hf).mono hsub_full
    have hstr_int := ContinuousOn.intervalIntegrable_of_Icc (μ:=MeasureTheory.volume) hx0
      hstr_cont
    have hcFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0 hc_cont hc_deriv
      hstr_int
    have hint_eq : (∫ y in (0 : ℝ)..x, derivWithin u (Set.Icc 0 L) y) =
        (∫ y in (0 : ℝ)..x, fixedTractionStrain k L P f y) := by
      apply intervalIntegral.integral_congr
      have huIcc : Set.uIcc (0 : ℝ) x = Set.Icc 0 x := Set.uIcc_of_le hx0
      rw [huIcc]
      intro y hy
      exact hderiv_eq y (hsub_full hy)
    rw [hu0] at huFTC
    rw [hc0] at hcFTC
    linarith
  · have hLle : L ≤ 0 := le_of_not_gt hLpos
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hxL : x ≤ L := hx.2
    have h0L : (0 : ℝ) ≤ L := hx0.trans hxL
    have hL0 : L = 0 := le_antisymm hLle h0L
    have hxL0 : x ≤ 0 := by rw [hL0] at hxL; exact hxL
    have hx0' : x = 0 := le_antisymm hxL0 hx0
    subst hL0
    subst hx0'
    have hu0 : u 0 = 0 := hu.2.2.1
    have hc0 : fixedTractionDisplacement k 0 P f 0 = 0 := by
      change (∫ y in (0 : ℝ)..(0 : ℝ), fixedTractionStrain k 0 P f y) = 0
      exact intervalIntegral.integral_same
    rw [hu0, hc0]

/-- Uniqueness: two solutions agree on `[0, L]`. -/
lemma IsFixedTractionSolution.eqOn {k L P : ℝ} {f u v : ℝ → ℝ} (hk : k ≠ 0)
    (hu : IsFixedTractionSolution k L P f u) (hv : IsFixedTractionSolution k L P f v) :
    Set.EqOn u v (Set.Icc 0 L) := by
  have huE := IsFixedTractionSolution.eqOn_fixedTractionDisplacement hk hu
  have hvE := IsFixedTractionSolution.eqOn_fixedTractionDisplacement hk hv
  intro x hx
  have hux : u x = fixedTractionDisplacement k L P f x := huE hx
  have hvx : v x = fixedTractionDisplacement k L P f x := hvE hx
  rw [hux, hvx]

/-- Torsional port: a circular shaft fixed at `x = 0`, with distributed torque `t` and end torque
`T` at `x = L`, is the same problem with `k = GJ`. Its twist equals
`fixedTractionDisplacement GJ L T t` on `[0, L]` and its internal torque is
`GJ * φ' x = T + ∫ y in x..L, t y`, by the bar lemmas; no second solver is used. -/
lemma IsFixedTractionSolution.twist {GJ L T : ℝ} {t φ : ℝ → ℝ} (hGJ : 0 < GJ)
    (hφ : IsFixedTractionSolution GJ L T t φ) :
    Set.EqOn φ (fixedTractionDisplacement GJ L T t) (Set.Icc 0 L) ∧
      ∀ x ∈ Set.Icc (0 : ℝ) L, GJ * derivWithin φ (Set.Icc 0 L) x = T + ∫ y in x..L, t y := by
  have hk : GJ ≠ 0 := ne_of_gt hGJ
  constructor
  · exact IsFixedTractionSolution.eqOn_fixedTractionDisplacement hk hφ
  · exact IsFixedTractionSolution.axialForce_eq hφ

/-! ## H. Fixed-traction bar: uniform load -/

/-- Uniform load `q`: the constructed displacement is the end-force term `P * x / k` plus the
fixed-free displacement. -/
lemma fixedTractionDisplacement_const (k L P q x : ℝ) :
    fixedTractionDisplacement k L P (fun _ => q) x = P * x / k + fixedFreeDisplacement k L q x := by
  have hstrain : ∀ y : ℝ, fixedTractionStrain k L P (fun _ => q) y =
      (P + (L - y) * q) / k := by
    intro y
    change (P + ∫ z in y..L, (fun _ => q) z) / k = _
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hint_eq : (∫ y in (0 : ℝ)..x, fixedTractionStrain k L P (fun _ => q) y) =
      (∫ y in (0 : ℝ)..x, (P + (L - y) * q) / k) := by
    apply intervalIntegral.integral_congr
    intro y _
    exact hstrain y
  have hcont_aff : Continuous (fun y : ℝ => (P + (L - y) * q) / k) := by fun_prop
  have hint_aff := hcont_aff.intervalIntegrable (μ:=MeasureTheory.volume) 0 x
  have hderiv_G : ∀ y ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun y : ℝ => ((P + q * L) * y - q * (y * y) / 2) / k)
        ((P + (L - y) * q) / k) y := by
    intro y _
    have h_id : HasDerivAt (fun y : ℝ => y) (1 : ℝ) y := hasDerivAt_id y
    have h_yy : HasDerivAt (fun y : ℝ => y * y) (1 * y + y * 1) y := h_id.mul h_id
    have h_qyy : HasDerivAt (fun y : ℝ => q * (y * y)) (q * (1 * y + y * 1)) y :=
      HasDerivAt.const_mul q h_yy
    have h_qyy2 : HasDerivAt (fun y : ℝ => q * (y * y) / 2) (q * (1 * y + y * 1) / 2) y :=
      HasDerivAt.div_const h_qyy 2
    have h_Ay : HasDerivAt (fun y : ℝ => (P + q * L) * y) ((P + q * L) * 1) y :=
      HasDerivAt.const_mul (P + q * L) h_id
    have h_sub : HasDerivAt (fun y : ℝ => (P + q * L) * y - q * (y * y) / 2)
        ((P + q * L) * 1 - q * (1 * y + y * 1) / 2) y :=
      h_Ay.sub h_qyy2
    have h_G : HasDerivAt (fun y : ℝ => ((P + q * L) * y - q * (y * y) / 2) / k)
        (((P + q * L) * 1 - q * (1 * y + y * 1) / 2) / k) y :=
      HasDerivAt.div_const h_sub k
    have hval : (((P + q * L) * 1 - q * (1 * y + y * 1) / 2) / k) =
        ((P + (L - y) * q) / k) := by ring
    rw [hval] at h_G
    exact h_G
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_G hint_aff
  have hLHS : fixedTractionDisplacement k L P (fun _ => q) x =
      ∫ y in (0 : ℝ)..x, fixedTractionStrain k L P (fun _ => q) y := rfl
  rw [hLHS, hint_eq, hFTC]
  change ((P + q * L) * x - q * (x * x) / 2) / k -
      (((P + q * L) * 0 - q * (0 * 0) / 2) / k) =
      P * x / k + q * x * (2 * L - x) / (2 * k)
  ring

/-! ## I. Boundary example: two free ends -/

/-- Free-free problem on `[0, L]`: end force `P₀` at `x = 0`, where the outward normal is `-x` so
the end force is `-(k * u' 0)`, and end force `P₁ = k * u' L` at `x = L`. -/
def IsFreeFreeSolution (k L P₀ P₁ : ℝ) (f u : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 u (Set.Icc 0 L) ∧
    (∀ x ∈ Set.Icc (0 : ℝ) L, -(k * iteratedDerivWithin 2 u (Set.Icc 0 L) x) = f x) ∧
    -(k * derivWithin u (Set.Icc 0 L) 0) = P₀ ∧ k * derivWithin u (Set.Icc 0 L) L = P₁

/-- Two free ends admit a rigid translation: a free-free solution shifted by any constant `c` is
again a solution. -/
lemma IsFreeFreeSolution.add_const {k L P₀ P₁ : ℝ} {f u : ℝ → ℝ}
    (hu : IsFreeFreeSolution k L P₀ P₁ f u) (c : ℝ) :
    IsFreeFreeSolution k L P₀ P₁ f (fun x => u x + c) := by
  obtain ⟨huC, heq, h0, hL⟩ := hu
  have hC : ContDiffOn ℝ 2 (fun x => u x + c) (Set.Icc 0 L) :=
    huC.add contDiffOn_const
  refine ⟨hC, ?_, ?_, ?_⟩
  · intro x hx
    have hiter : iteratedDerivWithin 2 (fun x => u x + c) (Set.Icc 0 L) x =
        iteratedDerivWithin 2 u (Set.Icc 0 L) x := by
      have hfun : (fun x : ℝ => u x + c) = (fun x : ℝ => c + u x) := by
        ext y
        exact add_comm _ _
      rw [hfun]
      exact iteratedDerivWithin_const_add (by norm_num : 0 < 2) c
    rw [hiter]
    exact heq x hx
  · have hd0 : derivWithin (fun x => u x + c) (Set.Icc 0 L) 0 =
        derivWithin u (Set.Icc 0 L) 0 :=
      derivWithin_add_const c
    rw [hd0]
    exact h0
  · have hdL : derivWithin (fun x => u x + c) (Set.Icc 0 L) L =
        derivWithin u (Set.Icc 0 L) L :=
      derivWithin_add_const c
    rw [hdL]
    exact hL

/-- The load of a free-free solution is continuous on `[0, L]`, being `-(k * u'')`. -/
private lemma continuousOn_f_of_freeFree {k L P₀ P₁ : ℝ} {f u : ℝ → ℝ} (hL : 0 < L)
    (hu : IsFreeFreeSolution k L P₀ P₁ f u) : ContinuousOn f (Set.Icc 0 L) := by
  have hU : UniqueDiffOn ℝ (Set.Icc 0 L) := uniqueDiffOn_Icc hL
  obtain ⟨huC, heq, _h0, _hL⟩ := hu
  have hiter : ContinuousOn (iteratedDerivWithin 2 u (Set.Icc 0 L)) (Set.Icc 0 L) :=
    huC.continuousOn_iteratedDerivWithin le_rfl hU
  have hkmul : ContinuousOn (fun x => k * iteratedDerivWithin 2 u (Set.Icc 0 L) x)
      (Set.Icc 0 L) :=
    hiter.const_mul k
  have hneg : ContinuousOn (fun x => -(k * iteratedDerivWithin 2 u (Set.Icc 0 L) x))
      (Set.Icc 0 L) :=
    hkmul.neg
  have hEq : ∀ x ∈ Set.Icc (0 : ℝ) L,
      f x = -(k * iteratedDerivWithin 2 u (Set.Icc 0 L) x) := by
    intro x hx
    exact (heq x hx).symm
  exact hneg.congr hEq

/-- Equilibrium of a free-free bar requires zero net load: `P₀ + P₁ + ∫₀ᴸ f = 0`. -/
lemma IsFreeFreeSolution.net_load {k L P₀ P₁ : ℝ} {f u : ℝ → ℝ} (hL : 0 < L)
    (hu : IsFreeFreeSolution k L P₀ P₁ f u) : P₀ + P₁ + ∫ x in (0 : ℝ)..L, f x = 0 := by
  have hU : UniqueDiffOn ℝ (Set.Icc 0 L) := uniqueDiffOn_Icc hL
  have hf : ContinuousOn f (Set.Icc 0 L) := continuousOn_f_of_freeFree hL hu
  obtain ⟨huC, heq, h0, hLend⟩ := hu
  have hC1 : ContDiffOn ℝ 1 (derivWithin u (Set.Icc 0 L)) (Set.Icc 0 L) :=
    huC.derivWithin hU le_rfl
  have hg_cont : ContinuousOn (fun y => k * derivWithin u (Set.Icc 0 L) y)
      (Set.Icc 0 L) :=
    hC1.continuousOn.const_mul k
  have hderiv : ∀ y ∈ Set.Ioo (0 : ℝ) L,
      HasDerivAt (fun y => k * derivWithin u (Set.Icc 0 L) y) (-f y) y := by
    intro y hy
    have hy_mem : y ∈ Set.Icc (0 : ℝ) L := ⟨le_of_lt hy.1, le_of_lt hy.2⟩
    have h2nd := hasDerivAt_second_of_contDiffOn_two hL huC hy
    have hkmul := HasDerivAt.const_mul k h2nd
    have heqy := heq y hy_mem
    have hval : k * iteratedDerivWithin 2 u (Set.Icc 0 L) y = -f y := by linarith
    rw [hval] at hkmul
    exact hkmul
  have hneg_cont : ContinuousOn (fun y => -f y) (Set.Icc 0 L) := hf.neg
  have hint := ContinuousOn.intervalIntegrable_of_Icc (μ:=MeasureTheory.volume)
    (le_of_lt hL) hneg_cont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hL) hg_cont
    hderiv hint
  have hneg_eq : (∫ x in (0 : ℝ)..L, -f x) = -(∫ x in (0 : ℝ)..L, f x) :=
    intervalIntegral.integral_neg
  rw [hneg_eq] at hFTC
  have hk0 : k * derivWithin u (Set.Icc 0 L) 0 = -P₀ := by linarith
  rw [hLend, hk0] at hFTC
  linarith

section ClosedCell

open Mechanics.EngineeringStatics (momentAbout)
open PhyslibExt.Mechanics.HarmonicMechanics (resultantForce)

/-! ## J. Thin closed rectangular cell: wall resultants and torque -/

/-- Midpoints of the four walls of the median rectangle `[-a/2, a/2] × [-b/2, b/2]` in the section
plane `z = 0`, in counterclockwise order about `+z`: bottom, right, top, left. -/
noncomputable def cellWallMidpoint (a b : ℝ) : Fin 4 → Fin 3 → ℝ :=
  ![![0, -(b / 2), 0], ![a / 2, 0, 0], ![0, b / 2, 0], ![-(a / 2), 0, 0]]

/-- Resultants of the uniform shear flow `q` on the four walls, in the order of
`cellWallMidpoint`: on each straight wall the flow integrates to `q` times the wall length (`a` for
the bottom and top walls, `b` for the right and left walls), directed along the wall in the
counterclockwise sense about `+z` for `q > 0`, with line of action through the wall midpoint. -/
noncomputable def cellWallForce (a b q : ℝ) : Fin 4 → Fin 3 → ℝ :=
  ![![q * a, 0, 0], ![0, q * b, 0], ![-(q * a), 0, 0], ![0, -(q * b), 0]]

/-- Lengths of the four walls along the median line, in the order of `cellWallMidpoint`. -/
def cellWallLength (a b : ℝ) : Fin 4 → ℝ :=
  ![a, b, a, b]

/-- **The closed cell is self-equilibrated.** The four wall resultants sum to zero. -/
lemma resultantForce_cellWallForce (a b q : ℝ) : resultantForce (cellWallForce a b q) = 0 := by
  unfold resultantForce cellWallForce
  rw [Fin.sum_univ_four]
  ext i
  fin_cases i <;> simp

/-- **Torque from the four wall resultants.** About every reference point `O`, the wall resultants
(no free couples) have the moment `(0, 0, 2 a b q)`: the cell carries the torque
`T = 2 a b q = 2 A q` about the member axis `+z`, positive for counterclockwise shear flow. -/
lemma momentAbout_cellWall (a b q : ℝ) (O : Fin 3 → ℝ) :
    momentAbout (cellWallMidpoint a b) (cellWallForce a b q) (fun _ => 0) O =
      ![0, 0, 2 * a * b * q] := by
  unfold momentAbout cellWallMidpoint cellWallForce
  rw [Fin.sum_univ_four]
  simp only [add_zero, Pi.sub_apply, cross_apply]
  ext i
  fin_cases i <;> simp; ring

/-! ## K. Thin closed rectangular cell: compatibility, shear stress and rigidity -/

/-- The stated thin-wall compatibility law of a single closed cell (the declared reduced model):
the circulation of the wall shear strain `q / (G t)` around the median line,
`∑ walls (q / (G t)) ℓ`, equals twice the enclosed area `a b` times the twist rate `θ'`. -/
def IsClosedCellCompatible (a b t G q θ' : ℝ) : Prop :=
  ∑ i, q / (G * t) * cellWallLength a b i = 2 * (a * b) * θ'

/-- Wall shear stress `τ = q / t` of the shear flow `q` in a wall of thickness `t`. -/
noncomputable def wallShearStress (q t : ℝ) : ℝ :=
  q / t

/-- Torsion constant of the thin closed rectangular cell, `J = 4 A² t / S` with the enclosed area
`A = a b` and the median perimeter `S = 2 (a + b)`: `J = 2 a² b² t / (a + b)`. `G J` is the
effective torsional rigidity of the cell. -/
noncomputable def closedCellTorsionConstant (a b t : ℝ) : ℝ :=
  2 * a ^ 2 * b ^ 2 * t / (a + b)

/-- **Twist rate under the compatibility law.** For `a, b, t, G > 0` and the torque `T` of the
wall resultants about any reference point `O`, the compatibility law holds exactly when
`θ' = T (a + b) / (2 G a² b² t)`. -/
lemma isClosedCellCompatible_iff {a b t G q θ' T : ℝ} {O : Fin 3 → ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) (hG : 0 < G)
    (hT : T = momentAbout (cellWallMidpoint a b) (cellWallForce a b q) (fun _ => 0) O 2) :
    IsClosedCellCompatible a b t G q θ' ↔ θ' = T * (a + b) / (2 * G * a ^ 2 * b ^ 2 * t) := by
  have hT' : T = 2 * a * b * q := by
    rw [hT, momentAbout_cellWall]
    simp
  unfold IsClosedCellCompatible cellWallLength
  rw [Fin.sum_univ_four]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  rw [hT']
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have ht' : t ≠ 0 := ne_of_gt ht
  have hG' : G ≠ 0 := ne_of_gt hG
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  constructor
  · intro h
    field_simp at h ⊢
    linear_combination -h / 2
  · intro h
    field_simp at h ⊢
    linear_combination -2 * h

/-- **Shear stress.** For `a, b ≠ 0` and a wall thickness `t > 0` the wall shear stress is
`τ = q / t = T / (2 a b t)`, where `T` is the torque of the wall resultants. -/
lemma wallShearStress_eq {a b t q T : ℝ} {O : Fin 3 → ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (ht : 0 < t)
    (hT : T = momentAbout (cellWallMidpoint a b) (cellWallForce a b q) (fun _ => 0) O 2) :
    wallShearStress q t = T / (2 * a * b * t) := by
  have hT' : T = 2 * a * b * q := by
    rw [hT, momentAbout_cellWall]
    simp
  unfold wallShearStress
  rw [hT']
  have ht' : t ≠ 0 := ne_of_gt ht
  field_simp

/-- **The torsion constant is Bredt's.** For `a, b, t > 0`,
`J = 4 A² / ∑ walls (ℓ / t)` with `A = a b`, and `J > 0`. -/
lemma closedCellTorsionConstant_eq {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    closedCellTorsionConstant a b t = 4 * (a * b) ^ 2 / ∑ i, cellWallLength a b i / t ∧
      0 < closedCellTorsionConstant a b t := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have ht' : t ≠ 0 := ne_of_gt ht
  have hab : 0 < a + b := add_pos ha hb
  have hab' : a + b ≠ 0 := ne_of_gt hab
  unfold closedCellTorsionConstant cellWallLength
  rw [Fin.sum_univ_four]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  constructor
  · field_simp
    ring
  · positivity

/-- **Effective torsional rigidity.** For `a, b, t, G > 0`, under the compatibility law the torque
of the wall resultants is the effective rigidity times the twist rate: `T = G J θ'`. -/
lemma torque_eq_rigidity_mul_twistRate {a b t G q θ' T : ℝ} {O : Fin 3 → ℝ} (ha : 0 < a)
    (hb : 0 < b) (ht : 0 < t) (hG : 0 < G)
    (hT : T = momentAbout (cellWallMidpoint a b) (cellWallForce a b q) (fun _ => 0) O 2)
    (h : IsClosedCellCompatible a b t G q θ') :
    T = G * closedCellTorsionConstant a b t * θ' := by
  have hθ := (isClosedCellCompatible_iff ha hb ht hG hT).mp h
  unfold closedCellTorsionConstant
  rw [hθ]
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb' : b ≠ 0 := ne_of_gt hb
  have ht' : t ≠ 0 := ne_of_gt ht
  have hG' : G ≠ 0 := ne_of_gt hG
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  field_simp

end ClosedCell

/-! ## L. Simply supported beam: existence and uniqueness -/

open Mechanics.EulerBernoulli

/-- The simply supported problem on a beam of positive length `L`: `w` is `C⁴`, satisfies
`EI * w'''' = q` on `(0, L)`, and has zero deflection and zero curvature at both pins. The slopes
at the pins are not constrained. -/
structure IsSimplySupportedSolution (EI L q : ℝ) (w : ℝ → ℝ) : Prop where
  span_pos : 0 < L
  contDiff : ContDiff ℝ 4 w
  eq : ∀ x ∈ Set.Ioo (0 : ℝ) L, EI * iteratedDeriv 4 w x = q
  zero_left : w 0 = 0
  zero_right : w L = 0
  curvature_left : iteratedDeriv 2 w 0 = 0
  curvature_right : iteratedDeriv 2 w L = 0

/-- Normal form of the uniform-load quartic in powers of `x`. -/
private lemma uld_eq (q EI L : ℝ) : uniformLoadDeflection q EI L = fun x =>
    q / (24 * EI) * x ^ 4 + (-(2 * q * L) / (24 * EI)) * x ^ 3 + q * L ^ 3 / (24 * EI) * x ^ 1 := by
  funext x
  unfold uniformLoadDeflection
  ring

/-- The uniform-load quartic is `C⁴`. -/
private lemma uld_contDiff (q EI L : ℝ) : ContDiff ℝ 4 (uniformLoadDeflection q EI L) := by
  rw [uld_eq]
  fun_prop

/-- Iterated derivatives of the uniform-load quartic, term by term. -/
private lemma iteratedDeriv_uld (q EI L : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (uniformLoadDeflection q EI L) x =
      q / (24 * EI) * iteratedDeriv n (fun x : ℝ => x ^ 4) x +
      (-(2 * q * L) / (24 * EI)) * iteratedDeriv n (fun x : ℝ => x ^ 3) x +
      q * L ^ 3 / (24 * EI) * iteratedDeriv n (fun x : ℝ => x ^ 1) x := by
  rw [uld_eq]
  have h1 : ContDiffAt ℝ n (fun x : ℝ => q / (24 * EI) * x ^ 4 +
      (-(2 * q * L) / (24 * EI)) * x ^ 3) x := by fun_prop
  have h2 : ContDiffAt ℝ n (fun x : ℝ => q * L ^ 3 / (24 * EI) * x ^ 1) x := by fun_prop
  have h3 : ContDiffAt ℝ n (fun x : ℝ => q / (24 * EI) * x ^ 4) x := by fun_prop
  have h4 : ContDiffAt ℝ n (fun x : ℝ => (-(2 * q * L) / (24 * EI)) * x ^ 3) x := by fun_prop
  rw [iteratedDeriv_fun_add h1 h2, iteratedDeriv_fun_add h3 h4]
  simp only [iteratedDeriv_const_mul_field]

/-- Two `C⁴` functions that agree on `[0, L]`, `L > 0`, have the same derivatives up to order
four at every point of `[0, L]`, endpoints included. -/
private lemma iteratedDeriv_eq_of_eqOn {L : ℝ} (hL : 0 < L) {f g : ℝ → ℝ} (hf : ContDiff ℝ 4 f)
    (hg : ContDiff ℝ 4 g) (h : Set.EqOn f g (Set.Icc 0 L)) {k : ℕ} (hk : k ≤ 4) {y : ℝ}
    (hy : y ∈ Set.Icc 0 L) : iteratedDeriv k f y = iteratedDeriv k g y := by
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) L) := uniqueDiffOn_Icc hL
  rw [← iteratedDerivWithin_eq_iteratedDeriv hU ((hf.of_le (by exact_mod_cast hk)).contDiffAt) hy,
    ← iteratedDerivWithin_eq_iteratedDeriv hU ((hg.of_le (by exact_mod_cast hk)).contDiffAt) hy]
  exact iteratedDerivWithin_congr h hy

/-- Existence: for a positive span the uniform-load quartic solves the simply supported
problem. -/
lemma isSimplySupportedSolution_uniformLoadDeflection {EI L : ℝ} (hEI : 0 < EI) (hL : 0 < L)
    (q : ℝ) : IsSimplySupportedSolution EI L q (uniformLoadDeflection q EI L) := by
  exact ⟨hL, uld_contDiff q EI L,
    fun x _ => uniformLoadDeflection_ei_mul_iteratedDeriv_four q EI L hEI x,
    uniformLoadDeflection_zero_left q EI L, uniformLoadDeflection_zero_right q EI L,
    uniformLoadDeflection_secondDeriv_zero_left q EI L,
    uniformLoadDeflection_secondDeriv_zero_right q EI L⟩

/-- Uniqueness: every solution of the simply supported problem agrees with the uniform-load
quartic on `[0, L]`. -/
lemma IsSimplySupportedSolution.eqOn {EI L q : ℝ} {w : ℝ → ℝ} (hEI : 0 < EI)
    (hw : IsSimplySupportedSolution EI L q w) :
    Set.EqOn w (uniformLoadDeflection q EI L) (Set.Icc 0 L) := by
  set d := fun y => w y - uniformLoadDeflection q EI L y with hd_def
  have hdc : ContDiff ℝ 4 d := hw.contDiff.sub (uld_contDiff q EI L)
  have hsub : ∀ (k : ℕ) (y : ℝ), k ≤ 4 → iteratedDeriv k d y =
      iteratedDeriv k w y - iteratedDeriv k (uniformLoadDeflection q EI L) y := by
    intro k y hk
    have h1 : ContDiffAt ℝ k w y := (hw.contDiff.of_le (by exact_mod_cast hk)).contDiffAt
    have h2 : ContDiffAt ℝ k (uniformLoadDeflection q EI L) y :=
      ((uld_contDiff q EI L).of_le (by exact_mod_cast hk)).contDiffAt
    exact iteratedDeriv_fun_sub h1 h2
  have h4 : ∀ y ∈ Set.Ioo (0 : ℝ) L, iteratedDeriv 4 d y = 0 := by
    intro y hy
    rw [hsub 4 y le_rfl]
    have e1 := hw.eq y hy
    have e2 := uniformLoadDeflection_ei_mul_iteratedDeriv_four q EI L hEI y
    have : EI * (iteratedDeriv 4 w y - iteratedDeriv 4 (uniformLoadDeflection q EI L) y) = 0 := by
      rw [mul_sub, e1, e2, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hEI.ne'
  obtain ⟨c₀, c₁, c₂, c₃, hc⟩ := exists_cubic_of_iteratedDeriv_four_eq_zero hdc h4
  have hcub : ∀ k ≤ 3, ∀ y ∈ Set.Icc (0 : ℝ) L, iteratedDeriv k d y =
      iteratedDeriv k (fun x : ℝ => c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3) y :=
    fun k hk y hy => iteratedDeriv_eq_of_eqOn hw.span_pos hdc (by fun_prop) hc (by omega) hy
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_rfl, hw.span_pos.le⟩
  have hLm : L ∈ Set.Icc (0 : ℝ) L := ⟨hw.span_pos.le, le_rfl⟩
  have t0 : d 0 = 0 := by
    simp only [hd_def, hw.zero_left, uniformLoadDeflection_zero_left, sub_self]
  have tL : d L = 0 := by
    simp only [hd_def, hw.zero_right, uniformLoadDeflection_zero_right, sub_self]
  have t20 : iteratedDeriv 2 d 0 = 0 := by
    rw [hsub 2 0 (by norm_num), hw.curvature_left, uniformLoadDeflection_secondDeriv_zero_left,
      sub_self]
  have t2L : iteratedDeriv 2 d L = 0 := by
    rw [hsub 2 L (by norm_num), hw.curvature_right, uniformLoadDeflection_secondDeriv_zero_right,
      sub_self]
  obtain ⟨-, p2L, -⟩ := iteratedDeriv_cubic c₀ c₁ c₂ c₃ L
  obtain ⟨-, p20, -⟩ := iteratedDeriv_cubic c₀ c₁ c₂ c₃ 0
  have e2 : c₂ = 0 := by
    have := hcub 2 (by norm_num) 0 h0
    rw [t20, p20] at this
    linarith
  have e3 : c₃ = 0 := by
    have := hcub 2 (by norm_num) L hLm
    rw [t2L, p2L, e2] at this
    have h' : c₃ * L = 0 := by linarith
    exact (mul_eq_zero.mp h').resolve_right hw.span_pos.ne'
  have e0 : c₀ = 0 := by
    have := hc 0 h0
    rw [t0] at this
    linarith
  have e1 : c₁ = 0 := by
    have := hc L hLm
    rw [tL, e0, e2, e3] at this
    have h' : c₁ * L = 0 := by linarith
    exact (mul_eq_zero.mp h').resolve_right hw.span_pos.ne'
  intro x hx
  simpa [hd_def, e0, e1, e2, e3, sub_eq_zero] using hc x hx

/-- Characterization: for `EI > 0` and `L > 0` the solutions of the simply supported problem are
exactly the `C⁴` functions that agree with the uniform-load quartic on `[0, L]`. -/
lemma isSimplySupportedSolution_iff {EI L q : ℝ} {w : ℝ → ℝ} (hEI : 0 < EI) (hL : 0 < L) :
    IsSimplySupportedSolution EI L q w ↔
      ContDiff ℝ 4 w ∧ Set.EqOn w (uniformLoadDeflection q EI L) (Set.Icc 0 L) := by
  refine ⟨fun hw => ⟨hw.contDiff, hw.eqOn hEI⟩, fun ⟨hc, he⟩ => ?_⟩
  have key : ∀ k ≤ 4, ∀ y ∈ Set.Icc (0 : ℝ) L,
      iteratedDeriv k w y = iteratedDeriv k (uniformLoadDeflection q EI L) y :=
    fun k hk y hy => iteratedDeriv_eq_of_eqOn hL hc (uld_contDiff q EI L) he hk hy
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_rfl, hL.le⟩
  have hLm : L ∈ Set.Icc (0 : ℝ) L := ⟨hL.le, le_rfl⟩
  refine ⟨hL, hc, fun x hx => ?_, ?_, ?_, ?_, ?_⟩
  · rw [key 4 le_rfl x (Set.Ioo_subset_Icc_self hx)]
    exact uniformLoadDeflection_ei_mul_iteratedDeriv_four q EI L hEI x
  · rw [he h0]
    exact uniformLoadDeflection_zero_left q EI L
  · rw [he hLm]
    exact uniformLoadDeflection_zero_right q EI L
  · rw [key 2 (by norm_num) 0 h0]
    exact uniformLoadDeflection_secondDeriv_zero_left q EI L
  · rw [key 2 (by norm_num) L hLm]
    exact uniformLoadDeflection_secondDeriv_zero_right q EI L

/-! ## M. Simply supported beam: support reactions and slopes -/

/-- Support reactions: every solution has the reaction `-(EI * w''' 0) = q * L / 2` at the left
pin and `EI * w''' L = q * L / 2` at the right pin. -/
lemma IsSimplySupportedSolution.reactions {EI L q : ℝ} {w : ℝ → ℝ} (hEI : 0 < EI)
    (hw : IsSimplySupportedSolution EI L q w) :
    -(EI * iteratedDeriv 3 w 0) = q * L / 2 ∧ EI * iteratedDeriv 3 w L = q * L / 2 := by
  have heq := hw.eqOn hEI
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_rfl, hw.span_pos.le⟩
  have hLm : L ∈ Set.Icc (0 : ℝ) L := ⟨hw.span_pos.le, le_rfl⟩
  rw [iteratedDeriv_eq_of_eqOn hw.span_pos hw.contDiff (uld_contDiff q EI L) heq (by norm_num) h0,
    iteratedDeriv_eq_of_eqOn hw.span_pos hw.contDiff (uld_contDiff q EI L) heq (by norm_num) hLm,
    iteratedDeriv_uld, iteratedDeriv_uld]
  simp [iteratedDeriv_pow, iteratedDeriv_fun_id]
  have hEI' : EI ≠ 0 := hEI.ne'
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The pins do not constrain the slope: every solution has the slope `q * L ^ 3 / (24 * EI)` at
the left pin and `-(q * L ^ 3 / (24 * EI))` at the right pin. -/
lemma IsSimplySupportedSolution.slopes {EI L q : ℝ} {w : ℝ → ℝ} (hEI : 0 < EI)
    (hw : IsSimplySupportedSolution EI L q w) :
    deriv w 0 = q * L ^ 3 / (24 * EI) ∧ deriv w L = -(q * L ^ 3 / (24 * EI)) := by
  have heq := hw.eqOn hEI
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := ⟨le_rfl, hw.span_pos.le⟩
  have hLm : L ∈ Set.Icc (0 : ℝ) L := ⟨hw.span_pos.le, le_rfl⟩
  rw [← iteratedDeriv_one,
    iteratedDeriv_eq_of_eqOn hw.span_pos hw.contDiff (uld_contDiff q EI L) heq (by norm_num) h0,
    iteratedDeriv_eq_of_eqOn hw.span_pos hw.contDiff (uld_contDiff q EI L) heq (by norm_num) hLm,
    iteratedDeriv_uld, iteratedDeriv_uld]
  simp [iteratedDeriv_pow, iteratedDeriv_fun_id]
  ring

/-! ## N. Simply supported beam: clamped slopes change the solution -/

/-- Clamped-clamped deflection under the uniform load `q`: `q * x ^ 2 * (L - x) ^ 2 / (24 * EI)`.
-/
noncomputable def clampedClampedDeflection (EI L q x : ℝ) : ℝ :=
  q * x ^ 2 * (L - x) ^ 2 / (24 * EI)

/-- Normal form of the clamped-clamped polynomial in powers of `x`. -/
private lemma ccd_eq (EI L q : ℝ) : clampedClampedDeflection EI L q = fun x =>
    q / (24 * EI) * x ^ 4 + (-(2 * q * L) / (24 * EI)) * x ^ 3 + q * L ^ 2 / (24 * EI) * x ^ 2 := by
  funext x
  unfold clampedClampedDeflection
  ring

/-- Iterated derivatives of the clamped-clamped polynomial, term by term. -/
private lemma iteratedDeriv_ccd (EI L q : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (clampedClampedDeflection EI L q) x =
      q / (24 * EI) * iteratedDeriv n (fun x : ℝ => x ^ 4) x +
      (-(2 * q * L) / (24 * EI)) * iteratedDeriv n (fun x : ℝ => x ^ 3) x +
      q * L ^ 2 / (24 * EI) * iteratedDeriv n (fun x : ℝ => x ^ 2) x := by
  rw [ccd_eq]
  have h1 : ContDiffAt ℝ n (fun x : ℝ => q / (24 * EI) * x ^ 4 +
      (-(2 * q * L) / (24 * EI)) * x ^ 3) x := by fun_prop
  have h2 : ContDiffAt ℝ n (fun x : ℝ => q * L ^ 2 / (24 * EI) * x ^ 2) x := by fun_prop
  have h3 : ContDiffAt ℝ n (fun x : ℝ => q / (24 * EI) * x ^ 4) x := by fun_prop
  have h4 : ContDiffAt ℝ n (fun x : ℝ => (-(2 * q * L) / (24 * EI)) * x ^ 3) x := by fun_prop
  rw [iteratedDeriv_fun_add h1 h2, iteratedDeriv_fun_add h3 h4]
  simp only [iteratedDeriv_const_mul_field]

/-- Replacing the two moment conditions by clamped slopes changes the solution: for `q ≠ 0` the
clamped-clamped polynomial satisfies the equation, both deflection conditions and both clamped
slopes, but it is not a simply supported solution, and its midspan deflection
`q * L ^ 4 / (384 * EI)` differs from the simply supported one. -/
lemma clampedSlopes_change_solution {EI L q : ℝ} (hEI : 0 < EI) (hL : 0 < L) (hq : q ≠ 0) :
    (∀ x, EI * iteratedDeriv 4 (clampedClampedDeflection EI L q) x = q) ∧
      clampedClampedDeflection EI L q 0 = 0 ∧ clampedClampedDeflection EI L q L = 0 ∧
      deriv (clampedClampedDeflection EI L q) 0 = 0 ∧
      deriv (clampedClampedDeflection EI L q) L = 0 ∧
      ¬ IsSimplySupportedSolution EI L q (clampedClampedDeflection EI L q) ∧
      clampedClampedDeflection EI L q (L / 2) ≠ uniformLoadDeflection q EI L (L / 2) := by
  have hEI' : EI ≠ 0 := hEI.ne'
  have hL' : L ≠ 0 := hL.ne'
  refine ⟨fun x => ?_, ?_, ?_, ?_, ?_, fun h => ?_, ?_⟩
  · rw [iteratedDeriv_ccd]
    simp [iteratedDeriv_pow]
    field_simp
  · unfold clampedClampedDeflection
    ring
  · unfold clampedClampedDeflection
    ring
  · rw [← iteratedDeriv_one, iteratedDeriv_ccd]
    simp [iteratedDeriv_pow]
  · rw [← iteratedDeriv_one, iteratedDeriv_ccd]
    simp [iteratedDeriv_pow]
    ring
  · have h2 := h.curvature_left
    have hv : iteratedDeriv 2 (clampedClampedDeflection EI L q) 0 = q * L ^ 2 / (12 * EI) := by
      rw [iteratedDeriv_ccd]
      simp [iteratedDeriv_pow]
      ring
    rw [hv] at h2
    exact div_ne_zero (mul_ne_zero hq (pow_ne_zero 2 hL')) (mul_ne_zero (by norm_num) hEI') h2
  · unfold clampedClampedDeflection uniformLoadDeflection
    intro h
    field_simp at h
    have h4 : q * L ^ 4 = 0 := by nlinarith
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact hq h5
    · exact hL' (pow_eq_zero_iff (by norm_num) |>.mp h5)

end Elasticity.PrismaticMembers

end
