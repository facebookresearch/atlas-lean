/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Tactic.Ring

/-!
# Bounded continuous multiplication on L²

Let X be a topological space with its Borel measurable structure, μ any measure on X and
H=L²(X,μ;ℂ). For f∈C_b(X,ℂ), let M_f:H→H be multiplication by f, (M_f u)(x)=f(x)u(x) μ-almost
everywhere. The operators satisfy ‖M_f‖≤‖f‖∞ and form a unital complex star representation
C_b(X,ℂ)→B(H). On compact X, the same representation applies to C(X,ℂ). The construction uses
the L² space for the given measure, including zero measures and empty spaces.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace BoundedContinuousFunction

universe uX

variable {X : Type uX} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
variable (μ : Measure X)

/-- **L² multiplication operator of a bounded continuous function.**

Let X be a topological space with its Borel measurable structure, μ any measure on X and
H=L²(X,μ;ℂ). For f∈C_b(X,ℂ), let M_f:H→H be multiplication by f, (M_f u)(x)=f(x)u(x) μ-almost
everywhere. The bounded complex linear operator l2MultiplicationOperator μ f is M_f.
-/
def l2MultiplicationOperator (f : X →ᵇ ℂ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (ContinuousLinearMap.lsmul ℂ ℂ).holderL μ ∞ 2 2
    ((f.memLp_top (μ := μ)).toLp f)

/-- **Product of a bounded continuous function with an L² class.**

Let X be a topological space with its Borel measurable structure, μ any measure on X and
H=L²(X,μ;ℂ). For f∈C_b(X,ℂ), let M_f:H→H be multiplication by f, (M_f u)(x)=f(x)u(x) μ-almost
everywhere. For u∈H, mulOnL2 μ f u is the L² class of x↦f(x)u(x).
-/
def mulOnL2 (f : X →ᵇ ℂ) (u : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  l2MultiplicationOperator μ f u

/-- **Pointwise representative of bounded-function L² multiplication.**

Let X be a topological space with its Borel measurable structure, μ any measure on X and
H=L²(X,μ;ℂ). For f∈C_b(X,ℂ), let M_f:H→H be multiplication by f, (M_f u)(x)=f(x)u(x) μ-almost
everywhere. For f∈C_b(X,ℂ) and u∈H, mulOnL2 μ f u=f*u μ-almost everywhere.
-/
theorem mulOnL2_ae_eq (f : X →ᵇ ℂ) (u : Lp ℂ 2 μ) :
    mulOnL2 μ f u =ᵐ[μ] fun x => f x * u x := by
  have hop := (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder (r := 2)
    ((f.memLp_top (μ := μ)).toLp f) u
  have hf := (MemLp.coeFn_toLp (f.memLp_top (μ := μ)))
  filter_upwards [hop, hf] with x hx hfx
  change mulOnL2 μ f u x = f x * u x
  change mulOnL2 μ f u x = _ at hx
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, hfx] using hx

/-- **Linear map of bounded-function multiplication on L².**

Let X be a topological space with its Borel measurable structure, μ any measure on X and
H=L²(X,μ;ℂ). For f∈C_b(X,ℂ), let M_f:H→H be multiplication by f, (M_f u)(x)=f(x)u(x) μ-almost
everywhere. The complex linear map mulOnL2LinearMap μ f:H→H sends u to the class f*u.
-/
def mulOnL2LinearMap (f : X →ᵇ ℂ) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
  (l2MultiplicationOperator μ f).toLinearMap

/-- **L² norm bound for bounded-function multiplication.**

Let X be a topological space with its Borel measurable structure, μ any measure on X and
H=L²(X,μ;ℂ). For f∈C_b(X,ℂ), let M_f:H→H be multiplication by f, (M_f u)(x)=f(x)u(x) μ-almost
everywhere. For u∈H, ‖mulOnL2 μ f u‖L²≤‖f‖∞‖u‖L².
-/
theorem mulOnL2_norm_le (f : X →ᵇ ℂ) (u : Lp ℂ 2 μ) :
    ‖mulOnL2 μ f u‖ ≤ ‖f‖ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulOnL2_ae_eq μ f u] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (norm_nonneg (u x))

/-- **Almost-everywhere value of the bounded multiplication operator.**

Let X be a topological space with its Borel measurable structure, μ any measure on X and
H=L²(X,μ;ℂ). For f∈C_b(X,ℂ), let M_f:H→H be multiplication by f, (M_f u)(x)=f(x)u(x) μ-almost
everywhere. For f∈C_b(X,ℂ) and u∈H, l2MultiplicationOperator μ f u equals x↦f(x)u(x) μ-almost
everywhere.
-/
theorem l2MultiplicationOperator_ae_eq (f : X →ᵇ ℂ) (u : Lp ℂ 2 μ) :
    l2MultiplicationOperator μ f u =ᵐ[μ] fun x => f x * u x := mulOnL2_ae_eq μ f u

/-- **Operator norm bound for L² multiplication.**

Let X be a topological space with its Borel measurable structure, μ any measure on X and
H=L²(X,μ;ℂ). For f∈C_b(X,ℂ), let M_f:H→H be multiplication by f, (M_f u)(x)=f(x)u(x) μ-almost
everywhere. For f∈C_b(X,ℂ), ‖l2MultiplicationOperator μ f‖≤‖f‖∞.
-/
theorem norm_l2MultiplicationOperator_le (f : X →ᵇ ℂ) :
    ‖l2MultiplicationOperator μ f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f) (mulOnL2_norm_le μ f)

/-- **Star representation of bounded continuous functions on L².**

Let X be a topological space with its Borel measurable structure, μ any measure on X and
H=L²(X,μ;ℂ). For f∈C_b(X,ℂ), let M_f:H→H be multiplication by f, (M_f u)(x)=f(x)u(x) μ-almost
everywhere. The unital complex star homomorphism
BoundedContinuousFunction.l2MultiplicationRepresentation μ:C_b(X,ℂ)→B(H) sends f to M_f, with
M_(f*g)=M_f*M_g and M_star(f)=star(M_f).
-/
def l2MultiplicationRepresentation : (X →ᵇ ℂ) →⋆ₐ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  toFun := l2MultiplicationOperator μ
  map_one' := by
    apply ContinuousLinearMap.ext
    intro u
    change mulOnL2 μ 1 u = u
    apply Lp.ext
    filter_upwards [mulOnL2_ae_eq μ 1 u] with x hx
    simpa using hx
  map_mul' f g := by
    apply ContinuousLinearMap.ext
    intro u
    change mulOnL2 μ (f * g) u = mulOnL2 μ f (mulOnL2 μ g u)
    apply Lp.ext
    filter_upwards [mulOnL2_ae_eq μ (f * g) u, mulOnL2_ae_eq μ f (mulOnL2 μ g u),
      mulOnL2_ae_eq μ g u] with x hfg hf hg
    rw [hfg, hf, hg]
    exact mul_assoc _ _ _
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro u
    change mulOnL2 μ 0 u = 0
    apply Lp.ext
    filter_upwards [mulOnL2_ae_eq μ 0 u, (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ))] with x hx hz
    rw [hx, hz]
    simp
  map_add' f g := by
    apply ContinuousLinearMap.ext
    intro u
    change mulOnL2 μ (f + g) u = mulOnL2 μ f u + mulOnL2 μ g u
    apply Lp.ext
    filter_upwards [mulOnL2_ae_eq μ (f + g) u,
      Lp.coeFn_add (mulOnL2 μ f u) (mulOnL2 μ g u),
      mulOnL2_ae_eq μ f u, mulOnL2_ae_eq μ g u] with x hfg hsum hf hg
    rw [hfg, hsum]
    change (f x + g x) * u x = mulOnL2 μ f u x + mulOnL2 μ g u x
    rw [hf, hg]
    exact add_mul _ _ _
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro u
    change mulOnL2 μ (algebraMap ℂ (X →ᵇ ℂ) c) u = c • u
    apply Lp.ext
    filter_upwards [mulOnL2_ae_eq μ (algebraMap ℂ (X →ᵇ ℂ) c) u,
      Lp.coeFn_smul c u] with x hc hu
    exact hc.trans hu.symm
  map_star' f := by
    show l2MultiplicationOperator μ (star f) = star (l2MultiplicationOperator μ f)
    rw [ContinuousLinearMap.star_eq_adjoint]
    refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_
    intro u v
    simp only [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [l2MultiplicationOperator_ae_eq μ (star f) u,
      l2MultiplicationOperator_ae_eq μ f v] with x hfu hfv
    rw [hfu, hfv]
    rw [RCLike.inner_apply', RCLike.inner_apply']
    simp only [← RCLike.star_def, BoundedContinuousFunction.star_apply,
      star_mul, star_star, mul_assoc]

/-- **Value of the bounded-function multiplication representation.**

Let X be a topological space with its Borel measurable structure, μ any measure on X and
H=L²(X,μ;ℂ). For f∈C_b(X,ℂ), let M_f:H→H be multiplication by f, (M_f u)(x)=f(x)u(x) μ-almost
everywhere. For f∈C_b(X,ℂ) and u∈H, BoundedContinuousFunction.l2MultiplicationRepresentation μ
f u equals x↦f(x)u(x) μ-almost everywhere.
-/
theorem l2MultiplicationRepresentation_ae_eq (f : X →ᵇ ℂ) (u : Lp ℂ 2 μ) :
    l2MultiplicationRepresentation μ f u =ᵐ[μ] fun x => f x * u x :=
  l2MultiplicationOperator_ae_eq μ f u

end BoundedContinuousFunction

namespace ContinuousMap

universe uX

section CompactToBounded

variable {X : Type uX} [TopologicalSpace X] [CompactSpace X]

/-- **Bounded-function inclusion on a compact space.**

Let X be a compact topological space. The unital complex star homomorphism
ContinuousMap.toBoundedStarAlgHom:C(X,ℂ)→C_b(X,ℂ) sends each continuous function to the
bounded continuous function with the same values and supremum norm.
-/
def toBoundedStarAlgHom : C(X, ℂ) →⋆ₐ[ℂ] BoundedContinuousFunction X ℂ where
  toFun := BoundedContinuousFunction.mkOfCompact
  map_one' := rfl
  map_mul' _f _g := rfl
  map_zero' := rfl
  map_add' _f _g := rfl
  commutes' _c := rfl
  map_star' _f := rfl

end CompactToBounded

variable {X : Type uX} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [CompactSpace X]

/-- **Continuous-function multiplication representation on compact L².**

Let X be a compact topological space with its Borel measurable structure, μ any measure and
H=L²(X,μ;ℂ). The unital complex star homomorphism ContinuousMap.l2MultiplicationRepresentation
μ:C(X,ℂ)→B(H) sends f to the multiplication operator M_f u(x)=f(x)u(x) almost everywhere.
-/
def l2MultiplicationRepresentation (μ : Measure X) :
    C(X, ℂ) →⋆ₐ[ℂ] (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  (BoundedContinuousFunction.l2MultiplicationRepresentation μ).comp toBoundedStarAlgHom

/-- **Pointwise value of compact-space continuous multiplication.**

Let X be a compact Borel topological space, μ any measure, f∈C(X,ℂ) and u∈L²(X,μ;ℂ). Then
ContinuousMap.l2MultiplicationRepresentation μ f u equals x↦f(x)u(x) μ-almost everywhere.
-/
theorem l2MultiplicationRepresentation_ae_eq (μ : Measure X) (f : C(X, ℂ)) (u : Lp ℂ 2 μ) :
    l2MultiplicationRepresentation μ f u =ᵐ[μ] fun x => f x * u x :=
  BoundedContinuousFunction.l2MultiplicationRepresentation_ae_eq μ
    (BoundedContinuousFunction.mkOfCompact f) u

end ContinuousMap

end
