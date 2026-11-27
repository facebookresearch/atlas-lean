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

public import MathlibExt.MeasureTheory.Measure.RadonProduct
public import Mathlib.Analysis.Complex.Basic

/-!
# Compact-support pure products and their Radon integrals

For Hausdorff topological spaces and a topological multiplicative space with absorbing zero and
continuous multiplication, compact factor functions have compact-support product
`(f⊠g)(x,y)=f(x)g(y)`.

For complex factors, `|f⊠g|²=|f|²⊠|g|²`. On locally compact Hausdorff Borel spaces with measures
finite on compact sets, `∫ f⊠g d(μ⊗_Rν)=(∫ f dμ)(∫ g dν)` for real factors, and the squared-norm
integral factors likewise for complex factors. Countability and s-finiteness are not required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped CompactlySupported

noncomputable section

universe uX uY uR

namespace CompactlySupportedContinuousMap

section Product

variable {X : Type uX} [TopologicalSpace X] [T2Space X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]
variable {R : Type uR} [TopologicalSpace R] [MulZeroClass R] [ContinuousMul R]

/-- **Compact-support product of two factor functions.** Let `X,Y` be Hausdorff spaces and `R`
a topological space with multiplication, absorbing zero and continuous multiplication
(`MulZeroClass R`). For `f∈C_c(X,R)`, `g∈C_c(Y,R)`, `mulProd f g∈C_c(X×Y,R)` has value
`(x,y) ↦ f(x)g(y)`. No associativity, additive structure or measures are assumed. -/
def mulProd (f : C_c(X, R)) (g : C_c(Y, R)) : C_c(X × Y, R) where
  toFun z := f z.1 * g z.2
  continuous_toFun := (f.continuous.comp continuous_fst).mul (g.continuous.comp continuous_snd)
  hasCompactSupport' := by
    apply HasCompactSupport.intro (f.hasCompactSupport.prod g.hasCompactSupport)
    rintro ⟨x, y⟩ hxy
    by_cases hx : x ∈ tsupport f
    · have hy : y ∉ tsupport g := fun hy => hxy ⟨hx, hy⟩
      simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- **Pointwise value of a compact-support pure product.** For Hausdorff `X,Y`, a topological
`R` with absorbing zero and continuous multiplication, and compact-support factors `f,g`,
`mulProd f g (x,y)=f(x)g(y)`. -/
@[simp]
theorem mulProd_apply (f : C_c(X, R)) (g : C_c(Y, R)) (x : X) (y : Y) :
    mulProd f g (x, y) = f x * g y := rfl

end Product

section NormSquare

variable {X : Type uX} [TopologicalSpace X]

/-- **Real squared norm of a compact-support complex function.** For any topological space `X`
and `f∈C_c(X,ℂ)`, `normSq f∈C_c(X,ℝ)` has value `x ↦ |f(x)|²`; no Hausdorff or measure
hypothesis is required. -/
def normSq (f : C_c(X, ℂ)) : C_c(X, ℝ) where
  toFun x := ‖f x‖ ^ 2
  continuous_toFun := f.continuous.norm.pow 2
  hasCompactSupport' := f.hasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)

/-- **Value of the compact-support squared-norm function.** For topological `X`, `f∈C_c(X,ℂ)`
and `x∈X`, `normSq f x=|f(x)|²`. -/
@[simp]
theorem normSq_apply (f : C_c(X, ℂ)) (x : X) : normSq f x = ‖f x‖ ^ 2 := rfl

variable [T2Space X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]

/-- **Squared norm of a pure product factors pointwise.** For Hausdorff `X,Y` and complex
compact-support `f,g`, `normSq(mulProd f g)=mulProd(normSq f)(normSq g)`. -/
theorem normSq_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    normSq (mulProd f g) = mulProd (normSq f) (normSq g) := by
  ext z
  rcases z with ⟨x, y⟩
  simp only [normSq_apply, mulProd_apply, norm_mul, mul_pow]

end NormSquare

section CoordinateIntegral

variable {X : Type uX} [TopologicalSpace X] [T2Space X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]
  [MeasurableSpace Y] [OpensMeasurableSpace Y]
variable (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]

/-- **Coordinate integral of a real pure product.** Let `X` be Hausdorff, `Y` a topological
space with a measurable structure making open sets measurable, and `ν` finite on compact
sets. Assume `Y` is Hausdorff. for `f∈C_c(X,ℝ)`, `g∈C_c(Y,ℝ)`, `integralRight ν (mulProd f
g)=(∫ g dν) • f`. -/
theorem integralRight_mulProd (f : C_c(X, ℝ)) (g : C_c(Y, ℝ)) :
    integralRight ν (mulProd f g) = (∫ y : Y, g y ∂ν) • f := by
  ext x
  change (∫ y : Y, f x * g y ∂ν) = (∫ y : Y, g y ∂ν) * f x
  rw [integral_const_mul]
  exact mul_comm _ _

/-- **Coordinate integral of a complex pure product's squared norm.** Let `X` be Hausdorff,
`Y` a topological space with a measurable structure making open sets measurable, and `ν`
finite on compact sets. Assume `Y` is Hausdorff. for complex compact-support `f,g`,
`integralRight ν (normSq(mulProd f g))=(∫ |g|² dν) • normSq f`. -/
theorem integralRight_normSq_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    integralRight ν (normSq (mulProd f g)) = (∫ y : Y, ‖g y‖ ^ 2 ∂ν) • normSq f := by
  rw [normSq_mulProd]
  exact integralRight_mulProd ν (normSq f) (normSq g)

end CoordinateIntegral

end CompactlySupportedContinuousMap

namespace MeasureTheory.Measure

open CompactlySupportedContinuousMap

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y)
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]

/-- **Borel product structure for compact-support integration.** For topological spaces `X,Y`,
the product carrier uses `borel(X×Y)` from its product topology. -/
local instance instCompactSupportProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instCompactSupportProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- **Radon integral of a real pure product factors.** Let `X,Y` be locally compact Hausdorff
spaces with their Borel measurable structures, and `μ,ν` measures finite on compact sets.
Write `μ⊗_Rν=radonProd μ ν` on the Borel topological product `X×Y`. for `f∈C_c(X,ℝ)`,
`g∈C_c(Y,ℝ)`, `∫ mulProd f g d(μ⊗_Rν)=(∫ f dμ)*(∫ g dν)`. -/
theorem integral_mulProd (f : C_c(X, ℝ)) (g : C_c(Y, ℝ)) :
    ∫ z : X × Y, mulProd f g z ∂(radonProd μ ν) =
      (∫ x : X, f x ∂μ) * ∫ y : Y, g y ∂ν := by
  calc
    ∫ z : X × Y, mulProd f g z ∂(radonProd μ ν) =
        ∫ x : X, ∫ y : Y, f x * g y ∂ν ∂μ := integral_radonProd μ ν (mulProd f g)
    _ = ∫ x : X, f x * (∫ y : Y, g y ∂ν) ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => integral_const_mul (f x) (g : Y → ℝ))
    _ = (∫ x : X, f x ∂μ) * ∫ y : Y, g y ∂ν :=
      integral_mul_const (∫ y : Y, g y ∂ν) (f : X → ℝ)

/-- **Radon squared-norm integral of a complex pure product factors.** Let `X,Y` be locally
compact Hausdorff spaces with their Borel measurable structures, and `μ,ν` measures finite
on compact sets. Write `μ⊗_Rν=radonProd μ ν` on the Borel topological product `X×Y`. for
`f∈C_c(X,ℂ)`, `g∈C_c(Y,ℂ)`, `∫ |mulProd f g|² d(μ⊗_Rν)=(∫ |f|² dμ)*(∫ |g|² dν)`. -/
theorem integral_norm_sq_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    ∫ z : X × Y, ‖mulProd f g z‖ ^ 2 ∂(radonProd μ ν) =
      (∫ x : X, ‖f x‖ ^ 2 ∂μ) * ∫ y : Y, ‖g y‖ ^ 2 ∂ν := by
  change (∫ z : X × Y, normSq (mulProd f g) z ∂(radonProd μ ν)) = _
  rw [normSq_mulProd]
  exact integral_mulProd μ ν (normSq f) (normSq g)

end MeasureTheory.Measure

end
