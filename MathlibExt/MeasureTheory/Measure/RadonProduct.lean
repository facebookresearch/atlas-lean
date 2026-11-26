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

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Radon product on a topological product's Borel structure

For locally compact Hausdorff Borel spaces `X,Y` and measures `μ,ν` finite on compact sets,
define the positive functional on `C_c(X×Y,ℝ)` by `f ↦ ∫ x, ∫ y, f(x,y) dν dμ`.

Its regular Riesz measure is `radonProd μ ν` on `borel(X×Y)`. Integration against it recovers
this iterated integral. The factor measures need not be regular, and no countability or
s-finiteness assumption is made. Equality with a product of measurable spaces is not imposed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped CompactlySupported

noncomputable section

universe uX uY

namespace CompactlySupportedContinuousMap

variable {X : Type uX} [TopologicalSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]

/-- **Second-coordinate section of a compact-support real function.** Let `X` be topological,
`Y` Hausdorff and `f∈C_c(X×Y,ℝ)`. For `x∈X`, `sectionRight f x∈C_c(Y,ℝ)` has value `y ↦
f(x,y)`. No measure or local compactness is required. -/
def sectionRight (f : C_c(X × Y, ℝ)) (x : X) : C_c(Y, ℝ) where
  toFun y := f (x, y)
  continuous_toFun := f.continuous.comp (continuous_const.prodMk continuous_id)
  hasCompactSupport' := by
    apply HasCompactSupport.intro (f.hasCompactSupport.image continuous_snd)
    intro y hy
    exact image_eq_zero_of_notMem_tsupport
      (fun hxy => hy ⟨(x, y), hxy, rfl⟩)

/-- **Value of a compact-support section.** Let `X` be topological, `Y` Hausdorff,
`f∈C_c(X×Y,ℝ)` and `x∈X`, `y∈Y`. Then `sectionRight f x y=f(x,y)`. -/
@[simp]
theorem sectionRight_apply (f : C_c(X × Y, ℝ)) (x : X) (y : Y) :
    sectionRight f x y = f (x, y) := rfl

variable [T2Space X] [MeasurableSpace Y] [OpensMeasurableSpace Y]
variable (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]

/-- **Compact-support function obtained by second-coordinate integration.** Let `X` be
Hausdorff, `Y` a topological space with a measurable structure making open sets
measurable, and `ν` finite on compact sets. for `f∈C_c(X×Y,ℝ)`, `integralRight ν
f∈C_c(X,ℝ)` has value `x ↦ ∫ y, f(x,y) dν`. Hausdorffness of `Y` is not required for this
value construction. -/
def integralRight (f : C_c(X × Y, ℝ)) : C_c(X, ℝ) where
  toFun x := ∫ y : Y, f (x, y) ∂ν
  continuous_toFun := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support
      (f.hasCompactSupport.image continuous_snd)
    · have huncurry :
          (Function.uncurry (fun (x : X) (y : Y) => f (x, y)) : X × Y → ℝ) =
            (f.toContinuousMap : X × Y → ℝ) := by
        funext p
        rcases p with ⟨x, y⟩
        rfl
      rw [huncurry, univ_prod_univ]
      exact f.continuous.continuousOn
    · intro x y _ hy
      exact image_eq_zero_of_notMem_tsupport
        (fun hxy => hy ⟨(x, y), hxy, rfl⟩)
  hasCompactSupport' := by
    apply HasCompactSupport.intro (f.hasCompactSupport.image continuous_fst)
    intro x hx
    have hzero (y : Y) : f (x, y) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hxy => hx ⟨(x, y), hxy, rfl⟩)
    simp only [hzero, integral_zero]

omit [T2Space Y] in
/-- **Pointwise value of a coordinate integral.** Let `X` be Hausdorff, `Y` a topological
space with a measurable structure making open sets measurable, and `ν` finite on compact
sets. for `f∈C_c(X×Y,ℝ)` and `x∈X`, `integralRight ν f x=∫ y, f(x,y) dν`. -/
@[simp]
theorem integralRight_apply (f : C_c(X × Y, ℝ)) (x : X) :
    integralRight ν f x = ∫ y : Y, f (x, y) ∂ν := rfl

/-- **Positive linear second-coordinate integral map.** Let `X` be Hausdorff, `Y` a
topological space with a measurable structure making open sets measurable, and `ν` finite
on compact sets. Assume also that `Y` is Hausdorff. `integralRightPositiveLinearMap ν`
sends `f∈C_c(X×Y,ℝ)` to `integralRight ν f`, preserving addition, real scalars and order. -/
def integralRightPositiveLinearMap : C_c(X × Y, ℝ) →ₚ[ℝ] C_c(X, ℝ) where
  toFun := integralRight ν
  map_add' f g := by
    ext x
    change (∫ y : Y, f (x, y) + g (x, y) ∂ν) =
      (∫ y : Y, f (x, y) ∂ν) + ∫ y : Y, g (x, y) ∂ν
    exact integral_add (sectionRight f x).integrable (sectionRight g x).integrable
  map_smul' c f := by
    ext x
    change (∫ y : Y, c • f (x, y) ∂ν) = c • ∫ y : Y, f (x, y) ∂ν
    exact integral_smul c (fun y : Y => f (x, y))
  monotone' := by
    intro f g hfg x
    exact integral_mono (sectionRight f x).integrable (sectionRight g x).integrable
      (fun y => hfg (x, y))

/-- **Function value of the positive coordinate integral map.** Let `X` be Hausdorff, `Y` a
topological space with a measurable structure making open sets measurable, and `ν` finite
on compact sets. Assume `Y` is Hausdorff. for `f∈C_c(X×Y,ℝ)`,
`integralRightPositiveLinearMap ν f=integralRight ν f`. -/
@[simp]
theorem integralRightPositiveLinearMap_apply (f : C_c(X × Y, ℝ)) :
    integralRightPositiveLinearMap ν f = integralRight ν f := rfl

end CompactlySupportedContinuousMap

namespace MeasureTheory.Measure

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y)
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]

/-- **Borel measurable structure of a topological product.** For topological spaces `X,Y`, use
`borel(X×Y)` from the product topology as the measurable structure on `X×Y`. -/
local instance instProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- **Regular Riesz measure of the iterated compact-support integral.** Let `X,Y` be locally
compact Hausdorff spaces with their Borel measurable structures, and `μ,ν` measures finite
on compact sets. Write `μ⊗_Rν=radonProd μ ν` on the Borel topological product `X×Y`.
`radonProd μ ν` is the regular measure representing `f ↦ ∫ x, ∫ y, f(x,y) dν dμ` on
`C_c(X×Y,ℝ)`. -/
def radonProd : @Measure (X × Y) (borel (X × Y)) :=
  RealRMK.rieszMeasure
    ((CompactlySupportedContinuousMap.integralPositiveLinearMap μ).comp
      (CompactlySupportedContinuousMap.integralRightPositiveLinearMap ν))

/-- **Regularity of the Borel Radon product.** Let `X,Y` be locally compact Hausdorff spaces
with their Borel measurable structures, and `μ,ν` measures finite on compact sets. Write
`μ⊗_Rν=radonProd μ ν` on the Borel topological product `X×Y`. the measure `μ⊗_Rν` is
regular, even without regularity assumptions on the factor measures. -/
instance regular_radonProd : (radonProd μ ν).Regular := by
  unfold radonProd
  infer_instance

/-- **Defining iterated integral of the Borel Radon product.** Let `X,Y` be locally compact
Hausdorff spaces with their Borel measurable structures, and `μ,ν` measures finite on
compact sets. Write `μ⊗_Rν=radonProd μ ν` on the Borel topological product `X×Y`. for
`f∈C_c(X×Y,ℝ)`, `∫ f d(μ⊗_Rν)=∫ x, ∫ y, f(x,y) dν dμ`. -/
theorem integral_radonProd (f : C_c(X × Y, ℝ)) :
    ∫ z : X × Y, f z ∂(radonProd μ ν) =
      ∫ x : X, ∫ y : Y, f (x, y) ∂ν ∂μ :=
  RealRMK.integral_rieszMeasure
    ((CompactlySupportedContinuousMap.integralPositiveLinearMap μ).comp
      (CompactlySupportedContinuousMap.integralRightPositiveLinearMap ν)) f

end MeasureTheory.Measure

end
