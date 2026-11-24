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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.CompactSupport
public import MathlibExt.MeasureTheory.Measure.RadonProduct.CompactSupport
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# The actual compact-support tensor map into Borel Radon L2

The literal compact-support product is a complex bilinear map. Its actual
Lp inclusion gives an algebraic tensor map into the original Borel Radon
product L2 space. Compact-support complex integrals prove the full mixed
inner-product identity, including the imaginary part. Bilinearity then
preserves every finite tensor pairing and its norm, compared with the stock
tensor of the two original compact-support L2 inclusions.

No completed tensor equivalence, dense-range conclusion or coordinate shear
is selected here. Their full arbitrary-group source scope remains open.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped CompactlySupported TensorProduct InnerProductSpace

noncomputable section

universe uX uY

namespace CompactlySupportedContinuousMap

section Components

variable {X : Type uX} [TopologicalSpace X]

/-- The actual real component of a complex compact-support function. -/
def realPart (f : C_c(X, ℂ)) : C_c(X, ℝ) where
  toFun x := (f x).re
  continuous_toFun := Complex.continuous_re.comp f.continuous
  hasCompactSupport' := f.hasCompactSupport.comp_left (g := Complex.re) (by simp)

/-- The actual imaginary component of a complex compact-support function. -/
def imagPart (f : C_c(X, ℂ)) : C_c(X, ℝ) where
  toFun x := (f x).im
  continuous_toFun := Complex.continuous_im.comp f.continuous
  hasCompactSupport' := f.hasCompactSupport.comp_left (g := Complex.im) (by simp)

/-- The compact-support real component retains every original pointwise value. -/
@[simp]
theorem realPart_apply (f : C_c(X, ℂ)) (x : X) : realPart f x = (f x).re := rfl

/-- The compact-support imaginary component retains every original pointwise value. -/
@[simp]
theorem imagPart_apply (f : C_c(X, ℂ)) (x : X) : imagPart f x = (f x).im := rfl

/-- The actual compact-support scalar inner-product function, linear in the second factor. -/
def innerPair (f g : C_c(X, ℂ)) : C_c(X, ℂ) := star f * g

/-- The compact-support pairing is the original complex inner product at every point. -/
@[simp]
theorem innerPair_apply (f g : C_c(X, ℂ)) (x : X) :
    innerPair f g x = inner ℂ (f x) (g x) := by
  change star (f x) * g x = inner ℂ (f x) (g x)
  exact (RCLike.inner_apply' (f x) (g x)).symm

end Components

section BilinearProduct

variable {X : Type uX} [TopologicalSpace X] [T2Space X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]

/-- The literal compact-support pure product as an actual complex bilinear map. -/
def mulProdBilinear : C_c(X, ℂ) →ₗ[ℂ] C_c(Y, ℂ) →ₗ[ℂ] C_c(X × Y, ℂ) where
  toFun f :=
    { toFun g := mulProd f g
      map_add' g h := by
        apply CompactlySupportedContinuousMap.ext
        rintro ⟨x, y⟩
        change f x * (g y + h y) = f x * g y + f x * h y
        exact mul_add _ _ _
      map_smul' c g := by
        apply CompactlySupportedContinuousMap.ext
        rintro ⟨x, y⟩
        change f x * (c * g y) = c * (f x * g y)
        rw [← mul_assoc, mul_comm (f x) c, mul_assoc] }
  map_add' f h := by
    apply LinearMap.ext
    intro g
    apply CompactlySupportedContinuousMap.ext
    rintro ⟨x, y⟩
    change (f x + h x) * g y = f x * g y + h x * g y
    exact add_mul _ _ _
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    apply CompactlySupportedContinuousMap.ext
    rintro ⟨x, y⟩
    change (c * f x) * g y = c * (f x * g y)
    exact mul_assoc _ _ _

/-- The bilinear constructor retains the exact compact-support pure product. -/
@[simp]
theorem mulProdBilinear_apply (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    mulProdBilinear f g = mulProd f g := rfl

/-- The real component of a pure product has the original real multiplication formula. -/
theorem realPart_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    realPart (mulProd f g) = mulProd (realPart f) (realPart g) - mulProd (imagPart f) (imagPart g) := by
  ext z
  rcases z with ⟨x, y⟩
  change (f x * g y).re = (f x).re * (g y).re - (f x).im * (g y).im
  exact Complex.mul_re _ _

/-- The imaginary component of a pure product has the original imaginary multiplication formula. -/
theorem imagPart_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    imagPart (mulProd f g) = mulProd (realPart f) (imagPart g) + mulProd (imagPart f) (realPart g) := by
  ext z
  rcases z with ⟨x, y⟩
  change (f x * g y).im = (f x).re * (g y).im + (f x).im * (g y).re
  exact Complex.mul_im _ _

end BilinearProduct

section ComponentIntegral

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

/-- The compact-support real-component integral is the real part of the original complex integral. -/
theorem integral_realPart (f : C_c(X, ℂ)) :
    ∫ x : X, realPart f x ∂μ = (∫ x : X, f x ∂μ).re := integral_re f.integrable

/-- The compact-support imaginary-component integral is the imaginary part of the original complex integral. -/
theorem integral_imagPart (f : C_c(X, ℂ)) :
    ∫ x : X, imagPart f x ∂μ = (∫ x : X, f x ∂μ).im := integral_im f.integrable

end ComponentIntegral

end CompactlySupportedContinuousMap

namespace MeasureTheory.Measure

open CompactlySupportedContinuousMap

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y)
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]

/-- The Borel measurable space of the literal product for compact-support complex integration. -/
local instance instComplexProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instComplexProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- The original Borel Radon integral of a complex compact-support pure product factors exactly. -/
theorem integral_mulProd_complex (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    ∫ z : X × Y, mulProd f g z ∂(radonProd μ ν) =
      (∫ x : X, f x ∂μ) * ∫ y : Y, g y ∂ν := by
  apply Complex.ext
  · rw [← integral_realPart (radonProd μ ν) (mulProd f g), realPart_mulProd]
    simp only [CompactlySupportedContinuousMap.sub_apply]
    rw [integral_sub (mulProd (realPart f) (realPart g)).integrable
      (mulProd (imagPart f) (imagPart g)).integrable]
    rw [integral_mulProd μ ν (realPart f) (realPart g),
      integral_mulProd μ ν (imagPart f) (imagPart g)]
    rw [integral_realPart μ f, integral_realPart ν g, integral_imagPart μ f, integral_imagPart ν g]
    exact (Complex.mul_re _ _).symm
  · rw [← integral_imagPart (radonProd μ ν) (mulProd f g), imagPart_mulProd]
    simp only [CompactlySupportedContinuousMap.add_apply]
    rw [integral_add (mulProd (realPart f) (imagPart g)).integrable
      (mulProd (imagPart f) (realPart g)).integrable]
    rw [integral_mulProd μ ν (realPart f) (imagPart g),
      integral_mulProd μ ν (imagPart f) (realPart g)]
    rw [integral_realPart μ f, integral_imagPart ν g, integral_imagPart μ f, integral_realPart ν g]
    exact (Complex.mul_im _ _).symm

end MeasureTheory.Measure

namespace MeasureTheory.HaarL2

open CompactlySupportedContinuousMap

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]

/-- The Borel measurable space of the literal product used by the original product L2 carrier. -/
local instance instProductL2BorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instProductL2BorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- The computed compact-support bilinear map into the actual Borel Radon product L2 space. -/
def compactSupportProduct :
    C_c(X, ℂ) →ₗ[ℂ] C_c(Y, ℂ) →ₗ[ℂ] Lp ℂ 2 (Measure.radonProd μ ν) :=
  (mulProdBilinear (X := X) (Y := Y)).compr₂
    (compactSupportInclusion (H := ℂ) (Measure.radonProd μ ν))

/-- The bilinear L2 map is the literal compact-support product followed by the original inclusion. -/
@[simp]
theorem compactSupportProduct_apply (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    compactSupportProduct μ ν f g = compactSupportInclusion (Measure.radonProd μ ν) (mulProd f g) := rfl

/-- The computed product L2 vector retains its literal factor values almost everywhere. -/
theorem compactSupportProduct_ae_eq (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    compactSupportProduct μ ν f g =ᵐ[Measure.radonProd μ ν] fun z => f z.1 * g z.2 :=
  compactSupportInclusion_ae_eq (Measure.radonProd μ ν) (mulProd f g)

/-- The computed pure product has the exact product of the original factor L2 squared norms. -/
theorem norm_compactSupportProduct_sq (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    ‖compactSupportProduct μ ν f g‖ ^ 2 =
      ‖compactSupportInclusion μ f‖ ^ 2 * ‖compactSupportInclusion ν g‖ ^ 2 := by
  rw [compactSupportProduct_apply, norm_compactSupportInclusion_sq,
    norm_compactSupportInclusion_sq, norm_compactSupportInclusion_sq]
  exact Measure.integral_norm_sq_mulProd μ ν f g

/-- The actual compact-support pure products preserve the full complex mixed factor pairing. -/
theorem compactSupportProduct_inner
    (f f' : C_c(X, ℂ)) (g g' : C_c(Y, ℂ)) :
    inner ℂ (compactSupportProduct μ ν f g) (compactSupportProduct μ ν f' g') =
      inner ℂ (compactSupportInclusion μ f) (compactSupportInclusion μ f') *
        inner ℂ (compactSupportInclusion ν g) (compactSupportInclusion ν g') := by
  rw [compactSupportProduct_apply, compactSupportProduct_apply]
  calc
    inner ℂ (compactSupportInclusion (Measure.radonProd μ ν) (mulProd f g))
        (compactSupportInclusion (Measure.radonProd μ ν) (mulProd f' g')) =
      ∫ z : X × Y, inner ℂ (mulProd f g z) (mulProd f' g' z) ∂(Measure.radonProd μ ν) :=
      compactSupportInclusion_inner (Measure.radonProd μ ν) _ _
    _ = ∫ z : X × Y, mulProd (innerPair f f') (innerPair g g') z ∂(Measure.radonProd μ ν) := by
      apply integral_congr_ae
      refine Eventually.of_forall ?_
      rintro ⟨x, y⟩
      simp only [mulProd_apply, innerPair_apply]
      simpa only [TensorProduct.inner_tmul] using
        (RCLike.inner_tmul_eq (f x) (g y) (f' x) (g' y)).symm
    _ = (∫ x : X, innerPair f f' x ∂μ) * ∫ y : Y, innerPair g g' y ∂ν :=
      Measure.integral_mulProd_complex μ ν (innerPair f f') (innerPair g g')
    _ = inner ℂ (compactSupportInclusion μ f) (compactSupportInclusion μ f') *
        inner ℂ (compactSupportInclusion ν g) (compactSupportInclusion ν g') := by
      rw [compactSupportInclusion_inner, compactSupportInclusion_inner]
      congr 1
      · exact integral_congr_ae (Eventually.of_forall fun x => innerPair_apply f f' x)
      · exact integral_congr_ae (Eventually.of_forall fun y => innerPair_apply g g' y)

/-- The literal algebraic tensor of the original two compact-support L2 inclusions. -/
def compactSupportFactorTensor :
    C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ) →ₗ[ℂ] (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν) :=
  TensorProduct.map (compactSupportInclusion μ) (compactSupportInclusion ν)

/-- The algebraic tensor lift of the computed product L2 bilinear map. -/
def compactSupportTensorToLp :
    C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ) →ₗ[ℂ] Lp ℂ 2 (Measure.radonProd μ ν) :=
  TensorProduct.lift (compactSupportProduct μ ν)

/-- The actual algebraic lift has its literal compact-support pure-tensor value. -/
@[simp]
theorem compactSupportTensorToLp_tmul (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    compactSupportTensorToLp μ ν (f ⊗ₜ[ℂ] g) =
      compactSupportInclusion (Measure.radonProd μ ν) (mulProd f g) :=
  TensorProduct.lift.tmul (f' := compactSupportProduct μ ν) f g

/-- The actual algebraic pure-tensor value is the original pointwise product almost everywhere. -/
theorem compactSupportTensorToLp_tmul_ae (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    compactSupportTensorToLp μ ν (f ⊗ₜ[ℂ] g) =ᵐ[Measure.radonProd μ ν] fun z => f z.1 * g z.2 := by
  rw [compactSupportTensorToLp_tmul]
  exact compactSupportInclusion_ae_eq (Measure.radonProd μ ν) (mulProd f g)

/-- Every finite compact-support tensor pairing agrees with its original stock factor-tensor pairing. -/
theorem compactSupportTensorToLp_inner (z w : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    inner ℂ (compactSupportTensorToLp μ ν z) (compactSupportTensorToLp μ ν w) =
      inner ℂ (compactSupportFactorTensor μ ν z) (compactSupportFactorTensor μ ν w) := by
  induction z using TensorProduct.inductionOn with
  | tmul f g =>
    induction w using TensorProduct.inductionOn with
    | tmul f' g' =>
      simp only [compactSupportTensorToLp_tmul, compactSupportFactorTensor,
        TensorProduct.map_tmul, TensorProduct.inner_tmul]
      exact compactSupportProduct_inner μ ν f f' g g'
    | add z w hz hw => simp only [map_add, inner_add_right, hz, hw]
  | add z w hz hw => simp only [map_add, inner_add_left, hz, hw]

/-- Every finite compact-support tensor has the original stock factor-tensor norm. -/
theorem norm_compactSupportTensorToLp (z : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
    ‖compactSupportTensorToLp μ ν z‖ = ‖compactSupportFactorTensor μ ν z‖ := by
  have hsq : ‖compactSupportTensorToLp μ ν z‖ ^ 2 = ‖compactSupportFactorTensor μ ν z‖ ^ 2 := by
    calc
      ‖compactSupportTensorToLp μ ν z‖ ^ 2 =
          RCLike.re (inner ℂ (compactSupportTensorToLp μ ν z) (compactSupportTensorToLp μ ν z)) :=
        InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
      _ = RCLike.re (inner ℂ (compactSupportFactorTensor μ ν z) (compactSupportFactorTensor μ ν z)) :=
        congrArg RCLike.re (compactSupportTensorToLp_inner μ ν z z)
      _ = ‖compactSupportFactorTensor μ ν z‖ ^ 2 :=
        (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
          (compactSupportFactorTensor μ ν z)).symm
  simpa only [Real.sqrt_sq (norm_nonneg (compactSupportTensorToLp μ ν z)),
    Real.sqrt_sq (norm_nonneg (compactSupportFactorTensor μ ν z))] using congrArg Real.sqrt hsq

end MeasureTheory.HaarL2

end
