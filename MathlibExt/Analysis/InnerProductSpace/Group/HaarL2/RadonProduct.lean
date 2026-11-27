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
# Compact-support tensor products in Borel Radon L²

For locally compact Hausdorff Borel spaces and regular measures, the product of scalar
compact-support functions gives the bilinear map `(f,g) ↦ i_R((x,y) ↦ f(x)g(y))` into `Lp ℂ 2
R`, where `R=radonProd μ ν`.

Its inner product factors into the two factor inner products. The algebraic tensor lift `F`
consequently satisfies `⟨F(z),F(w)⟩=⟨A(z),A(w)⟩` and `‖F(z)‖=‖A(z)‖`, with `A` the tensor of the
compact-support factor L² inclusions. The product uses the Borel topological product and no
countability or s-finiteness assumption.
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

/-- **Real component of a compact-support complex function.** On any topological space `X`,
`realPart f∈C_c(X,ℝ)` is `x ↦ Re f(x)` for `f∈C_c(X,ℂ)`. -/
def realPart (f : C_c(X, ℂ)) : C_c(X, ℝ) where
  toFun x := (f x).re
  continuous_toFun := Complex.continuous_re.comp f.continuous
  hasCompactSupport' := f.hasCompactSupport.comp_left (g := Complex.re) (by simp)

/-- **Imaginary component of a compact-support complex function.** On any topological space
`X`, `imagPart f∈C_c(X,ℝ)` is `x ↦ Im f(x)`. -/
def imagPart (f : C_c(X, ℂ)) : C_c(X, ℝ) where
  toFun x := (f x).im
  continuous_toFun := Complex.continuous_im.comp f.continuous
  hasCompactSupport' := f.hasCompactSupport.comp_left (g := Complex.im) (by simp)

/-- **Value of a compact-support real component.** For topological `X`, `f∈C_c(X,ℂ)` and
`x∈X`, `realPart f x=Re f(x)`. -/
@[simp]
theorem realPart_apply (f : C_c(X, ℂ)) (x : X) : realPart f x = (f x).re := rfl

/-- **Value of a compact-support imaginary component.** For topological `X`, `f∈C_c(X,ℂ)` and
`x∈X`, `imagPart f x=Im f(x)`. -/
@[simp]
theorem imagPart_apply (f : C_c(X, ℂ)) (x : X) : imagPart f x = (f x).im := rfl

/-- **Pointwise complex inner pairing of compact-support functions.** For topological `X` and
`f,g∈C_c(X,ℂ)`, `innerPair f g=conj(f)*g`, linear in the second argument. -/
def innerPair (f g : C_c(X, ℂ)) : C_c(X, ℂ) := star f * g

/-- **Value of the compact-support complex pairing.** For topological `X`, `f,g∈C_c(X,ℂ)` and
`x∈X`, `innerPair f g x=⟨f(x),g(x)⟩_ℂ=conj(f(x))*g(x)`. -/
@[simp]
theorem innerPair_apply (f g : C_c(X, ℂ)) (x : X) :
    innerPair f g x = inner ℂ (f x) (g x) := by
  change star (f x) * g x = inner ℂ (f x) (g x)
  exact (RCLike.inner_apply' (f x) (g x)).symm

end Components

section BilinearProduct

variable {X : Type uX} [TopologicalSpace X] [T2Space X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]

/-- **Complex bilinear pure product of compact-support functions.** For Hausdorff spaces
`X,Y`, `mulProdBilinear : C_c(X,ℂ) →ₗ[ℂ] C_c(Y,ℂ) →ₗ[ℂ] C_c(X×Y,ℂ)` sends `(f,g)` to
`(x,y) ↦ f(x)g(y)`. -/
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

/-- **Pure product value of the compact-support bilinear map.** For Hausdorff `X,Y` and
compact-support complex `f,g`, `mulProdBilinear f g=mulProd f g`. -/
@[simp]
theorem mulProdBilinear_apply (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    mulProdBilinear f g = mulProd f g := rfl

/-- **Real part of a compact-support pure product.** For Hausdorff `X,Y` and complex
compact-support `f,g`, `Re(f⊠g)=(Re f⊠Re g)-(Im f⊠Im g)`, where `⊠` denotes pointwise
factor product. -/
theorem realPart_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    realPart (mulProd f g) = mulProd (realPart f) (realPart g) - mulProd (imagPart f) (imagPart g) := by
  ext z
  rcases z with ⟨x, y⟩
  change (f x * g y).re = (f x).re * (g y).re - (f x).im * (g y).im
  exact Complex.mul_re _ _

/-- **Imaginary part of a compact-support pure product.** For Hausdorff `X,Y` and complex
compact-support `f,g`, `Im(f⊠g)=(Re f⊠Im g)+(Im f⊠Re g)`. -/
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

/-- **Real part commutes with compact-support complex integration.** Let `X` have a topology
and measurable open sets, and `μ` be finite on compact sets. For `f∈C_c(X,ℂ)`, `∫ Re f
dμ=Re(∫ f dμ)`. -/
theorem integral_realPart (f : C_c(X, ℂ)) :
    ∫ x : X, realPart f x ∂μ = (∫ x : X, f x ∂μ).re := integral_re f.integrable

/-- **Imaginary part commutes with compact-support complex integration.** Let `X` have a
topology and measurable open sets, and `μ` be finite on compact sets. For `f∈C_c(X,ℂ)`, `∫
Im f dμ=Im(∫ f dμ)`. -/
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

/-- **Borel product structure for complex compact-support integration.** For topological
`X,Y`, the product carrier uses `borel(X×Y)` from its product topology. -/
local instance instComplexProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instComplexProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- **Complex pure-product Radon integral factors.** Let `X,Y` be locally compact Hausdorff
Borel spaces and `μ,ν` measures finite on compact sets. For `f∈C_c(X,ℂ)`, `g∈C_c(Y,ℂ)`, `∫
f(x)g(y) d(radonProd μ ν)=(∫ f dμ)(∫ g dν)`. -/
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

/-- **Borel topological product underlying scalar Radon L².** For topological `X,Y`, use
`borel(X×Y)` as the measurable structure of the product carrier. -/
local instance instProductL2BorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instProductL2BorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- **Bilinear compact-support product into Radon L².** Let `X,Y` be locally compact Hausdorff
Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on `borel(X×Y)`,
`i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)`,
`A(z)` for the algebraic factor tensor inclusion into `T`, and `F(f⊗g)=i_R((x,y) ↦
f(x)g(y))`. `compactSupportProduct μ ν f g=i_R((x,y) ↦ f(x)g(y))`. -/
def compactSupportProduct :
    C_c(X, ℂ) →ₗ[ℂ] C_c(Y, ℂ) →ₗ[ℂ] Lp ℂ 2 (Measure.radonProd μ ν) :=
  (mulProdBilinear (X := X) (Y := Y)).compr₂
    (compactSupportInclusion (H := ℂ) (Measure.radonProd μ ν))

/-- **Compact-support product followed by its L² inclusion.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `compactSupportProduct μ ν f g=i_R(mulProd f g)` for
`f∈C_c(X,ℂ)`, `g∈C_c(Y,ℂ)`. -/
@[simp]
theorem compactSupportProduct_apply (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    compactSupportProduct μ ν f g = compactSupportInclusion (Measure.radonProd μ ν) (mulProd f g) := rfl

/-- **Almost-everywhere scalar pure-product L² value.** Let `X,Y` be locally compact Hausdorff
Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on `borel(X×Y)`,
`i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)`,
`A(z)` for the algebraic factor tensor inclusion into `T`, and `F(f⊗g)=i_R((x,y) ↦
f(x)g(y))`. for compact-support `f,g`, `compactSupportProduct μ ν f g` has representative
`(x,y) ↦ f(x)g(y)` almost everywhere for `R`. -/
theorem compactSupportProduct_ae_eq (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    compactSupportProduct μ ν f g =ᵐ[Measure.radonProd μ ν] fun z => f z.1 * g z.2 :=
  compactSupportInclusion_ae_eq (Measure.radonProd μ ν) (mulProd f g)

/-- **Product of squared factor norms for a compact-support L² product.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `‖compactSupportProduct μ ν f g‖²=‖i_μ f‖²‖i_ν g‖²`. -/
theorem norm_compactSupportProduct_sq (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    ‖compactSupportProduct μ ν f g‖ ^ 2 =
      ‖compactSupportInclusion μ f‖ ^ 2 * ‖compactSupportInclusion ν g‖ ^ 2 := by
  rw [compactSupportProduct_apply, norm_compactSupportInclusion_sq,
    norm_compactSupportInclusion_sq, norm_compactSupportInclusion_sq]
  exact Measure.integral_norm_sq_mulProd μ ν f g

/-- **Full complex inner product of pure Radon products.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for compact-support `f,f',g,g'`,
`⟨i_R(f⊠g),i_R(f'⊠g')⟩=⟨i_μ f,i_μ f'⟩⟨i_ν g,i_ν g'⟩`. -/
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

/-- **Algebraic tensor of the two compact-support L² inclusions.** Let `X,Y` be topological
Borel spaces and `μ,ν` regular measures. For compact-support functions, let `A :
C_c(X,ℂ)⊗C_c(Y,ℂ) → T` be the tensor of their L² inclusions followed by completion.
`compactSupportFactorTensor μ ν : C_c(X,ℂ)⊗C_c(Y,ℂ) →ₗ[ℂ] Lp ℂ 2 μ⊗Lp ℂ 2 ν` sends `f⊗g`
to `i_μ f⊗i_ν g`. -/
def compactSupportFactorTensor :
    C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ) →ₗ[ℂ] (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν) :=
  TensorProduct.map (compactSupportInclusion μ) (compactSupportInclusion ν)

/-- **Algebraic tensor lift of compact-support Radon products.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `compactSupportTensorToLp μ ν=F` is the complex-linear
lift sending `f⊗g` to `i_R(f⊠g)`. -/
def compactSupportTensorToLp :
    C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ) →ₗ[ℂ] Lp ℂ 2 (Measure.radonProd μ ν) :=
  TensorProduct.lift (compactSupportProduct μ ν)

/-- **Pure tensor value of the compact-support Radon lift.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `F(f⊗g)=i_R(mulProd f g)`. -/
@[simp]
theorem compactSupportTensorToLp_tmul (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    compactSupportTensorToLp μ ν (f ⊗ₜ[ℂ] g) =
      compactSupportInclusion (Measure.radonProd μ ν) (mulProd f g) :=
  TensorProduct.lift.tmul (f' := compactSupportProduct μ ν) f g

/-- **Almost-everywhere pure tensor value of the Radon lift.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for compact-support `f,g`, `F(f⊗g)(x,y)=f(x)g(y)` for
`R`-almost every `(x,y)`. -/
theorem compactSupportTensorToLp_tmul_ae (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    compactSupportTensorToLp μ ν (f ⊗ₜ[ℂ] g) =ᵐ[Measure.radonProd μ ν] fun z => f z.1 * g z.2 := by
  rw [compactSupportTensorToLp_tmul]
  exact compactSupportInclusion_ae_eq (Measure.radonProd μ ν) (mulProd f g)

/-- **Finite tensor pairings equal the factor Hilbert pairings.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for algebraic compact-support tensors `z,w`,
`⟨F(z),F(w)⟩=⟨A(z),A(w)⟩`. -/
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

/-- **Norm of the algebraic Radon tensor lift.** Let `X,Y` be locally compact Hausdorff Borel
spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on `borel(X×Y)`, `i_μ,i_ν,i_R`
for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)`, `A(z)` for the
algebraic factor tensor inclusion into `T`, and `F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for every
algebraic compact-support tensor `z`, `‖F(z)‖=‖A(z)‖`. -/
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
