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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.RadonProduct
public import MathlibExt.MeasureTheory.Function.L2Space.TensorProduct
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Compact-support L²-valued sections of a Radon product

A complex compact-support function `F` on a product has second-coordinate sections `S_F(x)=i_ν(y
↦ F(x,y))`. These are norm-continuous, and for Hausdorff `X` form a compact-support function
with values in `Lp ℂ 2 ν`.

For locally compact Hausdorff Borel factors with regular measures, the iterated L² vector `J(F)`
has the same squared norm as `i_R(F)`. The inverse one-measure tensor comparison gives a
factor-tensor representative `K(F)` with this norm. No countability or s-finiteness assumption
is required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped CompactlySupported TensorProduct Topology

noncomputable section

universe uX uY

namespace CompactlySupportedContinuousMap

section Sections

variable {X : Type uX} [TopologicalSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y]

/-- **Complex compact-support section in the second coordinate.** For topological `X`,
Hausdorff `Y` and `F∈C_c(X×Y,ℂ)`, `sectionRightComplex F x∈C_c(Y,ℂ)` is `y ↦ F(x,y)`. -/
def sectionRightComplex (F : C_c(X × Y, ℂ)) (x : X) : C_c(Y, ℂ) where
  toFun y := F (x, y)
  continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
  hasCompactSupport' := by
    apply HasCompactSupport.intro (F.hasCompactSupport.image continuous_snd)
    intro y hy
    exact image_eq_zero_of_notMem_tsupport (fun hxy => hy ⟨(x, y), hxy, rfl⟩)

/-- **Pointwise value of a complex compact-support section.** For topological `X`, Hausdorff
`Y`, `F∈C_c(X×Y,ℂ)` and `x,y`, `sectionRightComplex F x y=F(x,y)`. -/
@[simp]
theorem sectionRightComplex_apply (F : C_c(X × Y, ℂ)) (x : X) (y : Y) :
    sectionRightComplex F x y = F (x, y) := rfl

variable [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [ν.Regular]

/-- **Scalar L² vector of a compact-support product section.** Let `X` be topological, `Y`
Hausdorff with its Borel structure and regular measure `ν`, and `F∈C_c(X×Y,ℂ)`. Write
`S_F(x)=i_ν(y ↦ F(x,y)) ∈ Lp ℂ 2 ν`. `sectionRightLp ν F x=S_F(x)`. -/
def sectionRightLp (F : C_c(X × Y, ℂ)) (x : X) : Lp ℂ 2 ν :=
  HaarL2.compactSupportInclusion ν (sectionRightComplex F x)

/-- **Almost-everywhere representative of an L² section.** Let `X` be topological, `Y`
Hausdorff with its Borel structure and regular measure `ν`, and `F∈C_c(X×Y,ℂ)`. Write
`S_F(x)=i_ν(y ↦ F(x,y)) ∈ Lp ℂ 2 ν`. for `x∈X`, `S_F(x)(y)=F(x,y)` for `ν`-almost every
`y`. -/
theorem sectionRightLp_ae_eq (F : C_c(X × Y, ℂ)) (x : X) :
    sectionRightLp ν F x =ᵐ[ν] fun y => F (x, y) :=
  HaarL2.compactSupportInclusion_ae_eq ν (sectionRightComplex F x)

/-- **Squared L² norm of a compact-support section.** Let `X` be topological, `Y` Hausdorff
with its Borel structure and regular measure `ν`, and `F∈C_c(X×Y,ℂ)`. Write `S_F(x)=i_ν(y
↦ F(x,y)) ∈ Lp ℂ 2 ν`. for `x∈X`, `‖S_F(x)‖²=∫ |F(x,y)|² dν(y)`. -/
theorem norm_sectionRightLp_sq (F : C_c(X × Y, ℂ)) (x : X) :
    ‖sectionRightLp ν F x‖ ^ 2 = ∫ y : Y, ‖F (x, y)‖ ^ 2 ∂ν :=
  HaarL2.norm_compactSupportInclusion_sq ν (sectionRightComplex F x)

/-- **Squared distance between scalar L² sections.** Let `X` be topological, `Y` Hausdorff
with its Borel structure and regular measure `ν`, and `F∈C_c(X×Y,ℂ)`. Write `S_F(x)=i_ν(y
↦ F(x,y)) ∈ Lp ℂ 2 ν`. for `x,x'∈X`, `‖S_F(x)-S_F(x')‖²=∫ |F(x,y)-F(x',y)|² dν(y)`. -/
theorem norm_sectionRightLp_sub_sq (F : C_c(X × Y, ℂ)) (x x' : X) :
    ‖sectionRightLp ν F x - sectionRightLp ν F x'‖ ^ 2 =
      ∫ y : Y, ‖F (x, y) - F (x', y)‖ ^ 2 ∂ν := by
  change ‖HaarL2.compactSupportInclusion ν (sectionRightComplex F x) -
    HaarL2.compactSupportInclusion ν (sectionRightComplex F x')‖ ^ 2 = _
  rw [← map_sub, HaarL2.norm_compactSupportInclusion_sq]
  simp only [CompactlySupportedContinuousMap.sub_apply, sectionRightComplex_apply]

/-- **Norm-continuity of the compact-support L² section map.** Let `X` be topological, `Y`
Hausdorff with its Borel structure and regular measure `ν`, and `F∈C_c(X×Y,ℂ)`. Write
`S_F(x)=i_ν(y ↦ F(x,y)) ∈ Lp ℂ 2 ν`. the function `x ↦ S_F(x)` is continuous in the L²
norm. -/
theorem continuous_sectionRightLp (F : C_c(X × Y, ℂ)) : Continuous (sectionRightLp ν F) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hI : Continuous (fun x : X => ∫ y : Y, ‖F (x, y) - F (x₀, y)‖ ^ 2 ∂ν) := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (F.hasCompactSupport.image continuous_snd)
    · rw [univ_prod_univ]
      have hanchor : Continuous (fun _ : X × Y => x₀) := continuous_const
      refine ((F.continuous.sub (F.continuous.comp
        (hanchor.prodMk continuous_snd))).norm.pow 2).continuousOn.congr ?_
      rintro ⟨x, y⟩ _
      rfl
    · intro x y _ hy
      have hx : F (x, y) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hxy => hy ⟨(x, y), hxy, rfl⟩)
      have hx₀ : F (x₀, y) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hxy => hy ⟨(x₀, y), hxy, rfl⟩)
      simp only [hx, hx₀, sub_self, norm_zero, zero_pow two_ne_zero]
  have hN : Continuous (fun x : X => ‖sectionRightLp ν F x - sectionRightLp ν F x₀‖) := by
    have hEq : (fun x : X => ‖sectionRightLp ν F x - sectionRightLp ν F x₀‖) =
        fun x : X => Real.sqrt (∫ y : Y, ‖F (x, y) - F (x₀, y)‖ ^ 2 ∂ν) := by
      funext x
      rw [← norm_sectionRightLp_sub_sq,
        Real.sqrt_sq (norm_nonneg (sectionRightLp ν F x - sectionRightLp ν F x₀))]
    rw [hEq]
    exact Real.continuous_sqrt.comp hI
  simpa only [sub_self, norm_zero] using (hN.continuousAt (x := x₀)).tendsto

variable [T2Space X]

/-- **Compact-support function of scalar L² sections.** Let `X` be topological, `Y` Hausdorff
with its Borel structure and regular measure `ν`, and `F∈C_c(X×Y,ℂ)`. Write `S_F(x)=i_ν(y
↦ F(x,y)) ∈ Lp ℂ 2 ν`. assume additionally that `X` is Hausdorff. `sectionToLp ν
F∈C_c(X,Lp ℂ 2 ν)` sends `x` to `S_F(x)`. -/
def sectionToLp (F : C_c(X × Y, ℂ)) : C_c(X, Lp ℂ 2 ν) where
  toFun := sectionRightLp ν F
  continuous_toFun := continuous_sectionRightLp ν F
  hasCompactSupport' := by
    apply HasCompactSupport.intro (F.hasCompactSupport.image continuous_fst)
    intro x hx
    have hzero : sectionRightComplex F x = 0 := by
      apply CompactlySupportedContinuousMap.ext
      intro y
      change F (x, y) = 0
      exact image_eq_zero_of_notMem_tsupport (fun hxy => hx ⟨(x, y), hxy, rfl⟩)
    change HaarL2.compactSupportInclusion ν (sectionRightComplex F x) = 0
    rw [hzero, map_zero]

/-- **Value of the compact-support L² section constructor.** Let `X` be topological, `Y`
Hausdorff with its Borel structure and regular measure `ν`, and `F∈C_c(X×Y,ℂ)`. Write
`S_F(x)=i_ν(y ↦ F(x,y)) ∈ Lp ℂ 2 ν`. for Hausdorff `X`, `sectionToLp ν F x=sectionRightLp
ν F x`. -/
@[simp]
theorem sectionToLp_apply (F : C_c(X × Y, ℂ)) (x : X) :
    sectionToLp ν F x = sectionRightLp ν F x := rfl

/-- **Complex-linear construction of compact-support L² sections.** Let `X` be topological,
`Y` Hausdorff with its Borel structure and regular measure `ν`, and `F∈C_c(X×Y,ℂ)`. Write
`S_F(x)=i_ν(y ↦ F(x,y)) ∈ Lp ℂ 2 ν`. for Hausdorff `X`, `sectionToLpLinearMap ν :
C_c(X×Y,ℂ) →ₗ[ℂ] C_c(X,Lp ℂ 2 ν)` sends each product function to its section map. -/
def sectionToLpLinearMap : C_c(X × Y, ℂ) →ₗ[ℂ] C_c(X, Lp ℂ 2 ν) where
  toFun := sectionToLp ν
  map_add' F G := CompactlySupportedContinuousMap.ext (fun x => by
    change HaarL2.compactSupportInclusion ν (sectionRightComplex (F + G) x) =
      HaarL2.compactSupportInclusion ν (sectionRightComplex F x) +
        HaarL2.compactSupportInclusion ν (sectionRightComplex G x)
    have hsection : sectionRightComplex (F + G) x =
        sectionRightComplex F x + sectionRightComplex G x := by
      apply CompactlySupportedContinuousMap.ext
      intro y
      rfl
    rw [hsection, map_add])
  map_smul' c F := CompactlySupportedContinuousMap.ext (fun x => by
    change HaarL2.compactSupportInclusion ν (sectionRightComplex (c • F) x) =
      c • HaarL2.compactSupportInclusion ν (sectionRightComplex F x)
    have hsection : sectionRightComplex (c • F) x = c • sectionRightComplex F x := by
      apply CompactlySupportedContinuousMap.ext
      intro y
      rfl
    rw [hsection, map_smul])

/-- **Section of a pure compact-support scalar product.** Let `X` be topological, `Y`
Hausdorff with its Borel structure and regular measure `ν`, and `F∈C_c(X×Y,ℂ)`. Write
`S_F(x)=i_ν(y ↦ F(x,y)) ∈ Lp ℂ 2 ν`. for Hausdorff `X` and compact-support factors `f,g`,
`S_(f⊠g)(x)=f(x) • i_ν(g)`. -/
theorem sectionRightLp_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) (x : X) :
    sectionRightLp ν (mulProd f g) x = f x • HaarL2.compactSupportInclusion ν g := by
  change HaarL2.compactSupportInclusion ν (sectionRightComplex (mulProd f g) x) =
    f x • HaarL2.compactSupportInclusion ν g
  rw [← map_smul]
  congr 1

end Sections

end CompactlySupportedContinuousMap

namespace MeasureTheory.HaarL2

open CompactlySupportedContinuousMap

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]

/-- **Borel topological product for L² section comparisons.** For topological `X,Y`, the
product measurable structure is `borel(X×Y)`. -/
local instance instSectionsProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instSectionsProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- **Iterated L² vector of compact-support sections.** Let `X,Y` be Hausdorff Borel spaces,
`μ,ν` regular measures and `F∈C_c(X×Y,ℂ)`. Write `S_F(x)=i_ν(y ↦ F(x,y))`, `J(F)=i_μ(S_F)
∈ Lp (Lp ℂ 2 ν) 2 μ`, and `K(F)=tensorToLp μ⁻¹(J(F)) ∈ Completion(Lp ℂ 2 μ⊗Lp ℂ 2 ν)`.
`productToIteratedLp μ ν F=J(F)` is the L² inclusion of the compact-support section map `x
↦ S_F(x)`; local compactness is not required for this constructor. -/
def productToIteratedLp : C_c(X × Y, ℂ) →ₗ[ℂ] Lp (Lp ℂ 2 ν) 2 μ :=
  (compactSupportInclusion (H := Lp ℂ 2 ν) μ).comp (sectionToLpLinearMap ν)

omit [LocallyCompactSpace X] [LocallyCompactSpace Y] in
/-- **Almost-everywhere section values of the iterated L² construction.** Let `X,Y` be
Hausdorff Borel spaces, `μ,ν` regular measures and `F∈C_c(X×Y,ℂ)`. Write `S_F(x)=i_ν(y ↦
F(x,y))`, `J(F)=i_μ(S_F) ∈ Lp (Lp ℂ 2 ν) 2 μ`, and `K(F)=tensorToLp μ⁻¹(J(F)) ∈
Completion(Lp ℂ 2 μ⊗Lp ℂ 2 ν)`. `J(F)(x)=S_F(x)` for `μ`-almost every `x`, without local
compactness of either factor. -/
theorem productToIteratedLp_ae_eq (F : C_c(X × Y, ℂ)) :
    productToIteratedLp μ ν F =ᵐ[μ] sectionRightLp ν F := by
  change compactSupportInclusion (H := Lp ℂ 2 ν) μ (sectionToLp ν F) =ᵐ[μ] sectionRightLp ν F
  filter_upwards [compactSupportInclusion_ae_eq (H := Lp ℂ 2 ν) μ (sectionToLp ν F)] with x hx
  simpa only [sectionToLp_apply] using hx

/-- **Iterated section norm equals the Borel Radon L² norm.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for `J(F)=i_μ(x ↦ i_ν(F(x,·)))`, `‖J(F)‖²=‖i_R F‖²`. -/
theorem norm_productToIteratedLp_sq (F : C_c(X × Y, ℂ)) :
    ‖productToIteratedLp μ ν F‖ ^ 2 = ‖compactSupportInclusion (Measure.radonProd μ ν) F‖ ^ 2 := by
  change ‖compactSupportInclusion μ (sectionToLp ν F)‖ ^ 2 = _
  rw [norm_compactSupportInclusion_sq, norm_compactSupportInclusion_sq]
  calc
    (∫ x : X, ‖sectionToLp ν F x‖ ^ 2 ∂μ) = ∫ x : X, ∫ y : Y, ‖F (x, y)‖ ^ 2 ∂ν ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => norm_sectionRightLp_sq ν F x)
    _ = ∫ z : X × Y, ‖F z‖ ^ 2 ∂(Measure.radonProd μ ν) := by
      simpa only [CompactlySupportedContinuousMap.normSq_apply] using
        (Measure.integral_radonProd μ ν (normSq F)).symm

/-- **Factor-tensor representative of a compact-support product function.** Let `X,Y` be
Hausdorff Borel spaces, `μ,ν` regular measures and `F∈C_c(X×Y,ℂ)`. Write `S_F(x)=i_ν(y ↦
F(x,y))`, `J(F)=i_μ(S_F) ∈ Lp (Lp ℂ 2 ν) 2 μ`, and `K(F)=tensorToLp μ⁻¹(J(F)) ∈
Completion(Lp ℂ 2 μ⊗Lp ℂ 2 ν)`. `compactProductTensorRepresentative μ ν F=K(F)` is
obtained by applying the inverse scalar-to-vector one-measure tensor unitary to `J(F)`. -/
def compactProductTensorRepresentative :
    C_c(X × Y, ℂ) →ₗ[ℂ] UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :=
  (L2.tensorToLp (𝕜 := ℂ) (H := Lp ℂ 2 ν) μ).symm.toLinearMap.comp (productToIteratedLp μ ν)

/-- **Squared norm of a compact product's factor-tensor representative.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for `K(F)=tensorToLp μ⁻¹(i_μ(x ↦ i_ν(F(x,·))))`,
`‖K(F)‖²=‖i_R F‖²`. -/
theorem norm_compactProductTensorRepresentative_sq (F : C_c(X × Y, ℂ)) :
    ‖compactProductTensorRepresentative μ ν F‖ ^ 2 =
      ‖compactSupportInclusion (Measure.radonProd μ ν) F‖ ^ 2 := by
  change ‖(L2.tensorToLp (𝕜 := ℂ) (H := Lp ℂ 2 ν) μ).symm (productToIteratedLp μ ν F)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map]
  exact norm_productToIteratedLp_sq μ ν F

/-- **Norm of a compact product's factor-tensor representative.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for the factor-tensor representative `K(F)` of
`F∈C_c(X×Y,ℂ)`, `‖K(F)‖=‖i_R F‖`. -/
theorem norm_compactProductTensorRepresentative (F : C_c(X × Y, ℂ)) :
    ‖compactProductTensorRepresentative μ ν F‖ =
      ‖compactSupportInclusion (Measure.radonProd μ ν) F‖ := by
  simpa only [Real.sqrt_sq (norm_nonneg (compactProductTensorRepresentative μ ν F)),
    Real.sqrt_sq (norm_nonneg (compactSupportInclusion (Measure.radonProd μ ν) F))] using
    congrArg Real.sqrt (norm_compactProductTensorRepresentative_sq μ ν F)

end MeasureTheory.HaarL2

end
