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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.RadonProduct.Completion
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.RadonProduct.Sections

/-!
# Full scalar L² tensor unitary for a Borel Radon product

For locally compact Hausdorff Borel spaces with regular measures, the isometric extension `E :
Completion(L²(μ)⊗L²(ν)) → L²(R)` is surjective, where `R=radonProd μ ν`.

Its inverse is the extension of the factor-tensor representatives of compact-support product
functions. Thus the full scalar tensor unitary sends `i_μ f⊗i_ν g` to the class of `f(x)g(y)`.
No countability, s-finiteness or equality of factor and product Borel measurable structures is
assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped CompactlySupported TensorProduct

namespace MeasureTheory.HaarL2

noncomputable section

universe uX uY

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]

/-- **Borel product structure for the scalar Radon tensor unitary.** For topological `X,Y`,
the product carrier uses `borel(X×Y)`. -/
local instance instUnitaryProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instUnitaryProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

omit [LocallyCompactSpace X] [LocallyCompactSpace Y] in
/-- **Factor-tensor representative of a compact-support pure product.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. the representative `K(f⊠g)` obtained from the L²-valued
sections equals the completed tensor `i_μ f⊗i_ν g`. -/
theorem compactProductTensorRepresentative_mulProd (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    compactProductTensorRepresentative μ ν (CompactlySupportedContinuousMap.mulProd f g) =
      (((compactSupportInclusion μ f) ⊗ₜ[ℂ] (compactSupportInclusion ν g) :
        (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
          UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) := by
  apply (L2.tensorToLp (𝕜 := ℂ) (H := Lp ℂ 2 ν) μ).injective
  change (L2.tensorToLp μ)
      ((L2.tensorToLp μ).symm
        (productToIteratedLp μ ν (CompactlySupportedContinuousMap.mulProd f g))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply Lp.ext
  filter_upwards [productToIteratedLp_ae_eq μ ν (CompactlySupportedContinuousMap.mulProd f g),
    L2.tensorToLp_tmul_ae μ (compactSupportInclusion μ f) (compactSupportInclusion ν g),
    compactSupportInclusion_ae_eq μ f] with x hleft hright hf
  rw [hleft, hright, hf]
  exact CompactlySupportedContinuousMap.sectionRightLp_mulProd ν f g x

/-- **Reverse isometric extension from Radon L² to the factor tensor.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `radonProductTensorInverseEmbedding μ ν : Lp ℂ 2 R →ₗᵢ[ℂ]
T` extends the compact product representative `i_R F ↦ K(F)`. -/
def radonProductTensorInverseEmbedding :
    Lp ℂ 2 (Measure.radonProd μ ν) →ₗᵢ[ℂ]
      UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :=
  (compactProductTensorRepresentative μ ν).extendOfIsometry
    (e := compactSupportInclusion (H := ℂ) (Measure.radonProd μ ν))
    (denseRange_compactSupportInclusion (H := ℂ) (Measure.radonProd μ ν))
    (norm_compactProductTensorRepresentative μ ν)

/-- **Compact-support value of the inverse Radon tensor embedding.** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for `F∈C_c(X×Y,ℂ)`, `radonProductTensorInverseEmbedding μ
ν (i_R F)=K(F)`, where `K(F)` is the factor-tensor representative of its L²-valued
sections. -/
@[simp]
theorem radonProductTensorInverseEmbedding_apply_cc (F : C_c(X × Y, ℂ)) :
    radonProductTensorInverseEmbedding μ ν (compactSupportInclusion (Measure.radonProd μ ν) F) =
      compactProductTensorRepresentative μ ν F := by
  simp only [radonProductTensorInverseEmbedding, LinearMap.extendOfIsometry_eq]

/-- **Inverse embedding recovers every completed factor tensor.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. for `z∈T`, `radonProductTensorInverseEmbedding μ ν
(radonProductTensorEmbedding μ ν z)=z`. -/
theorem radonProductTensorInverseEmbedding_embedding
    (z : UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) :
    radonProductTensorInverseEmbedding μ ν (radonProductTensorEmbedding μ ν z) = z := by
  have hCore (t : C_c(X, ℂ) ⊗[ℂ] C_c(Y, ℂ)) :
      radonProductTensorInverseEmbedding μ ν
        (radonProductTensorEmbedding μ ν (compactSupportFactorTensorCompletion μ ν t)) =
      compactSupportFactorTensorCompletion μ ν t := by
    induction t using TensorProduct.inductionOn with
    | tmul f g =>
      rw [compactSupportFactorTensorCompletion_apply, compactSupportFactorTensor, TensorProduct.map_tmul]
      rw [radonProductTensorEmbedding_tmul, radonProductTensorInverseEmbedding_apply_cc,
        compactProductTensorRepresentative_mulProd]
    | add t u ht hu => simp only [map_add, ht, hu]
  exact (denseRange_compactSupportFactorTensorCompletion μ ν).induction
    (fun x hx => by
      obtain ⟨t, rfl⟩ := hx
      exact hCore t)
    (isClosed_eq
      ((radonProductTensorInverseEmbedding μ ν).continuous.comp
        (radonProductTensorEmbedding μ ν).continuous) continuous_id) z

/-- **Surjectivity of the full Radon tensor embedding.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `radonProductTensorEmbedding μ ν : T → Lp ℂ 2 R` is
surjective. -/
theorem surjective_radonProductTensorEmbedding :
    Function.Surjective (radonProductTensorEmbedding μ ν) := by
  intro ξ
  refine ⟨radonProductTensorInverseEmbedding μ ν ξ, ?_⟩
  apply (radonProductTensorInverseEmbedding μ ν).injective
  exact radonProductTensorInverseEmbedding_embedding μ ν (radonProductTensorInverseEmbedding μ ν ξ)

/-- **Dense range of the full Radon tensor embedding.** Let `X,Y` be locally compact Hausdorff
Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on `borel(X×Y)`,
`i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)`,
`A(z)` for the algebraic factor tensor inclusion into `T`, and `F(f⊗g)=i_R((x,y) ↦
f(x)g(y))`. the range of `radonProductTensorEmbedding μ ν` is norm-dense in `Lp ℂ 2 R`. -/
theorem denseRange_radonProductTensorEmbedding : DenseRange (radonProductTensorEmbedding μ ν) :=
  (surjective_radonProductTensorEmbedding μ ν).denseRange

/-- **Linear isometric equivalence of full scalar tensor and Radon L².** Let `X,Y` be locally
compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `radonProductTensorUnitary μ ν : T ≃ₗᵢ[ℂ] Lp ℂ 2 R` has
forward function the completed product embedding and inverse the section-representative
extension. -/
def radonProductTensorUnitary :
    UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (Measure.radonProd μ ν) :=
  LinearIsometryEquiv.ofSurjective (radonProductTensorEmbedding μ ν)
    (surjective_radonProductTensorEmbedding μ ν)

/-- **Almost-everywhere pure product formula of the scalar tensor unitary.** Let `X,Y` be
locally compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν`
on `borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ
⊗[ℂ] Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. `radonProductTensorUnitary μ ν (i_μ f⊗i_ν
g)(x,y)=f(x)g(y)` for `R`-almost every `(x,y)`. -/
theorem radonProductTensorUnitary_tmul_ae (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    radonProductTensorUnitary μ ν
        (((compactSupportInclusion μ f) ⊗ₜ[ℂ] (compactSupportInclusion ν g) :
          (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
            UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) =ᵐ[Measure.radonProd μ ν]
      fun z => f z.1 * g z.2 :=
  radonProductTensorEmbedding_tmul_ae μ ν f g

end

end MeasureTheory.HaarL2
