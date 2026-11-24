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
# The actual full scalar L2 tensor unitary for the Borel Radon product

Compact-support product functions have actual norm-preserving representatives
in the full stock factor tensor, obtained from their Lp-valued sections and
the proved one-measure tensor unitary. Dense original compact-support product
vectors extend these representatives isometrically to the entire product Lp.
The original pure formulas and dense factor tensors prove the inverse law,
so the computed forward embedding is genuinely surjective and gives the
strict full scalar product L2 unitary. No countability, s-finiteness, product
Borel equality, supplied norm identity or chosen output unitary is an input.
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

/-- The Borel measurable space of the literal product used by the actual full scalar L2 unitary. -/
local instance instUnitaryProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instUnitaryProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

omit [LocallyCompactSpace X] [LocallyCompactSpace Y] in
/-- The actual section representative of a compact-support pure product is the original full pure tensor. -/
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

/-- The computed isometric reverse map from the entire original Borel product L2 into the full stock tensor. -/
def radonProductTensorInverseEmbedding :
    Lp ℂ 2 (Measure.radonProd μ ν) →ₗᵢ[ℂ]
      UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :=
  (compactProductTensorRepresentative μ ν).extendOfIsometry
    (e := compactSupportInclusion (H := ℂ) (Measure.radonProd μ ν))
    (denseRange_compactSupportInclusion (H := ℂ) (Measure.radonProd μ ν))
    (norm_compactProductTensorRepresentative μ ν)

/-- The reverse extension retains every actual compact-support product L2 representative. -/
@[simp]
theorem radonProductTensorInverseEmbedding_apply_cc (F : C_c(X × Y, ℂ)) :
    radonProductTensorInverseEmbedding μ ν (compactSupportInclusion (Measure.radonProd μ ν) F) =
      compactProductTensorRepresentative μ ν F := by
  simp only [radonProductTensorInverseEmbedding, LinearMap.extendOfIsometry_eq]

/-- The computed reverse and forward isometries have their actual inverse law on the entire stock tensor. -/
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

/-- The computed full tensor embedding is genuinely onto the entire original Borel product L2 space. -/
theorem surjective_radonProductTensorEmbedding :
    Function.Surjective (radonProductTensorEmbedding μ ν) := by
  intro ξ
  refine ⟨radonProductTensorInverseEmbedding μ ν ξ, ?_⟩
  apply (radonProductTensorInverseEmbedding μ ν).injective
  exact radonProductTensorInverseEmbedding_embedding μ ν (radonProductTensorInverseEmbedding μ ν ξ)

/-- The computed full tensor embedding has genuine dense range in the original product L2 space. -/
theorem denseRange_radonProductTensorEmbedding : DenseRange (radonProductTensorEmbedding μ ν) :=
  (surjective_radonProductTensorEmbedding μ ν).denseRange

/-- The actual full scalar L2 tensor unitary for the original Borel Radon product. -/
def radonProductTensorUnitary :
    UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (Measure.radonProd μ ν) :=
  LinearIsometryEquiv.ofSurjective (radonProductTensorEmbedding μ ν)
    (surjective_radonProductTensorEmbedding μ ν)

/-- The actual product unitary retains the original compact-support pure values almost everywhere. -/
theorem radonProductTensorUnitary_tmul_ae (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) :
    radonProductTensorUnitary μ ν
        (((compactSupportInclusion μ f) ⊗ₜ[ℂ] (compactSupportInclusion ν g) :
          (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
            UniformSpace.Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) =ᵐ[Measure.radonProd μ ν]
      fun z => f z.1 * g z.2 :=
  radonProductTensorEmbedding_tmul_ae μ ν f g

end

end MeasureTheory.HaarL2
