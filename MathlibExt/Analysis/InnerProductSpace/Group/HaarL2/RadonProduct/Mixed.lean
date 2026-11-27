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

public import MathlibExt.Analysis.Normed.Operator.CompletionEquiv
public import MathlibExt.Analysis.InnerProductSpace.TensorProduct.InsideCompletion
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.RadonProduct.Hilbert

/-!
# Mixed scalar and Hilbert-valued Radon tensor models

For measures on measurable spaces and a complete complex Hilbert space, canonical completed
tensor congruence and rebracketing give `C : Completion(L²(μ)⊗L²(H,ν)) ≃
Completion(Completion(L²(μ)⊗L²(ν))⊗H)`. It sends `f⊗U_ν(g⊗ξ)` to `(f⊗g)⊗ξ`.

For locally compact Hausdorff Borel factors with regular measures, composition with the
Hilbert-amplified Radon unitary gives the mixed product unitary into `Lp H 2 R`. On
compact-support factors, its value is `f(x)g(y) • ξ` almost everywhere. The preliminary
completion maps preserve the Hilbert tensor norms, and do not replace them by another product
norm.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory UniformSpace
open scoped CompactlySupported TensorProduct

namespace MeasureTheory.HaarL2

noncomputable section


universe uX uY uH

section MixedComparison

variable {X : Type uX} [MeasurableSpace X]
variable {Y : Type uY} [MeasurableSpace Y]
variable (μ : Measure X) (ν : Measure Y)
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Removing an inner right-factor completion inside a completed tensor.** Let `X,Y` be
measurable spaces with measures `μ,ν`, `A=Lp ℂ 2 μ`, `B=Lp ℂ 2 ν`, and `H` a complex
normed inner-product space, possibly incomplete. the canonical linear map
`Completion(A⊗Completion(B⊗H)) → Completion(A⊗(B⊗H))` sends `f⊗(g⊗ξ)` to the same
algebraic tensor in the outer completion. -/
private def radonProductMixedTensorRightMap :
    Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Completion ((Lp ℂ 2 ν) ⊗[ℂ] H))) →ₗ[ℂ]
      Completion ((Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H)) :=
  (TensorProduct.completionRightTensorUnitary (𝕜 := ℂ)
    (E := Lp ℂ 2 μ) (F := (Lp ℂ 2 ν) ⊗[ℂ] H)).symm.toLinearMap

/-- **Associating a completed three-factor Hilbert tensor.** Let `X,Y` be measurable spaces
with measures `μ,ν`, `A=Lp ℂ 2 μ`, `B=Lp ℂ 2 ν`, and `H` a complex normed inner-product
space, possibly incomplete. the completed rebracketing map sends `f⊗(g⊗ξ)` to `(f⊗g)⊗ξ`,
from `Completion(A⊗(B⊗H))` to `Completion((A⊗B)⊗H)`. -/
private def radonProductMixedTensorAssocMap :
    Completion ((Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H)) →ₗ[ℂ]
      Completion (((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ⊗[ℂ] H) :=
  (LinearIsometryEquiv.completion
    (TensorProduct.assocIsometry ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν) H)).symm.toLinearMap

/-- **Inserting a completion of the scalar pair inside an outer completion.** Let `X,Y` be
measurable spaces with measures `μ,ν`, `A=Lp ℂ 2 μ`, `B=Lp ℂ 2 ν`, and `H` a complex
normed inner-product space, possibly incomplete. the canonical map `Completion((A⊗B)⊗H) →
Completion(Completion(A⊗B)⊗H)` sends `(f⊗g)⊗ξ` to its completed scalar-pair tensor with
`ξ`. -/
private def radonProductMixedTensorLeftMap :
    Completion (((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ⊗[ℂ] H) →ₗ[ℂ]
      Completion ((Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H) :=
  (TensorProduct.completionLeftTensorUnitary (𝕜 := ℂ)
    (E := (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) (F := H)).toLinearMap

/-- **Pure tensor value of removing the right inner completion.** Let `X,Y` be measurable
spaces with measures `μ,ν`, `A=Lp ℂ 2 μ`, `B=Lp ℂ 2 ν`, and `H` a complex normed
inner-product space, possibly incomplete. for `f∈A`, `g∈B`, `ξ∈H`, the right map sends the
completed pure tensor `f⊗(g⊗ξ)` to its image in `Completion(A⊗(B⊗H))`. -/
private theorem radonProductMixedTensorRightMap_tmul (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) (ξ : H) :
    radonProductMixedTensorRightMap μ ν
        ((f ⊗ₜ[ℂ]
          ((g ⊗ₜ[ℂ] ξ : (Lp ℂ 2 ν) ⊗[ℂ] H) : Completion ((Lp ℂ 2 ν) ⊗[ℂ] H)) :
            (Lp ℂ 2 μ) ⊗[ℂ] (Completion ((Lp ℂ 2 ν) ⊗[ℂ] H))) :
              Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Completion ((Lp ℂ 2 ν) ⊗[ℂ] H)))) =
      ((f ⊗ₜ[ℂ] (g ⊗ₜ[ℂ] ξ) : (Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H)) :
        Completion ((Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H))) := by
  let R := TensorProduct.completionRightTensorUnitary (𝕜 := ℂ)
    (E := Lp ℂ 2 μ) (F := (Lp ℂ 2 ν) ⊗[ℂ] H)
  change R.symm _ = _
  apply R.injective
  rw [R.apply_symm_apply]
  symm
  change TensorProduct.completionRightTensorEmbedding (𝕜 := ℂ)
    ((f ⊗ₜ[ℂ] (g ⊗ₜ[ℂ] ξ) : (Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H)) :
      Completion ((Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H))) = _
  exact TensorProduct.completionRightTensorEmbedding_tmul f (g ⊗ₜ[ℂ] ξ)

/-- **Pure value of completed tensor rebracketing.** Let `X,Y` be measurable spaces with
measures `μ,ν`, `A=Lp ℂ 2 μ`, `B=Lp ℂ 2 ν`, and `H` a complex normed inner-product space,
possibly incomplete. for `f∈A`, `g∈B`, `ξ∈H`, the association map sends `f⊗(g⊗ξ)` to
`(f⊗g)⊗ξ`. -/
private theorem radonProductMixedTensorAssocMap_tmul (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) (ξ : H) :
    radonProductMixedTensorAssocMap μ ν
        ((f ⊗ₜ[ℂ] (g ⊗ₜ[ℂ] ξ) : (Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H)) :
          Completion ((Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H))) =
      (((f ⊗ₜ[ℂ] g) ⊗ₜ[ℂ] ξ : ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ⊗[ℂ] H) :
        Completion (((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ⊗[ℂ] H)) := by
  change (LinearIsometryEquiv.completion
    (TensorProduct.assocIsometry ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν) H)).symm
    ((f ⊗ₜ[ℂ] (g ⊗ₜ[ℂ] ξ) : (Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H)) :
      Completion ((Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H))) = _
  rw [LinearIsometryEquiv.completion_symm_apply_coe]
  simp only [TensorProduct.assocIsometry_symm_apply, TensorProduct.assoc_symm_tmul]

/-- **Pure value of inserting the scalar-pair completion.** Let `X,Y` be measurable spaces
with measures `μ,ν`, `A=Lp ℂ 2 μ`, `B=Lp ℂ 2 ν`, and `H` a complex normed inner-product
space, possibly incomplete. for `f∈A`, `g∈B`, `ξ∈H`, the left map sends `(f⊗g)⊗ξ` to
`(ι_(A⊗B)(f⊗g))⊗ξ` in the completed outer tensor. -/
private theorem radonProductMixedTensorLeftMap_tmul (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) (ξ : H) :
    radonProductMixedTensorLeftMap μ ν
        (((f ⊗ₜ[ℂ] g) ⊗ₜ[ℂ] ξ : ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ⊗[ℂ] H) :
          Completion (((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ⊗[ℂ] H)) =
      ((((f ⊗ₜ[ℂ] g : (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
        Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗ₜ[ℂ] ξ) :
          Completion ((Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H)) := by
  change TensorProduct.completionLeftTensorEmbedding (𝕜 := ℂ)
    (((f ⊗ₜ[ℂ] g) ⊗ₜ[ℂ] ξ : ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ⊗[ℂ] H) :
      Completion (((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ⊗[ℂ] H)) = _
  exact TensorProduct.completionLeftTensorEmbedding_tmul (f ⊗ₜ[ℂ] g) ξ

variable [CompleteSpace H]

/-- **Mixed tensor congruence using the inverse vector-L² comparison.** Let `X,Y` be
measurable spaces with measures `μ,ν`, `A=Lp ℂ 2 μ`, `B=Lp ℂ 2 ν`, and `H` a complex
normed inner-product space, possibly incomplete. Assume `H` is complete and let `U_ν :
Completion(B⊗H) ≃ₗᵢ[ℂ] Lp H 2 ν` be the one-measure tensor unitary. Let `C` denote the
isometric comparison `Completion(A⊗Lp H 2 ν) → Completion(Completion(A⊗B)⊗H)`. the
congruence map is the completion of `I_A⊗U_ν⁻¹`, from `Completion(A⊗Lp H 2 ν)` to
`Completion(A⊗Completion(B⊗H))`. -/
private def radonProductMixedTensorCongruenceMap :
    Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) →ₗ[ℂ]
      Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Completion ((Lp ℂ 2 ν) ⊗[ℂ] H))) :=
  (LinearIsometryEquiv.completion
    (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ))
      (L2.tensorToLp (𝕜 := ℂ) (H := H) ν).symm)).toLinearMap

/-- **Pure value of the vector-L² inverse tensor congruence.** Let `X,Y` be measurable spaces
with measures `μ,ν`, `A=Lp ℂ 2 μ`, `B=Lp ℂ 2 ν`, and `H` a complex normed inner-product
space, possibly incomplete. Assume `H` is complete and let `U_ν : Completion(B⊗H) ≃ₗᵢ[ℂ]
Lp H 2 ν` be the one-measure tensor unitary. Let `C` denote the isometric comparison
`Completion(A⊗Lp H 2 ν) → Completion(Completion(A⊗B)⊗H)`. for `f∈A`, `g∈B`, `ξ∈H`, the
congruence sends `f⊗U_ν(g⊗ξ)` to `f⊗(g⊗ξ)` with the inner right tensor completed. -/
private theorem radonProductMixedTensorCongruenceMap_tmul (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) (ξ : H) :
    radonProductMixedTensorCongruenceMap μ ν
        ((f ⊗ₜ[ℂ] L2.tensorToLp ν
          ((g ⊗ₜ[ℂ] ξ : (Lp ℂ 2 ν) ⊗[ℂ] H) : Completion ((Lp ℂ 2 ν) ⊗[ℂ] H)) :
            (Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) : Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν))) =
      ((f ⊗ₜ[ℂ]
        ((g ⊗ₜ[ℂ] ξ : (Lp ℂ 2 ν) ⊗[ℂ] H) : Completion ((Lp ℂ 2 ν) ⊗[ℂ] H)) :
          (Lp ℂ 2 μ) ⊗[ℂ] (Completion ((Lp ℂ 2 ν) ⊗[ℂ] H))) :
            Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Completion ((Lp ℂ 2 ν) ⊗[ℂ] H)))) := by
  change (LinearIsometryEquiv.completion
    (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ))
      (L2.tensorToLp (𝕜 := ℂ) (H := H) ν).symm))
    ((f ⊗ₜ[ℂ] L2.tensorToLp ν
      ((g ⊗ₜ[ℂ] ξ : (Lp ℂ 2 ν) ⊗[ℂ] H) : Completion ((Lp ℂ 2 ν) ⊗[ℂ] H)) :
        (Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) : Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν))) = _
  rw [LinearIsometryEquiv.completion_apply_coe]
  change ((f ⊗ₜ[ℂ] (L2.tensorToLp (𝕜 := ℂ) (H := H) ν).symm
      (L2.tensorToLp ν
        ((g ⊗ₜ[ℂ] ξ : (Lp ℂ 2 ν) ⊗[ℂ] H) : Completion ((Lp ℂ 2 ν) ⊗[ℂ] H))) :
          (Lp ℂ 2 μ) ⊗[ℂ] (Completion ((Lp ℂ 2 ν) ⊗[ℂ] H))) :
            Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Completion ((Lp ℂ 2 ν) ⊗[ℂ] H)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

/-- **Isometric comparison of mixed L² tensor arrangements.** Let `X,Y` be measurable spaces
with measures `μ,ν`, `A=Lp ℂ 2 μ`, `B=Lp ℂ 2 ν`, and `H` a complex normed inner-product
space, possibly incomplete. Assume `H` is complete and let `U_ν : Completion(B⊗H) ≃ₗᵢ[ℂ]
Lp H 2 ν` be the one-measure tensor unitary. Let `C` denote the isometric comparison
`Completion(A⊗Lp H 2 ν) → Completion(Completion(A⊗B)⊗H)`.
`radonProductMixedTensorComparison μ ν=C` is the composite of inverse vector-L²
congruence, inner-completion removal, rebracketing and insertion of the scalar-pair
completion. -/
def radonProductMixedTensorComparison :
    Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) ≃ₗᵢ[ℂ]
      Completion ((Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H) :=
  (((LinearIsometryEquiv.completion
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ))
        (L2.tensorToLp (𝕜 := ℂ) (H := H) ν).symm)).trans
      (TensorProduct.completionRightTensorUnitary (𝕜 := ℂ)
        (E := Lp ℂ 2 μ) (F := (Lp ℂ 2 ν) ⊗[ℂ] H)).symm).trans
      (LinearIsometryEquiv.completion
        (TensorProduct.assocIsometry ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν) H)).symm).trans
      (TensorProduct.completionLeftTensorUnitary (𝕜 := ℂ)
        (E := (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) (F := H))

/-- **Four-map composition of the mixed tensor comparison.** Let `X,Y` be measurable spaces
with measures `μ,ν`, `A=Lp ℂ 2 μ`, `B=Lp ℂ 2 ν`, and `H` a complex normed inner-product
space, possibly incomplete. Assume `H` is complete and let `U_ν : Completion(B⊗H) ≃ₗᵢ[ℂ]
Lp H 2 ν` be the one-measure tensor unitary. Let `C` denote the isometric comparison
`Completion(A⊗Lp H 2 ν) → Completion(Completion(A⊗B)⊗H)`. `C=L∘A_s∘R_s∘G_s`, where
`G_s=Completion(I_A⊗U_ν⁻¹)`, `R_s` removes the inner right completion, `A_s` rebrackets
and `L` inserts the scalar-pair completion. -/
private theorem radonProductMixedTensorComparison_apply
    (z : Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν))) :
    radonProductMixedTensorComparison (H := H) μ ν z =
      radonProductMixedTensorLeftMap μ ν
        (radonProductMixedTensorAssocMap μ ν
          (radonProductMixedTensorRightMap μ ν (radonProductMixedTensorCongruenceMap μ ν z))) := rfl

/-- **Pure scalar-vector value of the mixed tensor comparison.** Let `X,Y` be measurable
spaces with measures `μ,ν`, `A=Lp ℂ 2 μ`, `B=Lp ℂ 2 ν`, and `H` a complex normed
inner-product space, possibly incomplete. Assume `H` is complete and let `U_ν :
Completion(B⊗H) ≃ₗᵢ[ℂ] Lp H 2 ν` be the one-measure tensor unitary. Let `C` denote the
isometric comparison `Completion(A⊗Lp H 2 ν) → Completion(Completion(A⊗B)⊗H)`. for `f∈A`,
`g∈B`, `ξ∈H`, `C(f⊗U_ν(g⊗ξ))=(ι_(A⊗B)(f⊗g))⊗ξ` in the completed outer tensor. -/
theorem radonProductMixedTensorComparison_tmul (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) (ξ : H) :
    radonProductMixedTensorComparison (H := H) μ ν
        ((f ⊗ₜ[ℂ] L2.tensorToLp ν
          ((g ⊗ₜ[ℂ] ξ : (Lp ℂ 2 ν) ⊗[ℂ] H) : Completion ((Lp ℂ 2 ν) ⊗[ℂ] H)) :
            (Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) : Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν))) =
      ((((f ⊗ₜ[ℂ] g : (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
        Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗ₜ[ℂ] ξ) :
          Completion ((Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H)) := by
  rw [radonProductMixedTensorComparison_apply, radonProductMixedTensorCongruenceMap_tmul,
    radonProductMixedTensorRightMap_tmul, radonProductMixedTensorAssocMap_tmul,
    radonProductMixedTensorLeftMap_tmul]

end MixedComparison

section OriginalProduct

variable {X : Type uX} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) (ν : Measure Y) [μ.Regular] [ν.Regular]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Borel topological product for a mixed Radon tensor model.** For topological `X,Y`, use
`borel(X×Y)` as the product measurable carrier. -/
local instance instMixedProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instMixedProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- **Mixed L² tensor unitary onto Hilbert-valued Radon product functions.** Let `X,Y` be
locally compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν`
on `borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ
⊗[ℂ] Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space, `U_R : T
≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor unitary, and `U_H : Completion(T⊗H) ≃ₗᵢ[ℂ] Lp H 2
R` its Hilbert amplification. Let `U_ν : Completion(Lp ℂ 2 ν⊗H) ≃ₗᵢ[ℂ] Lp H 2 ν` be the
one-measure tensor unitary and `C` the isometric comparison from `Completion(Lp ℂ 2 μ⊗Lp H
2 ν)` to `Completion(T⊗H)`. `radonProductMixedTensorUnitary μ ν=U_H∘C`, a linear isometric
equivalence from the mixed tensor completion to `Lp H 2 R`. -/
def radonProductMixedTensorUnitary :
    Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) ≃ₗᵢ[ℂ] Lp H 2 (Measure.radonProd μ ν) :=
  (radonProductMixedTensorComparison (H := H) μ ν).trans (radonProductTensorHilbertUnitary (H := H) μ ν)

/-- **Linear-map factorization of the mixed Radon unitary.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space, `U_R : T
≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor unitary, and `U_H : Completion(T⊗H) ≃ₗᵢ[ℂ] Lp H 2
R` its Hilbert amplification. Let `U_ν : Completion(Lp ℂ 2 ν⊗H) ≃ₗᵢ[ℂ] Lp H 2 ν` be the
one-measure tensor unitary and `C` the isometric comparison from `Completion(Lp ℂ 2 μ⊗Lp H
2 ν)` to `Completion(T⊗H)`. the underlying linear map is `U_H∘L∘A_s∘R_s∘G_s`, where the
four maps compose to `C` by inverse vector-L² congruence and completed rebracketing. -/
theorem radonProductMixedTensorUnitary_toLinearMap :
    (radonProductMixedTensorUnitary (H := H) μ ν).toLinearMap =
      (radonProductTensorHilbertUnitary (H := H) μ ν).toLinearMap.comp
        ((TensorProduct.completionLeftTensorUnitary (𝕜 := ℂ)
          (E := (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) (F := H)).toLinearMap.comp
          (((TensorProduct.assocIsometry ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν) H).symm.toLinearIsometry.completion).toLinearMap.comp
            ((TensorProduct.completionRightTensorUnitary (𝕜 := ℂ)
              (E := Lp ℂ 2 μ) (F := (Lp ℂ 2 ν) ⊗[ℂ] H)).symm.toLinearMap.comp
              ((TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ))
                (L2.tensorToLp (𝕜 := ℂ) (H := H) ν).symm).toLinearIsometry.completion).toLinearMap))) := rfl

/-- **Full scalar-factor pure value of the mixed Radon unitary.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space, `U_R : T
≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor unitary, and `U_H : Completion(T⊗H) ≃ₗᵢ[ℂ] Lp H 2
R` its Hilbert amplification. Let `U_ν : Completion(Lp ℂ 2 ν⊗H) ≃ₗᵢ[ℂ] Lp H 2 ν` be the
one-measure tensor unitary and `C` the isometric comparison from `Completion(Lp ℂ 2 μ⊗Lp H
2 ν)` to `Completion(T⊗H)`. for `f∈Lp ℂ 2 μ`, `g∈Lp ℂ 2 ν`, `ξ∈H`,
`U_mix(f⊗U_ν(g⊗ξ))=U_H((f⊗g)⊗ξ)`, where `U_mix=U_H∘C`. -/
theorem radonProductMixedTensorUnitary_tmul (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) (ξ : H) :
    radonProductMixedTensorUnitary (H := H) μ ν
        ((f ⊗ₜ[ℂ] L2.tensorToLp ν
          ((g ⊗ₜ[ℂ] ξ : (Lp ℂ 2 ν) ⊗[ℂ] H) : Completion ((Lp ℂ 2 ν) ⊗[ℂ] H)) :
            (Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) : Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν))) =
      radonProductTensorHilbertUnitary (H := H) μ ν
        ((((f ⊗ₜ[ℂ] g : (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) :
          Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗ₜ[ℂ] ξ) :
            Completion ((Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H)) := by
  change radonProductTensorHilbertUnitary μ ν (radonProductMixedTensorComparison μ ν _) = _
  rw [radonProductMixedTensorComparison_tmul]

/-- **Compact-support mixed tensor value on the Radon product.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space, `U_R : T
≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor unitary, and `U_H : Completion(T⊗H) ≃ₗᵢ[ℂ] Lp H 2
R` its Hilbert amplification. Let `U_ν : Completion(Lp ℂ 2 ν⊗H) ≃ₗᵢ[ℂ] Lp H 2 ν` be the
one-measure tensor unitary and `C` the isometric comparison from `Completion(Lp ℂ 2 μ⊗Lp H
2 ν)` to `Completion(T⊗H)`. for compact-support scalar `f,g` and `ξ∈H`, `U_mix(i_μ
f⊗U_ν(i_ν g⊗ξ))(x,y)=f(x)g(y) • ξ` almost everywhere. -/
theorem radonProductMixedTensorUnitary_compact_tmul_ae
    (f : C_c(X, ℂ)) (g : C_c(Y, ℂ)) (ξ : H) :
    radonProductMixedTensorUnitary (H := H) μ ν
        (((compactSupportInclusion μ f) ⊗ₜ[ℂ] L2.tensorToLp ν
          (((compactSupportInclusion ν g) ⊗ₜ[ℂ] ξ : (Lp ℂ 2 ν) ⊗[ℂ] H) :
            Completion ((Lp ℂ 2 ν) ⊗[ℂ] H)) : (Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) :
              Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν))) =ᵐ[Measure.radonProd μ ν]
      fun z => (f z.1 * g z.2) • ξ := by
  rw [radonProductMixedTensorUnitary_tmul]
  exact radonProductTensorHilbertUnitary_compact_tmul_ae μ ν f g ξ

/-- **Mixed tensor unitary into the product compact-support L² completion.** Let `X,Y` be
locally compact Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν`
on `borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ
⊗[ℂ] Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space, `U_R : T
≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor unitary, and `U_H : Completion(T⊗H) ≃ₗᵢ[ℂ] Lp H 2
R` its Hilbert amplification. Let `U_ν : Completion(Lp ℂ 2 ν⊗H) ≃ₗᵢ[ℂ] Lp H 2 ν` be the
one-measure tensor unitary and `C` the isometric comparison from `Completion(Lp ℂ 2 μ⊗Lp H
2 ν)` to `Completion(T⊗H)`. `radonProductMixedCompletionUnitary μ ν=J_R⁻¹∘U_H∘C`, with
`J_R : CompletionCore(H,R) ≃ Lp H 2 R` the compact-support completion comparison. -/
def radonProductMixedCompletionUnitary :
    Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) ≃ₗᵢ[ℂ]
      CompletionCore (H := H) (Measure.radonProd μ ν) :=
  (radonProductMixedTensorUnitary (H := H) μ ν).trans
    (completionToLp (H := H) (Measure.radonProd μ ν)).symm

/-- **L² value of the mixed compact-support completion unitary.** Let `X,Y` be locally compact
Hausdorff Borel spaces and `μ,ν` regular measures. Write `R=radonProd μ ν` on
`borel(X×Y)`, `i_μ,i_ν,i_R` for compact-support L² inclusions, `T=Completion(Lp ℂ 2 μ ⊗[ℂ]
Lp ℂ 2 ν)`, `A(z)` for the algebraic factor tensor inclusion into `T`, and
`F(f⊗g)=i_R((x,y) ↦ f(x)g(y))`. Let `H` be a complete complex Hilbert space, `U_R : T
≃ₗᵢ[ℂ] Lp ℂ 2 R` the scalar Radon tensor unitary, and `U_H : Completion(T⊗H) ≃ₗᵢ[ℂ] Lp H 2
R` its Hilbert amplification. Let `U_ν : Completion(Lp ℂ 2 ν⊗H) ≃ₗᵢ[ℂ] Lp H 2 ν` be the
one-measure tensor unitary and `C` the isometric comparison from `Completion(Lp ℂ 2 μ⊗Lp H
2 ν)` to `Completion(T⊗H)`. for each source vector `z`, applying `J_R` to
`radonProductMixedCompletionUnitary μ ν z` gives `U_H(C(z))`. -/
theorem radonProductMixedCompletionUnitary_toLp
    (z : Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν))) :
    completionToLp (H := H) (Measure.radonProd μ ν)
        (radonProductMixedCompletionUnitary (H := H) μ ν z) =
      radonProductMixedTensorUnitary (H := H) μ ν z :=
  LinearIsometryEquiv.apply_symm_apply _ _

end OriginalProduct

end

end MeasureTheory.HaarL2
