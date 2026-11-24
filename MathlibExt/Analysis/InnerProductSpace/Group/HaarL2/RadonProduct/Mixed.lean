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
# The original mixed-factor H-valued Radon product tensor

Actual completions of stock tensor congruence and associativity, with the
proved inside-completion maps, give the original direct mixed carrier.
Its composition with the constructed H-valued product unitary retains
literal completed pure vectors, independent factor/H universes and H=0.
No product isometry, associator model or norm certificate is an input.
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

/-- The actual linear map of the inverse right inside-completion unitary. -/
private def radonProductMixedTensorRightMap :
    Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Completion ((Lp ℂ 2 ν) ⊗[ℂ] H))) →ₗ[ℂ]
      Completion ((Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H)) :=
  (TensorProduct.completionRightTensorUnitary (𝕜 := ℂ)
    (E := Lp ℂ 2 μ) (F := (Lp ℂ 2 ν) ⊗[ℂ] H)).symm.toLinearMap

/-- The actual linear map of the inverse completed stock associator. -/
private def radonProductMixedTensorAssocMap :
    Completion ((Lp ℂ 2 μ) ⊗[ℂ] ((Lp ℂ 2 ν) ⊗[ℂ] H)) →ₗ[ℂ]
      Completion (((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ⊗[ℂ] H) :=
  (LinearIsometryEquiv.completion
    (TensorProduct.assocIsometry ℂ (Lp ℂ 2 μ) (Lp ℂ 2 ν) H)).symm.toLinearMap

/-- The actual linear map of the forward left inside-completion unitary. -/
private def radonProductMixedTensorLeftMap :
    Completion (((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) ⊗[ℂ] H) →ₗ[ℂ]
      Completion ((Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν))) ⊗[ℂ] H) :=
  (TensorProduct.completionLeftTensorUnitary (𝕜 := ℂ)
    (E := (Lp ℂ 2 μ) ⊗[ℂ] (Lp ℂ 2 ν)) (F := H)).toLinearMap

/-- The actual inverse right completion map strips the original inner completion on pure tensors. -/
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

/-- The actual completed associator inverse retains the original pure tensor association. -/
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

/-- The actual left completion map inserts the original completed left pure tensor. -/
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

/-- The actual linear map of the completed right-factor scalar-vector congruence. -/
private def radonProductMixedTensorCongruenceMap :
    Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) →ₗ[ℂ]
      Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Completion ((Lp ℂ 2 ν) ⊗[ℂ] H))) :=
  (LinearIsometryEquiv.completion
    (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (Lp ℂ 2 μ))
      (L2.tensorToLp (𝕜 := ℂ) (H := H) ν).symm)).toLinearMap

/-- The actual congruence map retains the literal f tensor L2(g tensor ξ) pure vector. -/
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

/-- Actual stock completion congruence and inside-completion associativity compare the original mixed tensor. -/
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

/-- The original comparison acts through its four actual completed linear-map fields. -/
private theorem radonProductMixedTensorComparison_apply
    (z : Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν))) :
    radonProductMixedTensorComparison (H := H) μ ν z =
      radonProductMixedTensorLeftMap μ ν
        (radonProductMixedTensorAssocMap μ ν
          (radonProductMixedTensorRightMap μ ν (radonProductMixedTensorCongruenceMap μ ν z))) := rfl

/-- The actual mixed comparison retains literal full scalar-factor vectors and their completed pure tensor. -/
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

/-- The original Borel measurable space of the topological product. -/
local instance instMixedProductBorelMeasurableSpace : MeasurableSpace (X × Y) := borel (X × Y)
local instance instMixedProductBorelSpace : BorelSpace (X × Y) := ⟨rfl⟩

/-- The original direct mixed tensor is the full H-valued Borel Radon product Lp space. -/
def radonProductMixedTensorUnitary :
    Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) ≃ₗᵢ[ℂ] Lp H 2 (Measure.radonProd μ ν) :=
  (radonProductMixedTensorComparison (H := H) μ ν).trans (radonProductTensorHilbertUnitary (H := H) μ ν)

/-- The original mixed map has the literal stock completed-congruence/associator linear DATA. -/
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

/-- Literal full scalar-factor vectors and ξ retain the original completed pure tensor values. -/
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

/-- Original compact-support scalar factors and ξ give their actual H-valued product a.e. -/
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

/-- The original direct mixed tensor maps into the actual H-valued compact-support completion model. -/
def radonProductMixedCompletionUnitary :
    Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν)) ≃ₗᵢ[ℂ]
      CompletionCore (H := H) (Measure.radonProd μ ν) :=
  (radonProductMixedTensorUnitary (H := H) μ ν).trans
    (completionToLp (H := H) (Measure.radonProd μ ν)).symm

/-- The mapped original completion model retains the actual full H-valued product Lp vector. -/
theorem radonProductMixedCompletionUnitary_toLp
    (z : Completion ((Lp ℂ 2 μ) ⊗[ℂ] (Lp H 2 ν))) :
    completionToLp (H := H) (Measure.radonProd μ ν)
        (radonProductMixedCompletionUnitary (H := H) μ ν z) =
      radonProductMixedTensorUnitary (H := H) μ ν z :=
  LinearIsometryEquiv.apply_symm_apply _ _

end OriginalProduct

end

end MeasureTheory.HaarL2
