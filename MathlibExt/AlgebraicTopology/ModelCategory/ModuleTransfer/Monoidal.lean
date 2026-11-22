/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer
import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer
import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct
import MathlibExt.CategoryTheory.Monoidal.Mod.FreePushoutProducts
import MathlibExt.CategoryTheory.Monoidal.Mod.Closed

/-!
# Closed symmetric monoidal models on the existing commutative modules

The original balanced tensor on `Mod C A.X` satisfies the pushout-product
axiom for an actual full free transfer. Its free-pair comparison identifies
the original generating pushout-products with the images of the base
pushout-products. A cofibrant base tensor unit makes the actual regular
module unit cofibrant, without a cofibrancy hypothesis on the scalar in `C`.
-/

set_option autoImplicit false
noncomputable section
universe w u v

open CategoryTheory Limits MonoidalCategory MorphismProperty
open CategoryTheory.SmallObject
open scoped MonoidalCategory CategoryTheory.MonObj

namespace HomotopicalAlgebra.ModuleTransfer.Monoidal

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  (A : CommMon C)

/-- The actual balanced tensor monoidal structure on commutative modules. -/
local instance moduleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
/-- The symmetry of the actual balanced tensor on commutative modules. -/
local instance moduleSymmetric : SymmetricCategory (Mod C A.X) := Mod.instSymmetricCategory A
/-- The actual internal Hom right adjoint to the balanced module tensor. -/
local instance moduleClosed : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A


/-- The original unit generator extended into the actual regular module. -/
def freeUnitRegularMap : (Mod.free A.X).obj (𝟙_ C) ⟶ Mod.regular A.X :=
  ((Mod.freeForgetAdjunction A.X).homEquiv (𝟙_ C) (Mod.regular A.X)).symm η[A.X]

omit [ModelCategory C] [MonoidalClosed C] in
/-- The complete carrier of the original unit extension is the original right unitor. -/
theorem freeUnitRegularMap_hom : (freeUnitRegularMap A).hom = (ρ_ A.X).hom := by
  have h := Mod.freeForgetAdjunction_homEquiv_symm_apply_hom A.X (Mod.regular A.X) η[A.X]
  change (freeUnitRegularMap A).hom = 𝟙 (A.X ⊗ 𝟙_ C) ≫ (A.X ◁ η[A.X]) ≫ μ[A.X] at h
  rw [Category.id_comp, MonObj.mul_one] at h
  exact h

/-- The original free module on the base unit is the actual regular module unit. -/
def freeUnitRegularIso : (Mod.free A.X).obj (𝟙_ C) ≅ Mod.regular A.X := by
  let e : ((Mod.free A.X).obj (𝟙_ C)).X ≅ (Mod.regular A.X).X := ρ_ A.X
  have he : e.hom = (freeUnitRegularMap A).hom := (freeUnitRegularMap_hom A).symm
  let : IsModHom A.X e.hom := by
    rw [he]
    infer_instance
  refine
    { hom := freeUnitRegularMap A
      inv := Mod.Hom.mk' e.inv (IsModHom.smul_hom (A := A.X) (f := e.inv))
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Mod.hom_ext
    change (freeUnitRegularMap A).hom ≫ e.inv = 𝟙 ((Mod.free A.X).obj (𝟙_ C)).X
    rw [← he]
    exact e.hom_inv_id
  · apply Mod.hom_ext
    change e.inv ≫ (freeUnitRegularMap A).hom = 𝟙 (Mod.regular A.X).X
    rw [← he]
    exact e.inv_hom_id

section Transfer

variable (I J : MorphismProperty C)
  (hSourceI : UniformRelativeSourceSmallness.{w} (I.strictMap (Mod.free A.X)))
  (hSourceJ : UniformRelativeSourceSmallness.{w} (J.strictMap (Mod.free A.X)))
  (t : RightTransfer.FullModelTransfer (Mod.free A.X) (Mod.forget (D := C) A.X)
    I J hSourceI hSourceJ)


omit [MonoidalClosed C] in
/-- The actual full transfer makes the original free/forget adjunction Quillen. -/
theorem quillenOfTransfer :
    letI : ModelCategory (Mod C A.X) := t.model
    CategoryTheory.Adjunction.IsQuillenAdjunction (Mod.freeForgetAdjunction A.X) := by
  let : ModelCategory (Mod C A.X) := t.model
  apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro M N f hf
    have h := t.fibrations_eq.le f hf
    exact h
  · intro M N f hf
    have h := t.trivialFibrations_eq.le f hf
    exact h

omit [MonoidalClosed C] in
/-- The full target cofibration class is the original free-I left lifting class. -/
theorem cofibrations_eq_freeI (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (Mod C A.X) := t.model
    cofibrations (Mod C A.X) = (I.strictMap (Mod.free A.X)).rlp.llp := by
  let : ModelCategory (Mod C A.X) := t.model
  rw [t.cofibrations_eq, strictMap_rlp_eq_inverseImage_rlp I
    (Mod.free A.X) (Mod.forget (D := C) A.X) (Mod.freeForgetAdjunction A.X), hI]

variable [IsClosedSymmetricMonoidalModelCategory C]

/-- Both original free-I generators satisfy the actual module pushout-product cofibration clause. -/
theorem freeI_pushoutProduct_cofibration (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (Mod C A.X) := t.model
    ∀ {P Q U V : Mod C A.X} (i : P ⟶ Q), (I.strictMap (Mod.free A.X)) i →
      ∀ (j : U ⟶ V), (I.strictMap (Mod.free A.X)) j →
        cofibrations (Mod C A.X) (Arrow.mk i □ Arrow.mk j).hom := by
  let : ModelCategory (Mod C A.X) := t.model
  have hGenI : I ≤ cofibrations C := by
    have h := I.le_llp_rlp
    rwa [hI, trivialFibrations_llp] at h
  let : CategoryTheory.Adjunction.IsQuillenAdjunction (Mod.freeForgetAdjunction A.X) :=
    quillenOfTransfer A I J hSourceI hSourceJ t
  intro P Q U V i hi j hj
  cases hi with
  | map hi =>
    cases hj with
    | map hj =>
      have hBase := IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
        (C := C) _ _ (hGenI _ hi) (hGenI _ hj)
      have hFree := (inferInstance : CategoryTheory.Adjunction.IsQuillenAdjunction
        (Mod.freeForgetAdjunction A.X)).preservesCofibrations _ hBase
      exact ((cofibrations (Mod C A.X)).arrow_iso_iff (Mod.FreePushoutProducts.iso A _ _)).mp hFree

/-- Original free-J/free-I generator pairs satisfy the actual trivial pushout-product clause. -/
theorem freeJ_freeI_pushoutProduct_trivial
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    letI : ModelCategory (Mod C A.X) := t.model
    ∀ {P Q U V : Mod C A.X} (i : P ⟶ Q), (J.strictMap (Mod.free A.X)) i →
      ∀ (j : U ⟶ V), (I.strictMap (Mod.free A.X)) j →
        trivialCofibrations (Mod C A.X) (Arrow.mk i □ Arrow.mk j).hom := by
  let : ModelCategory (Mod C A.X) := t.model
  have hSourceCofI : I ≤ cofibrations C := by
    have h := I.le_llp_rlp
    rwa [hI, trivialFibrations_llp] at h
  have hSourceTrivJ : J ≤ trivialCofibrations C := by
    have h := J.le_llp_rlp
    rwa [hJ, fibrations_llp] at h
  let : CategoryTheory.Adjunction.IsQuillenAdjunction (Mod.freeForgetAdjunction A.X) :=
    quillenOfTransfer A I J hSourceI hSourceJ t
  intro P Q U V i hi j hj
  cases hi with
  | map hi =>
    cases hj with
    | map hj =>
      have hBase := IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
        (C := C) _ _ (hSourceTrivJ _ hi) (hSourceCofI _ hj)
      have hFree := (inferInstance : CategoryTheory.Adjunction.IsQuillenAdjunction
        (Mod.freeForgetAdjunction A.X)).preservesTrivialCofibrations _ hBase
      exact ((trivialCofibrations (Mod C A.X)).arrow_iso_iff (Mod.FreePushoutProducts.iso A _ _)).mp hFree

/-- The original free-I lifting classes extend the actual generator cofibration clause to all maps. -/
theorem pushoutProduct_cofibration (hI : I.rlp = trivialFibrations C) {P Q U V : Mod C A.X} (i : P ⟶ Q) (j : U ⟶ V)
    : letI : ModelCategory (Mod C A.X) := t.model
    cofibrations (Mod C A.X) i → cofibrations (Mod C A.X) j →
      cofibrations (Mod C A.X) (Arrow.mk i □ Arrow.mk j).hom := by
  let : ModelCategory (Mod C A.X) := t.model
  intro hi hj
  have hC := cofibrations_eq_freeI A I J hSourceI hSourceJ t hI
  rw [hC] at hi hj ⊢
  apply pushoutProduct_mem_rlp_llp (I.strictMap (Mod.free A.X)) (I.strictMap (Mod.free A.X))
    (I.strictMap (Mod.free A.X)) ?_ hi hj
  intro X Y U V a ha b hb
  rw [← hC]
  exact freeI_pushoutProduct_cofibration A I J hSourceI hSourceJ t hI a ha b hb

/-- Original free-J/free-I lifting classes extend the actual trivial generator clause to all maps. -/
theorem pushoutProduct_trivial_left
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) {P Q U V : Mod C A.X} (i : P ⟶ Q) (j : U ⟶ V)
    : letI : ModelCategory (Mod C A.X) := t.model
    trivialCofibrations (Mod C A.X) i → cofibrations (Mod C A.X) j →
      trivialCofibrations (Mod C A.X) (Arrow.mk i □ Arrow.mk j).hom := by
  let : ModelCategory (Mod C A.X) := t.model
  intro hi hj
  have hC := cofibrations_eq_freeI A I J hSourceI hSourceJ t hI
  have hT := t.trivialCofibrations_eq
  rw [hT] at hi ⊢
  rw [hC] at hj
  apply pushoutProduct_mem_rlp_llp (J.strictMap (Mod.free A.X)) (I.strictMap (Mod.free A.X))
    (J.strictMap (Mod.free A.X)) ?_ hi hj
  intro X Y U V a ha b hb
  rw [← hT]
  exact freeJ_freeI_pushoutProduct_trivial A I J hSourceI hSourceJ t hI hJ a ha b hb

/-- The actual balanced tensor symmetry supplies the right trivial pushout-product clause. -/
theorem pushoutProduct_trivial_right
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) {P Q U V : Mod C A.X} (i : P ⟶ Q) (j : U ⟶ V)
    : letI : ModelCategory (Mod C A.X) := t.model
    cofibrations (Mod C A.X) i → trivialCofibrations (Mod C A.X) j →
      trivialCofibrations (Mod C A.X) (Arrow.mk i □ Arrow.mk j).hom := by
  let : ModelCategory (Mod C A.X) := t.model
  intro hi hj
  have h := pushoutProduct_trivial_left A I J hSourceI hSourceJ t hI hJ j i hj hi
  exact ((trivialCofibrations (Mod C A.X)).arrow_iso_iff
    (CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.braiding (Arrow.mk i) (Arrow.mk j))).mpr h

variable [IsCofibrant (𝟙_ C)]

omit [IsClosedSymmetricMonoidalModelCategory C] in
/-- A cofibrant base unit makes the actual regular module unit cofibrant in the full transfer. -/
theorem moduleUnit_isCofibrant :
    letI : ModelCategory (Mod C A.X) := t.model
    IsCofibrant (𝟙_ (Mod C A.X)) := by
  let : ModelCategory (Mod C A.X) := t.model
  let : CategoryTheory.Adjunction.IsQuillenAdjunction (Mod.freeForgetAdjunction A.X) :=
    quillenOfTransfer A I J hSourceI hSourceJ t
  let : IsCofibrant ((Mod.free A.X).obj (𝟙_ C)) :=
    CategoryTheory.Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Mod.freeForgetAdjunction A.X) inferInstance
  change IsCofibrant (Mod.regular A.X)
  exact isCofibrant_of_cofibration (freeUnitRegularIso A).hom

/-- The original balanced tensor is a closed symmetric monoidal model on the actual full transfer. -/
theorem monoidalOfTransfer
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    letI : ModelCategory (Mod C A.X) := t.model
    IsClosedSymmetricMonoidalModelCategory (Mod C A.X) := by
  let : ModelCategory (Mod C A.X) := t.model
  let : IsCofibrant (𝟙_ (Mod C A.X)) := moduleUnit_isCofibrant A I J hSourceI hSourceJ t
  apply isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit (Mod C A.X)
  · exact pushoutProduct_cofibration A I J hSourceI hSourceJ t hI
  · exact pushoutProduct_trivial_left A I J hSourceI hSourceJ t hI hJ
  · exact pushoutProduct_trivial_right A I J hSourceI hSourceJ t hI hJ

end Transfer

section SourceModels

variable (I J : MorphismProperty C)
  (hSourceI : UniformRelativeSourceSmallness.{w} (I.strictMap (Mod.free A.X)))
  (hSourceJ : UniformRelativeSourceSmallness.{w} (J.strictMap (Mod.free A.X)))

/-- A full original commutative module transfer with its actual balanced monoidal model. -/
structure FullCommutativeModelTransfer where
  /-- The source-derived full model, source ranks, generators and complete factors. -/
  transfer : RightTransfer.FullModelTransfer (Mod.free A.X) (Mod.forget (D := C) A.X)
    I J hSourceI hSourceJ
  /-- The closed symmetric monoidal model on that same transfer and the actual balanced tensor. -/
  monoidal : letI : ModelCategory (Mod C A.X) := transfer.model
    IsClosedSymmetricMonoidalModelCategory (Mod C A.X)

variable [HasLimitsOfSize.{w, w} C] [HasColimitsOfSize.{w, w} C] [LocallySmall.{w} C]
  [I.IsSmall.{w}] [J.IsSmall.{w}] [MonoidAxiom.{w} C]
  [IsClosedSymmetricMonoidalModelCategory C] [IsCofibrant (𝟙_ C)]

/-- Original source generation and the monoid axiom construct the actual commutative monoidal model.
The target transfer is constructed here; no target model, pushout-product or unit outcome is an input. -/
def fullCommutativeModuleModelTransfer
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    FullCommutativeModelTransfer A I J hSourceI hSourceJ := by
  let t := HomotopicalAlgebra.ModuleTransfer.fullLeftModuleModelTransfer A.toMon I J hI hJ
    hSourceI hSourceJ
  exact
    { transfer := t
      monoidal := monoidalOfTransfer A I J hSourceI hSourceJ t hI hJ }

end SourceModels

end HomotopicalAlgebra.ModuleTransfer.Monoidal
