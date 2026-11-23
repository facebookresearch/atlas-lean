/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer.OriginalRank
import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.Monoidal

/-!
# The actual balanced monoidal model at the original module source rank

The original fixed-rank source transfer gives the complete created model and
its full free-I/free-J generation. The exact free-pair balanced tensor Arrow
comparison proves all three pushout-product clauses, first on the original
generators and then on the entire lifting classes. The actual regular module
unit is the free module on the original cofibrant base unit.

No uniform-smallness claim is made from a fixed-rank source algorithm, and no
cofibrancy of the diagonal regular bimodule is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v wA

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped MonoidalCategory CategoryTheory.MonObj

namespace HomotopicalAlgebra.ModuleTransfer.OriginalRankMonoidal

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  (A : CommMon C) {I J : MorphismProperty C}
  {κA : Cardinal.{wA}} [Fact κA.IsRegular] [OrderBot κA.ord.ToType]
  (t : RightTransfer.OriginalRankModelTransfer (Mod.free A.X) (Mod.forget (D := C) A.X) I J κA)

/-- The existing commutative-module tensor and tensor unit. -/
local instance moduleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A
/-- The existing commutative-module braiding on that tensor. -/
local instance moduleSymmetric : SymmetricCategory (Mod C A.X) := Mod.instSymmetricCategory A
/-- The existing relative module tensor–Hom adjunction. -/
local instance moduleClosed : MonoidalClosed (Mod C A.X) := Mod.instMonoidalClosed A

omit [MonoidalClosed C] in
/-- The original free/forget adjunction is Quillen in the completely source-produced original-rank model. -/
theorem freeQuillen :
    letI : ModelCategory (Mod C A.X) := t.model
    (Mod.freeForgetAdjunction A.X).IsQuillenAdjunction := by
  let : ModelCategory (Mod C A.X) := t.model
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y f hf
    exact t.fibrations_eq.le f hf
  · intro X Y f hf
    exact t.trivialFibrations_eq.le f hf

omit [MonoidalClosed C] in
/-- The full target cofibration class is the same original free-I lifting class. -/
theorem cofibrations_eq_originalFreeI :
    letI : ModelCategory (Mod C A.X) := t.model
    cofibrations (Mod C A.X) = (I.strictMap (Mod.free A.X)).rlp.llp := by
  let : ModelCategory (Mod C A.X) := t.model
  rw [← t.generation_I, t.generation.I_rlp, trivialFibrations_llp]

variable [IsClosedSymmetricMonoidalModelCategory C]

/-- Every original free-I pair retains the actual balanced tensor cofibration clause. -/
theorem originalFreeI_pushoutProduct (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (Mod C A.X) := t.model
    ∀ {P Q U V : Mod C A.X} (i : P ⟶ Q), (I.strictMap (Mod.free A.X)) i →
      ∀ (j : U ⟶ V), (I.strictMap (Mod.free A.X)) j →
        cofibrations (Mod C A.X) (Arrow.mk i □ Arrow.mk j).hom := by
  let : ModelCategory (Mod C A.X) := t.model
  have hGen : I ≤ cofibrations C := by
    have h := I.le_llp_rlp
    rwa [hI, trivialFibrations_llp] at h
  let : (Mod.freeForgetAdjunction A.X).IsQuillenAdjunction := freeQuillen A t
  intro P Q U V i hi j hj
  cases hi with
  | map hi =>
    cases hj with
    | map hj =>
      have hBase := IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
        (C := C) _ _ (hGen _ hi) (hGen _ hj)
      have hFree := Adjunction.IsQuillenAdjunction.preservesCofibrations
        (adj := Mod.freeForgetAdjunction A.X) _ hBase
      exact ((cofibrations (Mod C A.X)).arrow_iso_iff (Mod.FreePushoutProducts.iso A _ _)).mp hFree

/-- Every original free-J/free-I pair retains the actual balanced tensor trivial clause. -/
theorem originalFreeJFreeI_pushoutProduct
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    letI : ModelCategory (Mod C A.X) := t.model
    ∀ {P Q U V : Mod C A.X} (i : P ⟶ Q), (J.strictMap (Mod.free A.X)) i →
      ∀ (j : U ⟶ V), (I.strictMap (Mod.free A.X)) j →
        trivialCofibrations (Mod C A.X) (Arrow.mk i □ Arrow.mk j).hom := by
  let : ModelCategory (Mod C A.X) := t.model
  have hGenI : I ≤ cofibrations C := by
    have h := I.le_llp_rlp
    rwa [hI, trivialFibrations_llp] at h
  have hGenJ : J ≤ trivialCofibrations C := by
    have h := J.le_llp_rlp
    rwa [hJ, fibrations_llp] at h
  let : (Mod.freeForgetAdjunction A.X).IsQuillenAdjunction := freeQuillen A t
  intro P Q U V i hi j hj
  cases hi with
  | map hi =>
    cases hj with
    | map hj =>
      have hBase := IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
        (C := C) _ _ (hGenJ _ hi) (hGenI _ hj)
      have hFree := Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations
        (adj := Mod.freeForgetAdjunction A.X) _ hBase
      exact ((trivialCofibrations (Mod C A.X)).arrow_iso_iff (Mod.FreePushoutProducts.iso A _ _)).mp hFree

/-- The entire original free-I lifting classes satisfy the actual balanced tensor cofibration clause. -/
theorem pushoutProduct_cofibration (hI : I.rlp = trivialFibrations C)
    {P Q U V : Mod C A.X} (i : P ⟶ Q) (j : U ⟶ V) :
    letI : ModelCategory (Mod C A.X) := t.model
    cofibrations (Mod C A.X) i → cofibrations (Mod C A.X) j →
      cofibrations (Mod C A.X) (Arrow.mk i □ Arrow.mk j).hom := by
  let : ModelCategory (Mod C A.X) := t.model
  intro hi hj
  have hC := cofibrations_eq_originalFreeI A t
  rw [hC] at hi hj ⊢
  apply pushoutProduct_mem_rlp_llp (I.strictMap (Mod.free A.X)) (I.strictMap (Mod.free A.X))
    (I.strictMap (Mod.free A.X)) ?_ hi hj
  intro X Y U V f hf g hg
  rw [← hC]
  exact originalFreeI_pushoutProduct A t hI f hf g hg

/-- The entire original free-J/free-I lifting classes satisfy the actual left trivial clause. -/
theorem pushoutProduct_trivial_left
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    {P Q U V : Mod C A.X} (i : P ⟶ Q) (j : U ⟶ V) :
    letI : ModelCategory (Mod C A.X) := t.model
    trivialCofibrations (Mod C A.X) i → cofibrations (Mod C A.X) j →
      trivialCofibrations (Mod C A.X) (Arrow.mk i □ Arrow.mk j).hom := by
  let : ModelCategory (Mod C A.X) := t.model
  intro hi hj
  have hC := cofibrations_eq_originalFreeI A t
  rw [t.trivialCofibrations_eq] at hi ⊢
  rw [hC] at hj
  apply pushoutProduct_mem_rlp_llp (J.strictMap (Mod.free A.X)) (I.strictMap (Mod.free A.X))
    (J.strictMap (Mod.free A.X)) ?_ hi hj
  intro X Y U V f hf g hg
  rw [← t.trivialCofibrations_eq]
  exact originalFreeJFreeI_pushoutProduct A t hI hJ f hf g hg

/-- The original full balanced braid proves the right trivial clause on every original pair. -/
theorem pushoutProduct_trivial_right
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    {P Q U V : Mod C A.X} (i : P ⟶ Q) (j : U ⟶ V) :
    letI : ModelCategory (Mod C A.X) := t.model
    cofibrations (Mod C A.X) i → trivialCofibrations (Mod C A.X) j →
      trivialCofibrations (Mod C A.X) (Arrow.mk i □ Arrow.mk j).hom := by
  let : ModelCategory (Mod C A.X) := t.model
  intro hi hj
  exact ((trivialCofibrations (Mod C A.X)).arrow_iso_iff
    (CategoryTheory.MonoidalCategory.Arrow.PushoutProduct.braiding (Arrow.mk i) (Arrow.mk j))).mpr
      (pushoutProduct_trivial_left A t hI hJ j i hj hi)

variable [IsCofibrant (𝟙_ C)]

omit [IsClosedSymmetricMonoidalModelCategory C] in
/-- The actual regular module unit is cofibrant, as the original free module on the cofibrant base unit. -/
theorem moduleUnit_isCofibrant :
    letI : ModelCategory (Mod C A.X) := t.model
    IsCofibrant (𝟙_ (Mod C A.X)) := by
  let : ModelCategory (Mod C A.X) := t.model
  let : (Mod.freeForgetAdjunction A.X).IsQuillenAdjunction := freeQuillen A t
  let : IsCofibrant ((Mod.free A.X).obj (𝟙_ C)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := Mod.freeForgetAdjunction A.X) inferInstance
  change IsCofibrant (Mod.regular A.X)
  exact isCofibrant_of_cofibration (ModuleTransfer.Monoidal.freeUnitRegularIso A).hom

/-- The same original-rank source model is closed symmetric monoidal for the actual balanced tensor. -/
theorem monoidalModel
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    letI : ModelCategory (Mod C A.X) := t.model
    IsClosedSymmetricMonoidalModelCategory (Mod C A.X) := by
  let : ModelCategory (Mod C A.X) := t.model
  let : IsCofibrant (𝟙_ (Mod C A.X)) := moduleUnit_isCofibrant A t
  apply isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit (Mod C A.X)
  · exact pushoutProduct_cofibration A t hI
  · exact pushoutProduct_trivial_left A t hI hJ
  · exact pushoutProduct_trivial_right A t hI hJ

end HomotopicalAlgebra.ModuleTransfer.OriginalRankMonoidal
