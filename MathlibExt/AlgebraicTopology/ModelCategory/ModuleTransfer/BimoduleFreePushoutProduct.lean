/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer.OriginalRank
public import MathlibExt.AlgebraicTopology.ModelCategory.StructuredReplacementComparisons
public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen
public import MathlibExt.CategoryTheory.Monoidal.Bimod.FreePushoutProducts

/-!
# The original free bimodule tensor cells in the source model

The exact free-pair Leibniz Arrow is the free outer image of the base
pushout-product with the original middle scalar. Its underlying
cofibrancy is the original sufficient hypothesis. The actual created
outer bimodule model and adjunction prove all three generating clauses.
No domain cofibrancy or diagonal regular-bimodule cofibrancy is added.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v wAD

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.BimoduleFreePushoutProduct

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  [HasColimitsOfSize.{0, 0} C] {A B D : Mon C} {I J : MorphismProperty C}
  {κAD : Cardinal.{wAD}} [Fact κAD.IsRegular] [OrderBot κAD.ord.ToType]
  (tAD : RightTransfer.OriginalRankModelTransfer (Bimod.free A D)
    (Bimod.forget (B := D) A) I J κAD)

omit [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
    [HasColimitsOfSize.{0, 0} C] in
/-- The actual outer free adjunction is Quillen from the original created classes. -/
theorem outerFreeQuillen :
    letI : ModelCategory (Bimod A D) := tAD.model
    (Bimod.freeForgetAdjunction A D).IsQuillenAdjunction := by
  let : ModelCategory (Bimod A D) := tAD.model
  exact StructuredReplacementComparisons.actualQuillen
    (Bimod.forget (B := D) A) tAD.weak_eq (Bimod.freeForgetAdjunction A D) tAD.fibrations_eq

variable [IsCofibrant B.X]

/-- The entire original free-I/free-I Arrow has the actual outer bimodule cofibration class. -/
theorem originalFreeI_pushoutProduct (hI : I.rlp = trivialFibrations C) :
    letI : ModelCategory (Bimod A D) := tAD.model
    ∀ {M M' : Bimod A B} (f : M ⟶ M'), I.strictMap (Bimod.free A B) f →
      ∀ {N N' : Bimod B D} (g : N ⟶ N'), I.strictMap (Bimod.free B D) g →
        cofibrations (Bimod A D)
          (((Bimod.tensorCurried A B D).leibnizPushout.obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let : ModelCategory (Bimod A D) := tAD.model
  let : (Bimod.freeForgetAdjunction A D).IsQuillenAdjunction := outerFreeQuillen tAD
  let : (ihom.adjunction B.X).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant B.X
  have hGen : I ≤ cofibrations C := by
    have h := I.le_llp_rlp
    rwa [hI, trivialFibrations_llp] at h
  intro M M' f hf N N' g hg
  cases hf with
  | @map U V i hi =>
    cases hg with
    | @map X Y j hj =>
      have hMiddle := Adjunction.IsQuillenAdjunction.preservesCofibrations
        (adj := ihom.adjunction B.X) j (hGen j hj)
      have hBase := IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
        (C := C) i (B.X ◁ j) (hGen i hi) hMiddle
      have hFree := Adjunction.IsQuillenAdjunction.preservesCofibrations
        (adj := Bimod.freeForgetAdjunction A D) _ hBase
      exact ((cofibrations (Bimod A D)).arrow_iso_iff
        (Bimod.freePushoutProductIso A B D i j)).mp hFree

/-- The original free-J/free-I Arrow has the left trivial-cofibration clause. -/
theorem originalFreeJFreeI_pushoutProduct
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    letI : ModelCategory (Bimod A D) := tAD.model
    ∀ {M M' : Bimod A B} (f : M ⟶ M'), J.strictMap (Bimod.free A B) f →
      ∀ {N N' : Bimod B D} (g : N ⟶ N'), I.strictMap (Bimod.free B D) g →
        trivialCofibrations (Bimod A D)
          (((Bimod.tensorCurried A B D).leibnizPushout.obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let : ModelCategory (Bimod A D) := tAD.model
  let : (Bimod.freeForgetAdjunction A D).IsQuillenAdjunction := outerFreeQuillen tAD
  let : (ihom.adjunction B.X).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant B.X
  have hGenI : I ≤ cofibrations C := by
    have h := I.le_llp_rlp
    rwa [hI, trivialFibrations_llp] at h
  have hGenJ : J ≤ trivialCofibrations C := by
    have h := J.le_llp_rlp
    rwa [hJ, fibrations_llp] at h
  intro M M' f hf N N' g hg
  cases hf with
  | @map U V i hi =>
    cases hg with
    | @map X Y j hj =>
      have hMiddle := Adjunction.IsQuillenAdjunction.preservesCofibrations
        (adj := ihom.adjunction B.X) j (hGenI j hj)
      have hBase := IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
        (C := C) i (B.X ◁ j) (hGenJ i hi) hMiddle
      have hFree := Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations
        (adj := Bimod.freeForgetAdjunction A D) _ hBase
      exact ((trivialCofibrations (Bimod A D)).arrow_iso_iff
        (Bimod.freePushoutProductIso A B D i j)).mp hFree

/-- The other original free-I/free-J orientation has its actual trivial-cofibration clause. -/
theorem originalFreeIFreeJ_pushoutProduct
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C) :
    letI : ModelCategory (Bimod A D) := tAD.model
    ∀ {M M' : Bimod A B} (f : M ⟶ M'), I.strictMap (Bimod.free A B) f →
      ∀ {N N' : Bimod B D} (g : N ⟶ N'), J.strictMap (Bimod.free B D) g →
        trivialCofibrations (Bimod A D)
          (((Bimod.tensorCurried A B D).leibnizPushout.obj (Arrow.mk f)).obj (Arrow.mk g)).hom := by
  let : ModelCategory (Bimod A D) := tAD.model
  let : (Bimod.freeForgetAdjunction A D).IsQuillenAdjunction := outerFreeQuillen tAD
  let : (ihom.adjunction B.X).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant B.X
  have hGenI : I ≤ cofibrations C := by
    have h := I.le_llp_rlp
    rwa [hI, trivialFibrations_llp] at h
  have hGenJ : J ≤ trivialCofibrations C := by
    have h := J.le_llp_rlp
    rwa [hJ, fibrations_llp] at h
  intro M M' f hf N N' g hg
  cases hf with
  | @map U V i hi =>
    cases hg with
    | @map X Y j hj =>
      have hMiddle := Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations
        (adj := ihom.adjunction B.X) j (hGenJ j hj)
      have hBase := IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
        (C := C) i (B.X ◁ j) (hGenI i hi) hMiddle
      have hFree := Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations
        (adj := Bimod.freeForgetAdjunction A D) _ hBase
      exact ((trivialCofibrations (Bimod A D)).arrow_iso_iff
        (Bimod.freePushoutProductIso A B D i j)).mp hFree

end HomotopicalAlgebra.ModuleTransfer.BimoduleFreePushoutProduct
