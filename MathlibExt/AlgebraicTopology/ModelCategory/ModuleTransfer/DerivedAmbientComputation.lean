/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.AmbientActionPointSet

/-!
# Actual cofibrant computation of the external derived action

The original coefficient and module Q counits give a complete two-variable
natural comparison to the original point-set action. Its invertibility is
proved from the earned ambient Brown laws at actual cofibrant endpoints.
The same tensor/cotensor Quillen adjunction proves cofibrancy of their tensor.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v wA wC

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MorphismProperty Functor
open scoped CategoryTheory.MonObj MonoidalCategory

namespace HomotopicalAlgebra.ModuleTransfer.DerivedAmbientAction

variable {C : Type u} [Category.{v} C] [ModelCategory C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
  {A : C} [MonObj A] {I J : MorphismProperty C}
  {κA : Cardinal.{wA}} [Fact κA.IsRegular] [OrderBot κA.ord.ToType]
  (tA : RightTransfer.OriginalRankModelTransfer (Mod.free A) (Mod.forget (D := C) A) I J κA)
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  (dC : CofibrantGenerationData C κC)

open CategoryTheory.HomogeneousLocalization
open CategoryTheory.HomogeneousLocalization.AmbientTensorHom

local notation "qA" => tA.replacements
local notation "qC" => GeneratedFunctorialReplacements.fromGeneration dC
local notation "M" => Mod C A
local notation "WA" => moduleWeak tA
local notation "HA" => MorphismProperty.Localization WA
local notation "HC" => MorphismProperty.Localization (weakEquivalences C)
local notation "πA" => MorphismProperty.Q WA
local notation "πC" => MorphismProperty.Q (weakEquivalences C)

/-- The actual produced transfer and original ambient adjunction earn cofibrancy of every cofibrant pair. -/
theorem tensorModule_isCofibrant (U : C) [IsCofibrant U] (N : M) :
    letI : ModelCategory M := tA.model
    IsCofibrant N → IsCofibrant (Mod.AmbientTensor.tensorModule A U N) := by
  let : ModelCategory M := tA.model
  intro hN
  let : IsCofibrant N := hN
  let : (adjunction A U).IsQuillenAdjunction :=
    AmbientBrown.fixedAdjunction_isQuillen tA.weak_eq tA.fibrations_eq U
  exact Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adjunction A U) hN

/-- The ordinary original ambient action retains every original coefficient and module map. -/
def ordinary : C ⥤ M ⥤ HA := leftBifunctor A ⋙ (whiskeringRight M M HA).obj πA

/-- Both original Q counits give the whole source comparison to the ordinary original action. -/
def ordinaryComparisonMap : raw tA dC ⟶ ordinary tA := by
  letI : ModelCategory M := tA.model
  refine
    { app := fun U =>
        { app := fun N => (πA).map (Mod.AmbientTensor.map A ((qC).q.app U) ((qA).q.app N))
          naturality := ?_ }
      naturality := ?_ }
  · intro N N' p
    change (πA).map (Mod.AmbientTensor.map A (𝟙 ((qC).Q.obj U)) ((qA).Q.map p)) ≫
        (πA).map (Mod.AmbientTensor.map A ((qC).q.app U) ((qA).q.app N')) =
      (πA).map (Mod.AmbientTensor.map A ((qC).q.app U) ((qA).q.app N)) ≫
        (πA).map (Mod.AmbientTensor.map A (𝟙 U) p)
    rw [← (πA).map_comp, ← (πA).map_comp]
    apply (πA).congr_map
    erw [← Mod.AmbientTensor.map_comp, ← Mod.AmbientTensor.map_comp, Category.id_comp, Category.comp_id,
      (qA).q.naturality]
    rfl
  · intro U V f
    apply NatTrans.ext
    funext N
    change (πA).map (Mod.AmbientTensor.map A ((qC).Q.map f) (𝟙 ((qA).Q.obj N))) ≫
        (πA).map (Mod.AmbientTensor.map A ((qC).q.app V) ((qA).q.app N)) =
      (πA).map (Mod.AmbientTensor.map A ((qC).q.app U) ((qA).q.app N)) ≫
        (πA).map (Mod.AmbientTensor.map A f (𝟙 N))
    rw [← (πA).map_comp, ← (πA).map_comp]
    apply (πA).congr_map
    erw [← Mod.AmbientTensor.map_comp, ← Mod.AmbientTensor.map_comp, Category.id_comp, Category.comp_id,
      (qC).q.naturality]
    rfl

omit [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C] in
/-- The complete ordinary comparison retains the literal original tensor of both Q counits. -/
theorem ordinaryComparisonMap_app (U : C) (N : M) :
    letI : ModelCategory M := tA.model
    ((ordinaryComparisonMap tA dC).app U).app N =
      (πA).map (Mod.AmbientTensor.map A ((qC).q.app U) ((qA).q.app N)) := rfl

/-- That exact source comparison is invertible at the two actual original cofibrant endpoints. -/
theorem ordinaryComparisonMap_isIso (U : C) [IsCofibrant U] (N : M) :
    letI : ModelCategory M := tA.model
    IsCofibrant N → IsIso (((ordinaryComparisonMap tA dC).app U).app N) := by
  let : ModelCategory M := tA.model
  intro hN
  let : IsCofibrant N := hN
  let : IsCofibrant ((𝟭 C).obj U) := (inferInstance : IsCofibrant U)
  let : IsCofibrant ((𝟭 M).obj N) := hN
  let : IsCofibrant ((qC).Q.obj U) := (qC).q_cofibrant U
  let : IsCofibrant ((qA).Q.obj N) := (qA).q_cofibrant N
  have h₁ := AmbientBrown.coefficient_weak_of_cofibrant tA.weak_eq tA.fibrations_eq
    ((qA).Q.obj N) ((qC).q.app U) ((qC).q_trivialFibration U).2
  have h₂ := AmbientBrown.module_weak_of_cofibrant tA.weak_eq tA.fibrations_eq
    U ((qA).q.app N) ((qA).q_trivialFibration N).2
  have h := (weakEquivalences M).comp_mem _ _ h₁ h₂
  change weakEquivalences M
    (Mod.AmbientTensor.map A ((qC).q.app U) (𝟙 ((qA).Q.obj N)) ≫
      Mod.AmbientTensor.map A (𝟙 U) ((qA).q.app N)) at h
  erw [← Mod.AmbientTensor.map_comp, Category.comp_id, Category.id_comp] at h
  change IsIso ((πA).map (Mod.AmbientTensor.map A ((qC).q.app U) ((qA).q.app N)))
  exact Localization.inverts πA WA _ h

/-- Ordinary tensor of the same cofibrant coefficient and module computes the actual derived action. -/
def cofibrantComparison (U : C) [IsCofibrant U] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N], ((action tA dC).obj ((πC).obj U)).obj ((πA).obj N) ≅
      (πA).obj (Mod.AmbientTensor.tensorModule A U N) := by
  letI : ModelCategory M := tA.model
  intro hN
  letI : IsIso (((ordinaryComparisonMap tA dC).app U).app N) :=
    ordinaryComparisonMap_isIso tA dC U N hN
  exact comparison tA dC U N ≪≫ asIso (((ordinaryComparisonMap tA dC).app U).app N)

end HomotopicalAlgebra.ModuleTransfer.DerivedAmbientAction
