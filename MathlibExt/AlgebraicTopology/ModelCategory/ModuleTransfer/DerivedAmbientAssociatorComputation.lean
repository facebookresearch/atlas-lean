/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.ModuleTransfer.DerivedAmbientAssociator
public import MathlibExt.AlgebraicTopology.ModelCategory.DerivedTensorComputation

/-!
# Original computation of the full derived module associator

The two complete nested computation maps use the same original base and
module Q counits. Their compatibility with the full derived associator is
proved at every original endpoint. Cofibrancy is needed only to invert the
ordinary computation maps.
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

local notation "qA" => tA.replacements
local notation "qC" => GeneratedFunctorialReplacements.fromGeneration dC
local notation "M" => Mod C A
local notation "WC" => weakEquivalences C
local notation "WA" => moduleWeak tA
local notation "HA" => MorphismProperty.Localization WA
local notation "HC" => MorphismProperty.Localization WC
local notation "πA" => MorphismProperty.Q WA
local notation "πC" => MorphismProperty.Q WC

/-- Every original coefficient map is natural for the complete projected action comparison. -/
@[reassoc]
theorem comparison_naturality_coefficient {U V : C} (f : U ⟶ V) (N : M) :
    letI : ModelCategory M := tA.model
    ((action tA dC).map ((πC).map f)).app ((πA).obj N) ≫ (comparison tA dC V N).hom =
      (comparison tA dC U N).hom ≫
        (πA).map (Mod.AmbientTensor.map A ((qC).Q.map f) (𝟙 ((qA).Q.obj N))) := by
  let : ModelCategory M := tA.model
  exact congrArg (fun a => a.app N) ((projectionIso tA dC).hom.naturality f)

/-- Every original module map is natural for the same complete source comparison. -/
@[reassoc]
theorem comparison_naturality_module (U : C) {N N' : M} (p : N ⟶ N') :
    letI : ModelCategory M := tA.model
    ((action tA dC).obj ((πC).obj U)).map ((πA).map p) ≫ (comparison tA dC U N').hom =
      (comparison tA dC U N).hom ≫
        (πA).map ((Mod.AmbientTensor.functor A ((qC).Q.obj U)).map ((qA).Q.map p)) := by
  let : ModelCategory M := tA.model
  exact ((projectionIso tA dC).hom.app U).naturality p

/-- Both actual original Q counits give the ordinary computation at every original endpoint. -/
def ordinaryComparison (U : C) (N : M) :
    ((action tA dC).obj ((πC).obj U)).obj ((πA).obj N) ⟶
      (πA).obj (Mod.AmbientTensor.tensorModule A U N) :=
  (comparison tA dC U N).hom ≫ ((ordinaryComparisonMap tA dC).app U).app N

/-- Every original coefficient map commutes with the same actual two-counit computation. -/
@[reassoc]
theorem ordinaryComparison_naturality_coefficient {U V : C} (f : U ⟶ V) (N : M) :
    ((action tA dC).map ((πC).map f)).app ((πA).obj N) ≫ ordinaryComparison tA dC V N =
      ordinaryComparison tA dC U N ≫ (πA).map (Mod.AmbientTensor.map A f (𝟙 N)) := by
  let : ModelCategory M := tA.model
  have h := NatTrans.congr_app ((ordinaryComparisonMap tA dC).naturality f) N
  change (πA).map (Mod.AmbientTensor.map A ((qC).Q.map f) (𝟙 ((qA).Q.obj N))) ≫
      ((ordinaryComparisonMap tA dC).app V).app N =
    ((ordinaryComparisonMap tA dC).app U).app N ≫ (πA).map (Mod.AmbientTensor.map A f (𝟙 N)) at h
  unfold ordinaryComparison
  rw [Category.assoc, comparison_naturality_coefficient_assoc]
  simpa only [Category.assoc] using (comparison tA dC U N).hom ≫= h

/-- Every original module map commutes with the same actual two-counit computation. -/
@[reassoc]
theorem ordinaryComparison_naturality_module (U : C) {N N' : M} (p : N ⟶ N') :
    ((action tA dC).obj ((πC).obj U)).map ((πA).map p) ≫ ordinaryComparison tA dC U N' =
      ordinaryComparison tA dC U N ≫ (πA).map ((Mod.AmbientTensor.functor A U).map p) := by
  let : ModelCategory M := tA.model
  have h := ((ordinaryComparisonMap tA dC).app U).naturality p
  change (πA).map ((Mod.AmbientTensor.functor A ((qC).Q.obj U)).map ((qA).Q.map p)) ≫
      ((ordinaryComparisonMap tA dC).app U).app N' =
    ((ordinaryComparisonMap tA dC).app U).app N ≫
      (πA).map ((Mod.AmbientTensor.functor A U).map p) at h
  unfold ordinaryComparison
  rw [Category.assoc, comparison_naturality_module_assoc]
  simpa only [Category.assoc] using (comparison tA dC U N).hom ≫= h

/-- The actual left bracket projection keeps the original base tensor and module Q source. -/
def leftBracketComparison (U V : C) (N : M) :
    letI : ModelCategory M := tA.model
    ((action tA dC).obj (((DerivedTensorConstructions.tensor (qC)).obj ((πC).obj U)).obj ((πC).obj V))).obj
        ((πA).obj N) ≅
      (πA).obj (Mod.AmbientTensor.tensorModule A ((qC).Q.obj ((qC).Q.obj U ⊗ (qC).Q.obj V)) ((qA).Q.obj N)) := by
  letI : ModelCategory M := tA.model
  exact (((Localization.Lifting₃.iso πC πC πA WC WC WA (rawLeftBracket tA dC)
    (bifunctorComp₁₂ (DerivedTensorConstructions.tensor (qC)) (action tA dC))).app U).app V).app N

/-- The actual right bracket projection keeps both original module Q action source functors. -/
def rightBracketComparison (U V : C) (N : M) :
    letI : ModelCategory M := tA.model
    ((action tA dC).obj ((πC).obj U)).obj
        (((action tA dC).obj ((πC).obj V)).obj ((πA).obj N)) ≅
      (πA).obj (Mod.AmbientTensor.tensorModule A ((qC).Q.obj U)
        ((qA).Q.obj (Mod.AmbientTensor.tensorModule A ((qC).Q.obj V) ((qA).Q.obj N)))) := by
  letI : ModelCategory M := tA.model
  exact (((Localization.Lifting₃.iso πC πC πA WC WC WA (rawRightBracket tA dC)
    (bifunctorComp₂₃ (action tA dC) (action tA dC))).app U).app V).app N

/-- The left bracket comparison is the original pair of base and action projection comparisons. -/
theorem leftBracketComparison_hom (U V : C) (N : M) :
    (leftBracketComparison tA dC U V N).hom =
      ((action tA dC).map (DerivedTensorConstructions.comparison (qC) U V).hom).app ((πA).obj N) ≫
        (comparison tA dC ((qC).Q.obj U ⊗ (qC).Q.obj V) N).hom := by
  let : ModelCategory M := tA.model
  dsimp [leftBracketComparison, leftBracketLifting, Localization.Lifting₃.bifunctorComp₁₂,
    comparison, projectionIso, DerivedTensorConstructions.comparison, DerivedTensorConstructions.projectionIso]
  rfl

/-- The right bracket comparison is the original pair of action projection comparisons. -/
theorem rightBracketComparison_hom (U V : C) (N : M) :
    letI : ModelCategory M := tA.model
    (rightBracketComparison tA dC U V N).hom =
      ((action tA dC).obj ((πC).obj U)).map (comparison tA dC V N).hom ≫
        (comparison tA dC U (Mod.AmbientTensor.tensorModule A ((qC).Q.obj V) ((qA).Q.obj N))).hom := by
  let : ModelCategory M := tA.model
  dsimp [rightBracketComparison, rightBracketLifting, Localization.Lifting₃.bifunctorComp₂₃,
    comparison, projectionIso]
  rfl

/-- The actual original Q source is retained by the whole lifted associator. -/
theorem derivedAssociator_hom_source (U V : C) (N : M) :
    (((derivedAssociator tA dC).hom.app ((πC).obj U)).app ((πC).obj V)).app ((πA).obj N) =
      (leftBracketComparison tA dC U V N).hom ≫
        (((rawBracketAssociator tA dC).hom.app U).app V).app N ≫
          (rightBracketComparison tA dC U V N).inv := by
  let : ModelCategory M := tA.model
  exact derivedAssociator_hom_app tA dC U V N

/-- The full left ordinary computation uses the actual base and module counits. -/
def leftOrdinaryComparison (U V : C) (N : M) :
    ((action tA dC).obj (((DerivedTensorConstructions.tensor (qC)).obj ((πC).obj U)).obj ((πC).obj V))).obj
        ((πA).obj N) ⟶ (πA).obj (Mod.AmbientTensor.tensorModule A (U ⊗ V) N) :=
  ((action tA dC).map (DerivedTensorConstructions.ordinaryComparison (qC) U V)).app ((πA).obj N) ≫
    ordinaryComparison tA dC (U ⊗ V) N

/-- The full right ordinary computation uses the same two actual action counits. -/
def rightOrdinaryComparison (U V : C) (N : M) :
    ((action tA dC).obj ((πC).obj U)).obj
        (((action tA dC).obj ((πC).obj V)).obj ((πA).obj N)) ⟶
      (πA).obj (Mod.AmbientTensor.tensorModule A U (Mod.AmbientTensor.tensorModule A V N)) :=
  ((action tA dC).obj ((πC).obj U)).map (ordinaryComparison tA dC V N) ≫
    ordinaryComparison tA dC U (Mod.AmbientTensor.tensorModule A V N)

/-- The left nested computation contracts to the original three Q counit maps. -/
theorem leftOrdinaryComparison_contract (U V : C) (N : M) :
    letI : ModelCategory M := tA.model
    leftOrdinaryComparison tA dC U V N = (leftBracketComparison tA dC U V N).hom ≫
      (((leftBracketContraction tA dC).app U).app V).app N ≫
        (πA).map (Mod.AmbientTensor.map A ((qC).q.app U ⊗ₘ (qC).q.app V) ((qA).q.app N)) := by
  let : ModelCategory M := tA.model
  let f : (qC).Q.obj U ⊗ (qC).Q.obj V ⟶ U ⊗ V := (qC).q.app U ⊗ₘ (qC).q.app V
  have hq : (qC).Q.map f ≫ (qC).q.app (U ⊗ V) =
      (qC).q.app ((qC).Q.obj U ⊗ (qC).Q.obj V) ≫ f := (qC).q.naturality f
  have ht : Mod.AmbientTensor.map A ((qC).Q.map f) (𝟙 ((qA).Q.obj N)) ≫
        Mod.AmbientTensor.map A ((qC).q.app (U ⊗ V)) ((qA).q.app N) =
      Mod.AmbientTensor.map A ((qC).q.app ((qC).Q.obj U ⊗ (qC).Q.obj V)) (𝟙 ((qA).Q.obj N)) ≫
        Mod.AmbientTensor.map A f ((qA).q.app N) := by
    erw [← Mod.AmbientTensor.map_comp, ← Mod.AmbientTensor.map_comp, Category.id_comp, hq]
  dsimp [leftOrdinaryComparison, ordinaryComparison, ordinaryComparisonMap,
    DerivedTensorConstructions.ordinaryComparison,
    DerivedTensorConstructions.cofibrantComparisonMap]
  rw [leftBracketComparison_hom, leftBracketContraction_app]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  erw [reassoc_of% comparison_naturality_coefficient tA dC f N, ← (πA).map_comp, ht, (πA).map_comp]
  rfl

/-- The right nested computation contracts to the same original three Q counit maps. -/
theorem rightOrdinaryComparison_contract (U V : C) (N : M) :
    letI : ModelCategory M := tA.model
    rightOrdinaryComparison tA dC U V N = (rightBracketComparison tA dC U V N).hom ≫
      (((rightBracketContraction tA dC).app U).app V).app N ≫
        (πA).map (Mod.AmbientTensor.map A ((qC).q.app U)
          (Mod.AmbientTensor.map A ((qC).q.app V) ((qA).q.app N))) := by
  let : ModelCategory M := tA.model
  let f : Mod.AmbientTensor.tensorModule A ((qC).Q.obj V) ((qA).Q.obj N) ⟶
      Mod.AmbientTensor.tensorModule A V N := Mod.AmbientTensor.map A ((qC).q.app V) ((qA).q.app N)
  have hq : (qA).Q.map f ≫ (qA).q.app (Mod.AmbientTensor.tensorModule A V N) =
      (qA).q.app (Mod.AmbientTensor.tensorModule A ((qC).Q.obj V) ((qA).Q.obj N)) ≫ f :=
    (qA).q.naturality f
  have ht : Mod.AmbientTensor.map A (𝟙 ((qC).Q.obj U)) ((qA).Q.map f) ≫
        Mod.AmbientTensor.map A ((qC).q.app U) ((qA).q.app (Mod.AmbientTensor.tensorModule A V N)) =
      Mod.AmbientTensor.map A (𝟙 ((qC).Q.obj U))
          ((qA).q.app (Mod.AmbientTensor.tensorModule A ((qC).Q.obj V) ((qA).Q.obj N))) ≫
        Mod.AmbientTensor.map A ((qC).q.app U) f := by
    erw [← Mod.AmbientTensor.map_comp, ← Mod.AmbientTensor.map_comp, Category.id_comp, hq]
  dsimp [rightOrdinaryComparison, ordinaryComparison, ordinaryComparisonMap]
  rw [rightBracketComparison_hom, rightBracketContraction_app]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% comparison_naturality_module tA dC U f, ← (πA).map_comp, ht, (πA).map_comp]
  rfl

/-- The whole raw associator contracts to the exact original linear module associator. -/
theorem rawBracketAssociator_contract (U V : C) (N : M) :
    letI : ModelCategory M := tA.model
    (((rawBracketAssociator tA dC).hom.app U).app V).app N ≫
        (((rightBracketContraction tA dC).app U).app V).app N =
      (((leftBracketContraction tA dC).app U).app V).app N ≫
        (πA).map (AmbientActionPointSet.associate ((qC).Q.obj U) ((qC).Q.obj V) ((qA).Q.obj N)).hom := by
  let : ModelCategory M := tA.model
  let L := (((leftBracketContractionIso tA dC).app U).app V).app N
  let R := (((rightBracketContractionIso tA dC).app U).app V).app N
  change (L.hom ≫
      (πA).map (AmbientActionPointSet.associate ((qC).Q.obj U) ((qC).Q.obj V) ((qA).Q.obj N)).hom ≫
        R.inv) ≫ R.hom = L.hom ≫
      (πA).map (AmbientActionPointSet.associate ((qC).Q.obj U) ((qC).Q.obj V) ((qA).Q.obj N)).hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- At every original endpoint the full derived associator commutes with both actual ordinary computations. -/
@[reassoc]
theorem derivedAssociator_ordinaryComparison (U V : C) (N : M) :
    (((derivedAssociator tA dC).hom.app ((πC).obj U)).app ((πC).obj V)).app ((πA).obj N) ≫
        rightOrdinaryComparison tA dC U V N =
      leftOrdinaryComparison tA dC U V N ≫ (πA).map (AmbientActionPointSet.associate U V N).hom := by
  let : ModelCategory M := tA.model
  rw [derivedAssociator_hom_source, leftOrdinaryComparison_contract, rightOrdinaryComparison_contract]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% rawBracketAssociator_contract tA dC U V N]
  have h : (πA).map (Mod.AmbientTensor.map A ((qC).q.app U ⊗ₘ (qC).q.app V) ((qA).q.app N)) ≫
        (πA).map (AmbientActionPointSet.associate U V N).hom =
      (πA).map (AmbientActionPointSet.associate ((qC).Q.obj U) ((qC).Q.obj V) ((qA).Q.obj N)).hom ≫
        (πA).map (Mod.AmbientTensor.map A ((qC).q.app U)
          (Mod.AmbientTensor.map A ((qC).q.app V) ((qA).q.app N))) := by
    rw [← (πA).map_comp, ← (πA).map_comp]
    apply (πA).congr_map
    apply Mod.hom_ext
    simp only [Mod.comp_hom', Mod.AmbientTensor.map_hom, AmbientActionPointSet.associate_hom]
    exact associator_naturality ((qC).q.app U) ((qC).q.app V) ((qA).q.app N).hom
  rw [← h]

/-- The ordinary comparison is precisely the actual cofibrant computation Iso hom. -/
theorem ordinaryComparison_cofibrant (U : C) [IsCofibrant U] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N], ordinaryComparison tA dC U N = (cofibrantComparison tA dC U N).hom := by
  let : ModelCategory M := tA.model
  intro hN
  rfl

/-- Cofibrant computation retains every original coefficient arrow and its full naturality. -/
@[reassoc]
theorem cofibrantComparison_naturality_coefficient {U V : C} (f : U ⟶ V)
    [IsCofibrant U] [IsCofibrant V] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N],
      ((action tA dC).map ((πC).map f)).app ((πA).obj N) ≫ (cofibrantComparison tA dC V N).hom =
        (cofibrantComparison tA dC U N).hom ≫ (πA).map (Mod.AmbientTensor.map A f (𝟙 N)) := by
  let : ModelCategory M := tA.model
  intro hN
  exact ordinaryComparison_naturality_coefficient tA dC f N

/-- Cofibrant computation retains every original module arrow and its full naturality. -/
@[reassoc]
theorem cofibrantComparison_naturality_module (U : C) [IsCofibrant U] {N N' : M} (p : N ⟶ N') :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N] [_hN' : IsCofibrant N'],
      ((action tA dC).obj ((πC).obj U)).map ((πA).map p) ≫ (cofibrantComparison tA dC U N').hom =
        (cofibrantComparison tA dC U N).hom ≫ (πA).map ((Mod.AmbientTensor.functor A U).map p) := by
  let : ModelCategory M := tA.model
  intro hN hN'
  exact ordinaryComparison_naturality_module tA dC U p

/-- The full original left nested computation is an Iso at the actual cofibrant endpoints. -/
def leftCofibrantComparison (U V : C) [IsCofibrant U] [IsCofibrant V] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N],
      ((action tA dC).obj (((DerivedTensorConstructions.tensor (qC)).obj ((πC).obj U)).obj ((πC).obj V))).obj
          ((πA).obj N) ≅ (πA).obj (Mod.AmbientTensor.tensorModule A (U ⊗ V) N) := by
  letI : ModelCategory M := tA.model
  intro hN
  letI : IsCofibrant (U ⊗ V) := DerivedTensorConstructions.tensor_isCofibrant U V
  exact ((action tA dC).mapIso (DerivedTensorConstructions.cofibrantComparison (qC) U V)).app ((πA).obj N) ≪≫
    cofibrantComparison tA dC (U ⊗ V) N

/-- The full original right nested computation is an Iso at the actual cofibrant endpoints. -/
def rightCofibrantComparison (U V : C) [IsCofibrant U] [IsCofibrant V] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N],
      ((action tA dC).obj ((πC).obj U)).obj
          (((action tA dC).obj ((πC).obj V)).obj ((πA).obj N)) ≅
        (πA).obj (Mod.AmbientTensor.tensorModule A U (Mod.AmbientTensor.tensorModule A V N)) := by
  letI : ModelCategory M := tA.model
  intro hN
  letI : IsCofibrant (Mod.AmbientTensor.tensorModule A V N) := tensorModule_isCofibrant tA V N hN
  exact ((action tA dC).obj ((πC).obj U)).mapIso (cofibrantComparison tA dC V N) ≪≫
    cofibrantComparison tA dC U (Mod.AmbientTensor.tensorModule A V N)

/-- The left bracket Iso retains exactly the original ordinary comparison function. -/
theorem leftCofibrantComparison_hom (U V : C) [IsCofibrant U] [IsCofibrant V] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N], (leftCofibrantComparison tA dC U V N).hom =
      leftOrdinaryComparison tA dC U V N := by
  let : ModelCategory M := tA.model
  intro hN
  rfl

/-- The right bracket Iso retains exactly the original ordinary comparison function. -/
theorem rightCofibrantComparison_hom (U V : C) [IsCofibrant U] [IsCofibrant V] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N], (rightCofibrantComparison tA dC U V N).hom =
      rightOrdinaryComparison tA dC U V N := by
  let : ModelCategory M := tA.model
  intro hN
  rfl

/-- The full derived associator is exactly the original linear associator between both actual computations. -/
theorem derivedAssociator_cofibrant (U V : C) [IsCofibrant U] [IsCofibrant V] (N : M) :
    letI : ModelCategory M := tA.model
    ∀ [_hN : IsCofibrant N],
      (((derivedAssociator tA dC).hom.app ((πC).obj U)).app ((πC).obj V)).app ((πA).obj N) =
        (leftCofibrantComparison tA dC U V N).hom ≫
          (πA).map (AmbientActionPointSet.associate U V N).hom ≫
          (rightCofibrantComparison tA dC U V N).inv := by
  let : ModelCategory M := tA.model
  intro hN
  apply (cancel_mono (rightCofibrantComparison tA dC U V N).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [leftCofibrantComparison_hom, rightCofibrantComparison_hom]
  exact derivedAssociator_ordinaryComparison tA dC U V N

end HomotopicalAlgebra.ModuleTransfer.DerivedAmbientAction
