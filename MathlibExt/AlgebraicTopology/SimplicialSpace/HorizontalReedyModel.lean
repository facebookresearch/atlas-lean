/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyModelCategory
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
import Mathlib.AlgebraicTopology.ModelCategory.Transport

/-!
# The horizontal Joyal--Reedy model on simplicial spaces

Transpose the two original simplicial coordinates so that the inner degree is
the Reedy diagram index and each diagram value is the original outer row.
Transport the selected Joyal model from its designated copy to ordinary
simplicial sets, form the Reedy model, and transport it back to the designated
simplicial-space carrier.

The resulting named model has rowwise categorical equivalences as weak maps,
genuine categorical relative-matching fibrations, and the original
monomorphisms as cofibrations.  The transpose, diagramwise Joyal-copy
equivalence, literal row maps, and relative matching maps are exposed for the
subsequent Joyal--Tierney row comparison.  No Rezk localization assertion is
made here.
-/

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial

namespace SimplicialSpace.HorizontalModel

/-- Exchange the two original simplicial coordinates. -/
def transposeEquivalence :
    SimplicialObject SSet.{u} ≌ SimplicialObject SSet.{u} :=
  Functor.flipping

/-- Apply the designated Joyal-copy forgetful functor at every diagram value. -/
abbrev diagramwiseJoyalForget :
    SimplicialObject JoyalSSet.{u} ⥤ SimplicialObject SSet.{u} :=
  (Functor.whiskeringRight SimplexCategoryᵒᵖ JoyalSSet.{u} SSet.{u}).obj
    JoyalSSet.forget

instance : diagramwiseJoyalForget.{u}.IsEquivalence := inferInstance

/-- The diagramwise equivalence between designated Joyal simplicial sets and
ordinary simplicial sets. -/
noncomputable def joyalDiagramEquivalence :
    SimplicialObject JoyalSSet.{u} ≌ SimplicialObject SSet.{u} :=
  diagramwiseJoyalForget.asEquivalence

/-- The literal transposed ordinary diagram underlying a simplicial space. -/
noncomputable def rawCarrierEquivalence :
    SimplicialSpace.{u} ≌ SimplicialObject SSet.{u} :=
  SimplicialSpace.equivalenceSimplicialObject.{u} |>.trans
    transposeEquivalence

/-- Transposition as an equivalence of the designated simplicial-space
carrier with itself.  This is the orientation used to turn the existing
column-power API into the genuine row-power API. -/
noncomputable def transposeSpaceEquivalence :
    SimplicialSpace.{u} ≌ SimplicialSpace.{u} :=
  rawCarrierEquivalence.trans
    SimplicialSpace.equivalenceSimplicialObject.symm

/-- The transposed diagram, with every row wrapped in the designated Joyal
copy. -/
noncomputable def carrierEquivalence :
    SimplicialSpace.{u} ≌ SimplicialObject JoyalSSet.{u} :=
  rawCarrierEquivalence.trans joyalDiagramEquivalence.symm

/-- Regard a simplicial space as its transposed ordinary row diagram. -/
abbrev horizontalDiagram :
    SimplicialSpace.{u} ⥤ SimplicialObject SSet.{u} :=
  rawCarrierEquivalence.functor

/-- The original map on a fixed horizontal row. -/
abbrev horizontalRowMap {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) :=
  (horizontalDiagram.map f).app n

/-- The genuine relative matching map of the transposed row diagram. -/
noncomputable abbrev horizontalRelativeMatchingMap
    {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) (n : ℕ) :=
  SimplicialObject.relativeMatchingMap (horizontalDiagram.map f) n

/-- Transposition sends original bidegree `(m,n)` to degree `m` in row `n`. -/
@[simp]
theorem horizontalDiagram_obj_obj (X : SimplicialSpace.{u})
    (m n : SimplexCategoryᵒᵖ) :
    ((horizontalDiagram.obj X).obj n).obj m = (X.diagram.obj m).obj n :=
  rfl

/-- Operators inside a horizontal row are the original outer operators. -/
@[simp]
theorem horizontalDiagram_obj_map (X : SimplicialSpace.{u})
    {m m' : SimplexCategoryᵒᵖ} (a : m ⟶ m')
    (n : SimplexCategoryᵒᵖ) :
    ((horizontalDiagram.obj X).obj n).map a = (X.diagram.map a).app n :=
  rfl

/-- Operators between horizontal rows are the original inner operators. -/
@[simp]
theorem horizontalDiagram_map_app (X : SimplicialSpace.{u})
    {n n' : SimplexCategoryᵒᵖ} (a : n ⟶ n')
    (m : SimplexCategoryᵒᵖ) :
    ((horizontalDiagram.obj X).map a).app m = (X.diagram.obj m).map a :=
  rfl

/-- The designated-space transpose has the same literal bidegree swap. -/
@[simp]
theorem transposeSpaceEquivalence_obj_obj (X : SimplicialSpace.{u})
    (m n : SimplexCategoryᵒᵖ) :
    ((SimplicialSpace.forget.obj
      (transposeSpaceEquivalence.functor.obj X)).obj n).obj m =
      (X.diagram.obj m).obj n :=
  rfl

/-- Maps under the designated-space transpose retain the original bidegree
component. -/
@[simp]
theorem transposeSpaceEquivalence_map_app {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) (m n : SimplexCategoryᵒᵖ) :
    (((SimplicialSpace.forget.map
      (transposeSpaceEquivalence.functor.map f)).app n).app m) =
      (f.hom.app m).app n :=
  rfl

/-- The transposed row map retains the original bidegree component. -/
@[simp]
theorem horizontalRowMap_app {X Y : SimplicialSpace.{u}} (f : X ⟶ Y)
    (m n : SimplexCategoryᵒᵖ) :
    (horizontalRowMap f n).app m = (f.hom.app m).app n :=
  rfl

/-- Forgetting the diagramwise Joyal copy canonically recovers the literal
transposed ordinary row diagram. -/
noncomputable def carrierForgetIso :
    carrierEquivalence.{u}.functor ⋙ diagramwiseJoyalForget.{u} ≅
      horizontalDiagram.{u} :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft rawCarrierEquivalence.functor
      joyalDiagramEquivalence.counitIso ≪≫
    horizontalDiagram.rightUnitor

/-- The Joyal-copy comparison retains the whole original transposed map. -/
@[reassoc]
theorem carrierForgetIso_naturality {X Y : SimplicialSpace.{u}}
    (f : X ⟶ Y) :
    (carrierEquivalence.functor ⋙ diagramwiseJoyalForget).map f ≫
        carrierForgetIso.hom.app Y =
      carrierForgetIso.hom.app X ≫ horizontalDiagram.map f :=
  carrierForgetIso.hom.naturality f

@[instance_reducible]
private noncomputable def joyalModelOnSSet : ModelCategory SSet.{u} := by
  let J : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory
  let _ : ModelCategory JoyalSSet.{u} := J
  let _ : CategoryWithCofibrations SSet.{u} :=
    { cofibrations := monomorphisms SSet.{u} }
  let _ : CategoryWithWeakEquivalences SSet.{u} :=
    { weakEquivalences := SSet.categoricalEquivalences.{u} }
  let _ : CategoryWithFibrations SSet.{u} :=
    { fibrations := SSet.categoricalFibrations.{u} }
  apply ModelCategory.transport JoyalSSet.equivalenceSSet.symm
  · change monomorphisms SSet.{u} =
      (JoyalSSet.modelCategory.{u}.categoryWithCofibrations.cofibrations).inverseImage
        JoyalSSet.ofSSet.{u}
    rw [JoyalSSet.modelCategory_cofibrations]
    apply MorphismProperty.ext
    intro X Y f
    change Mono f ↔ Mono (JoyalSSet.ofSSet.{u}.map f)
    constructor
    · intro hf
      let _ : Mono f := hf
      infer_instance
    · exact JoyalSSet.ofSSet.{u}.mono_of_mono_map
  · change SSet.categoricalFibrations.{u} =
      (JoyalSSet.modelCategory.{u}.categoryWithFibrations.fibrations).inverseImage
        JoyalSSet.ofSSet.{u}
    rw [JoyalSSet.modelCategory_fibrations]
    rfl
  · change SSet.categoricalEquivalences.{u} =
      (JoyalSSet.modelCategory.{u}.categoryWithWeakEquivalences.weakEquivalences).inverseImage
        JoyalSSet.ofSSet.{u}
    rw [JoyalSSet.modelCategory_weakEquivalences]
    rfl

@[instance_reducible]
private noncomputable def rawModelCategory :
    ModelCategory (SimplicialObject SSet.{u}) := by
  let _ : ModelCategory SSet.{u} := joyalModelOnSSet
  exact SimplicialObject.reedyModelCategory

/-- The horizontal Joyal--Reedy model on the designated simplicial-space
carrier. -/
@[instance_reducible]
noncomputable def modelCategory : ModelCategory SimplicialSpace.{u} := by
  let R : ModelCategory (SimplicialObject SSet.{u}) := rawModelCategory
  let _ : ModelCategory (SimplicialObject SSet.{u}) := R
  let _ : CategoryWithCofibrations SimplicialSpace.{u} :=
    { cofibrations := (cofibrations (SimplicialObject SSet.{u})).inverseImage
        rawCarrierEquivalence.functor }
  let _ : CategoryWithFibrations SimplicialSpace.{u} :=
    { fibrations := (fibrations (SimplicialObject SSet.{u})).inverseImage
        rawCarrierEquivalence.functor }
  let _ : CategoryWithWeakEquivalences SimplicialSpace.{u} :=
    { weakEquivalences :=
        (weakEquivalences (SimplicialObject SSet.{u})).inverseImage
          rawCarrierEquivalence.functor }
  exact ModelCategory.transport rawCarrierEquivalence rfl rfl rfl

/-- Weak equivalences in the horizontal model are exactly the rowwise genuine
categorical equivalences. -/
theorem weakEquivalence_iff {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    WeakEquivalence f ↔
      ∀ n : ℕ,
        SSet.categoricalEquivalences.{u} (horizontalRowMap f (Opposite.op ⦋n⦌)) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  change (∀ a : SimplexCategoryᵒᵖ,
      SSet.categoricalEquivalences ((horizontalDiagram.map f).app a)) ↔ _
  constructor
  · intro h n
    exact h (Opposite.op ⦋n⦌)
  · intro h a
    exact h a.unop.len

/-- Fibrations in the horizontal model are exactly the maps whose genuine row
relative-matching maps are categorical fibrations. -/
theorem fibration_iff {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    Fibration f ↔
      ∀ n : ℕ,
        SSet.categoricalFibrations.{u} (horizontalRelativeMatchingMap f n) := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [HomotopicalAlgebra.fibration_iff]
  change SimplicialObject.reedyRight SSet.categoricalFibrations
      (horizontalDiagram.map f) ↔ _
  exact SimplicialObject.reedyRight_iff
    (C := SSet.{u}) SSet.categoricalFibrations (horizontalDiagram.map f)

/-- Cofibrations in the horizontal model are exactly the original
monomorphisms. -/
theorem cofibration_iff {X Y : SimplicialSpace.{u}} (f : X ⟶ Y) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    Cofibration f ↔ Mono f := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [HomotopicalAlgebra.cofibration_iff]
  change SimplicialObject.reedyLeft (monomorphisms SSet.{u})
      (rawCarrierEquivalence.functor.map f) ↔ Mono f
  rw [SimplicialObject.reedyLeft_monomorphisms_eq]
  constructor
  · intro hf
    exact rawCarrierEquivalence.functor.mono_of_mono_map hf
  · intro hf
    let _ : Mono f := hf
    infer_instance

private theorem mono_initial_to (X : SimplicialSpace.{u}) :
    Mono (initial.to X) := by
  apply (SimplicialSpace.mono_forget_map_iff (initial.to X)).mp
  apply (NatTrans.mono_iff_mono_app
    (SimplicialSpace.forget.map (initial.to X))).2
  intro m
  apply (NatTrans.mono_iff_mono_app
    ((SimplicialSpace.forget.map (initial.to X)).app m)).2
  intro n
  have hRaw : IsInitial (SimplicialSpace.forget.obj
      (⊥_ SimplicialSpace.{u})) :=
    initialIsInitial.isInitialObj SimplicialSpace.forget
      (⊥_ SimplicialSpace.{u})
  have hOuter : IsInitial
      ((SimplicialSpace.forget.obj (⊥_ SimplicialSpace.{u})).obj m) :=
    hRaw.isInitialObj ((evaluation SimplexCategoryᵒᵖ SSet.{u}).obj m)
      (SimplicialSpace.forget.obj (⊥_ SimplicialSpace.{u}))
  have hType : IsInitial
      (((SimplicialSpace.forget.obj
        (⊥_ SimplicialSpace.{u})).obj m).obj n) :=
    hOuter.isInitialObj ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n)
      ((SimplicialSpace.forget.obj (⊥_ SimplicialSpace.{u})).obj m)
  let _ : IsEmpty (((SimplicialSpace.forget.obj
      (⊥_ SimplicialSpace.{u})).obj m).obj n) :=
    (Types.initial_iff_empty _).mp ⟨hType⟩
  exact (mono_iff_injective _).2 (Function.injective_of_subsingleton _)

/-- Every simplicial space is cofibrant in the horizontal model. -/
theorem isCofibrant (X : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := modelCategory
    HomotopicalAlgebra.IsCofibrant X := by
  let _ : ModelCategory SimplicialSpace.{u} := modelCategory
  rw [HomotopicalAlgebra.isCofibrant_iff]
  exact (cofibration_iff (initial.to X)).2 (mono_initial_to X)

namespace ModelCategory

/-- Opt-in horizontal Joyal--Reedy model-category instance. -/
noncomputable scoped instance instModelCategory :
    HomotopicalAlgebra.ModelCategory SimplicialSpace.{u} :=
  HorizontalModel.modelCategory

end ModelCategory

end SimplicialSpace.HorizontalModel
