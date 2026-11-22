/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FullEEquivalenceEvaluation
import MathlibExt.AlgebraicTopology.SimplicialSpace.WalkingIsomorphismStages
import MathlibExt.AlgebraicTopology.SimplicialSpace.EquivalenceMappingComponents
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# The original shifted full-E decorated mapping limit

The actual shifted source colimit gives the raw mapping limit. The original
component inclusions and full-E top selection give its selected cone and
universal map. Its zeroth isomorphism is the original forward-edge comparison.
All data retain the same coefficient, operators and target maps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.FullEEquivalence

@[implicit_reducible]
private def shiftedStages : ℕ ⥤ SSet.{u} where
  obj n := (SSet.coherentIso.stage (n + 1) : SSet.{u})
  map f := SSet.Subcomplex.homOfLE
    (SSet.coherentIso.monotone_stage (Nat.add_le_add_right (leOfHom f) 1))
  map_id n := by
    apply (cancel_mono (SSet.coherentIso.stage (n + 1)).ι).mp
    rw [SSet.Subcomplex.homOfLE_ι, Category.id_comp]
  map_comp f g := by
    apply (cancel_mono (SSet.coherentIso.stage (_ + 1)).ι).mp
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι]

@[implicit_reducible]
private def shiftedStageCocone : Cocone shiftedStages.{u} where
  pt := SSet.coherentIso
  ι := { app n := (SSet.coherentIso.stage (n + 1)).ι
         naturality := by
           intro n m f
           change SSet.Subcomplex.homOfLE
               (SSet.coherentIso.monotone_stage (Nat.add_le_add_right (leOfHom f) 1)) ≫
                 (SSet.coherentIso.stage (m + 1)).ι =
             (SSet.coherentIso.stage (n + 1)).ι ≫ 𝟙 _
           rw [SSet.Subcomplex.homOfLE_ι, Category.comp_id] }

private def shiftedStageIsColimit : IsColimit shiftedStageCocone.{u} :=
  evaluationJointlyReflectsColimits _ fun d => by
    apply Types.FilteredColimit.isColimitOf'
    · intro x
      exact ⟨2 * d.unop.len, ⟨x, SSet.coherentIso.mem_stage_bound x⟩, rfl⟩
    · intro n x y h
      change x.val = y.val at h
      refine ⟨n, 𝟙 n, ?_⟩
      exact congrArg (fun z => ((shiftedStages.map (𝟙 n)).app d) z) (Subtype.ext h)

@[implicit_reducible]
private def shiftedInnerCocone : Cocone (shiftedStages.{u} ⋙ SSet.simplicialSpaceDiscrete) :=
  SSet.simplicialSpaceDiscrete.mapCocone shiftedStageCocone

private def shiftedInnerIsColimit : IsColimit shiftedInnerCocone.{u} :=
  evaluationJointlyReflectsColimits _ fun a =>
    evaluationJointlyReflectsColimits _ fun _ =>
      isColimitOfPreserves ((CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type u)).obj a)
        shiftedStageIsColimit

@[implicit_reducible]
private def rawMappingDiagram (W : SimplicialSpace.{u}) : ℕᵒᵖ ⥤ SSet.{u} :=
  shiftedStages.op ⋙ discreteSourceMapping W

@[implicit_reducible]
private def rawMappingCone (W : SimplicialSpace.{u}) : Cone (rawMappingDiagram W) where
  pt := (discreteSourceMapping W).obj (op SSet.coherentIso)
  π :=
    { app n := (discreteSourceMapping W).map (SSet.coherentIso.stage (n.unop + 1)).ι.op
      naturality := by
        intro n m f
        change (discreteSourceMapping W).map (SSet.coherentIso.stage (m.unop + 1)).ι.op =
          (discreteSourceMapping W).map (SSet.coherentIso.stage (n.unop + 1)).ι.op ≫
            (discreteSourceMapping W).map (shiftedStages.map f.unop).op
        have hs : shiftedStages.map f.unop ≫ (SSet.coherentIso.stage (n.unop + 1)).ι =
            (SSet.coherentIso.stage (m.unop + 1)).ι :=
          SSet.Subcomplex.homOfLE_ι
            (SSet.coherentIso.monotone_stage (Nat.add_le_add_right (leOfHom f.unop) 1))
        rw [← (discreteSourceMapping W).map_comp, ← op_comp, hs] }

private def rawMappingIsLimit (W : SimplicialSpace.{u}) : IsLimit (rawMappingCone W) := by
  let _ : PreservesColimitsOfShape ℕ (innerHomFunctor.flip.obj W).rightOp :=
    innerHom_rightOp_preservesColimitsOfShape ℕ W
  have hI := isColimitOfPreserves ofSimplicialObject shiftedInnerIsColimit.{u}
  have hM := isColimitOfPreserves (innerHomFunctor.flip.obj W).rightOp hI
  exact (isLimitConeLeftOpOfCocone _ hM).ofIsoLimit
    (Cone.ext (Iso.refl _) (fun n => by rfl))

@[implicit_reducible]
private def selectedMappingTower (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    ℕᵒᵖ ⥤ SSet.{u} where
  obj n := (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage (n.unop + 1)) : SSet.{u})
  map f := EquivalenceMapping.restriction W hW (shiftedStages.map f.unop)
  map_id n := by
    rw [unop_id, CategoryTheory.Functor.map_id]
    exact EquivalenceMapping.restriction_id W hW (SSet.coherentIso.stage (n.unop + 1))
  map_comp f g := by
    rw [unop_comp, CategoryTheory.Functor.map_comp]
    exact EquivalenceMapping.restriction_comp W hW (shiftedStages.map g.unop)
      (shiftedStages.map f.unop)

/-- The original selected mapping tower has literal shifted stages E(n+1). -/
@[implicit_reducible]
def mappingTower (W : SimplicialSpace.{u}) (hW : segalSpaces W) : ℕᵒᵖ ⥤ SSet.{u} :=
  selectedMappingTower W hW

/-- Every original tower object is the same decorated shifted stage. -/
theorem mappingTower_obj (W : SimplicialSpace.{u}) (hW : segalSpaces W) (n : ℕ) :
    (mappingTower W hW).obj (op n) =
      (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage (n + 1)) : SSet.{u}) := rfl

/-- Every original opposite arrow is restriction along the same shifted source map. -/
theorem mappingTower_map (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    {n m : ℕ} (h : n ≤ m) :
    (mappingTower W hW).map (homOfLE h).op =
      EquivalenceMapping.restriction W hW (SSet.coherentIso.stageDiagram.map
        (homOfLE (Nat.add_le_add_right h 1))) := rfl

/-- The canonical selected cone retains the raw full-E mapping object as its point. -/
@[implicit_reducible]
def mappingTowerCone (W : SimplicialSpace.{u}) (hW : segalSpaces W) : Cone (mappingTower W hW) :=
  let eFull : (EquivalenceMapping.subcomplex W hW SSet.coherentIso : SSet.{u}) ≅
      (discreteSourceMapping W).obj (op SSet.coherentIso) :=
    SSet.Subcomplex.eqToIso (selection_eq_top W hW) ≪≫ SSet.Subcomplex.topIso _
  { pt := (discreteSourceMapping W).obj (op SSet.coherentIso)
    π :=
      { app n := eFull.inv ≫ EquivalenceMapping.restriction W hW
          (SSet.coherentIso.stage (n.unop + 1)).ι
        naturality := by
          intro n m f
          change eFull.inv ≫ EquivalenceMapping.restriction W hW
              (SSet.coherentIso.stage (m.unop + 1)).ι =
            (eFull.inv ≫ EquivalenceMapping.restriction W hW
              (SSet.coherentIso.stage (n.unop + 1)).ι) ≫
                EquivalenceMapping.restriction W hW (shiftedStages.map f.unop)
          have hs : shiftedStages.map f.unop ≫ (SSet.coherentIso.stage (n.unop + 1)).ι =
              (SSet.coherentIso.stage (m.unop + 1)).ι :=
            SSet.Subcomplex.homOfLE_ι
              (SSet.coherentIso.monotone_stage (Nat.add_le_add_right (leOfHom f.unop) 1))
          calc
            _ = eFull.inv ≫ EquivalenceMapping.restriction W hW
                (shiftedStages.map f.unop ≫ (SSet.coherentIso.stage (n.unop + 1)).ι) :=
              congrArg (fun i => eFull.inv ≫ EquivalenceMapping.restriction W hW i) hs.symm
            _ = _ := (congrArg (fun i => eFull.inv ≫ i)
              (EquivalenceMapping.restriction_comp W hW (shiftedStages.map f.unop)
                (SSet.coherentIso.stage (n.unop + 1)).ι)).trans (Category.assoc _ _ _).symm } }

/-- The cone point is the unchanged full-E inner mapping space. -/
theorem mappingTowerCone_pt (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (mappingTowerCone W hW).pt = (discreteSourceMapping W).obj (op SSet.coherentIso) := rfl

/-- Every canonical projection followed by its original inclusion is raw source restriction. -/
theorem mappingTowerCone_π_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) (n : ℕ) :
    (mappingTowerCone W hW).π.app (op n) ≫
        (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage (n + 1))).ι =
      (discreteSourceMapping W).map (SSet.coherentIso.stage (n + 1)).ι.op := by
  let eFull := SSet.Subcomplex.eqToIso (selection_eq_top W hW) ≪≫ SSet.Subcomplex.topIso _
  have he : eFull.inv ≫ (EquivalenceMapping.subcomplex W hW SSet.coherentIso).ι = 𝟙 _ := by
    simp only [eFull, Iso.trans_inv, SSet.Subcomplex.eqToIso_inv, Category.assoc,
      SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.topIso_inv_ι]
  change (eFull.inv ≫ EquivalenceMapping.restriction W hW
      (SSet.coherentIso.stage (n + 1)).ι) ≫
        (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage (n + 1))).ι = _
  rw [Category.assoc, EquivalenceMapping.restriction_ι, ← Category.assoc, he, Category.id_comp]

@[implicit_reducible]
private def towerInclusion (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    mappingTower W hW ⟶ rawMappingDiagram W where
  app n := (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage (n.unop + 1))).ι
  naturality := by
    intro n m f
    exact EquivalenceMapping.restriction_ι W hW (shiftedStages.map f.unop)

private def selectedMappingIsLimit (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    IsLimit (mappingTowerCone W hW) := by
  let inc := towerInclusion W hW
  let hc := rawMappingIsLimit W
  refine
    { lift := fun s => hc.lift ((Cone.postcompose inc).obj s)
      fac := ?_
      uniq := ?_ }
  · intro s n
    let _ : Mono (inc.app n) := by
      change Mono (EquivalenceMapping.subcomplex W hW
        (SSet.coherentIso.stage (n.unop + 1))).ι
      infer_instance
    apply (cancel_mono (inc.app n)).mp
    change (hc.lift ((Cone.postcompose inc).obj s) ≫ (mappingTowerCone W hW).π.app n) ≫
      (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage (n.unop + 1))).ι = _
    rw [Category.assoc, mappingTowerCone_π_ι W hW n.unop]
    exact hc.fac ((Cone.postcompose inc).obj s) n
  · intro s m hm
    apply hc.hom_ext
    intro n
    change m ≫ (discreteSourceMapping W).map (SSet.coherentIso.stage (n.unop + 1)).ι.op = _
    calc
      _ = (m ≫ (mappingTowerCone W hW).π.app n) ≫ inc.app n := by
        change m ≫ (discreteSourceMapping W).map
            (SSet.coherentIso.stage (n.unop + 1)).ι.op =
          (m ≫ (mappingTowerCone W hW).π.app n) ≫
            (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage (n.unop + 1))).ι
        rw [Category.assoc, mappingTowerCone_π_ι W hW n.unop]
      _ = s.π.app n ≫ inc.app n := congrArg (fun f => f ≫ inc.app n) (hm n)
      _ = hc.lift ((Cone.postcompose inc).obj s) ≫ (rawMappingCone W).π.app n :=
        (hc.fac ((Cone.postcompose inc).obj s) n).symm

/-- The actual cone is limiting, with its universal map and every original factor equation. -/
def mappingTowerIsLimit (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    IsLimit (mappingTowerCone W hW) :=
  selectedMappingIsLimit W hW

/-- The original E1 restriction and restricted Yoneda give the actual zeroth isomorphism. -/
def mappingTowerZeroIso (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (mappingTower W hW).obj (op 0) ≅ (SegalHomotopy.equivalenceSubcomplex W hW : SSet.{u}) :=
  let e : (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage 1) : SSet.{u}) ≅
      (EquivalenceMapping.subcomplex W hW Δ[1] : SSet.{u}) :=
    { hom := EquivalenceMapping.restriction W hW SSet.coherentIso.forwardIso.hom
      inv := EquivalenceMapping.restriction W hW SSet.coherentIso.forwardIso.inv
      hom_inv_id := by
        rw [← EquivalenceMapping.restriction_comp, Iso.inv_hom_id,
          EquivalenceMapping.restriction_id]
      inv_hom_id := by
        rw [← EquivalenceMapping.restriction_comp, Iso.hom_inv_id,
          EquivalenceMapping.restriction_id] }
  e ≪≫ EquivalenceMapping.yonedaIsoOne W hW

/-- The forward zero comparison retains the original inclusion and forward source isomorphism. -/
theorem mappingTowerZeroIso_hom_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (mappingTowerZeroIso W hW).hom ≫ (SegalHomotopy.equivalenceSubcomplex W hW).ι =
      (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage 1)).ι ≫
        (discreteSourceMapping W).map SSet.coherentIso.forwardIso.hom.op ≫
          (discreteYonedaIso W 1).hom := by
  change (EquivalenceMapping.restriction W hW SSet.coherentIso.forwardIso.hom ≫
    (EquivalenceMapping.yonedaIsoOne W hW).hom) ≫ _ = _
  rw [Category.assoc, EquivalenceMapping.yonedaIsoOne_hom_ι, ← Category.assoc,
    EquivalenceMapping.restriction_ι, Category.assoc]

/-- The inverse zero comparison retains the original inverse source and Yoneda maps. -/
theorem mappingTowerZeroIso_inv_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (mappingTowerZeroIso W hW).inv ≫
        (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage 1)).ι =
      (SegalHomotopy.equivalenceSubcomplex W hW).ι ≫ (discreteYonedaIso W 1).inv ≫
        (discreteSourceMapping W).map SSet.coherentIso.forwardIso.inv.op := by
  change ((EquivalenceMapping.yonedaIsoOne W hW).inv ≫
    EquivalenceMapping.restriction W hW SSet.coherentIso.forwardIso.inv) ≫ _ = _
  rw [Category.assoc, EquivalenceMapping.restriction_ι, ← Category.assoc,
    EquivalenceMapping.yonedaIsoOne_inv_ι, Category.assoc]

/-- The canonical zero projection is the same original full-E forward evaluation. -/
theorem mappingTowerCone_zero (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (mappingTowerCone W hW).π.app (op 0) ≫ (mappingTowerZeroIso W hW).hom =
      evaluation W hW SSet.coherentIso.forwardMap := by
  apply (cancel_mono (SegalHomotopy.equivalenceSubcomplex W hW).ι).mp
  calc
    _ = (mappingTowerCone W hW).π.app (op 0) ≫
        ((mappingTowerZeroIso W hW).hom ≫
          (SegalHomotopy.equivalenceSubcomplex W hW).ι) := Category.assoc _ _ _
    _ = (mappingTowerCone W hW).π.app (op 0) ≫
        ((EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage 1)).ι ≫
          (discreteSourceMapping W).map SSet.coherentIso.forwardIso.hom.op ≫
            (discreteYonedaIso W 1).hom) := by rw [mappingTowerZeroIso_hom_ι]
    _ = ((mappingTowerCone W hW).π.app (op 0) ≫
        (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage 1)).ι) ≫
          (discreteSourceMapping W).map SSet.coherentIso.forwardIso.hom.op ≫
            (discreteYonedaIso W 1).hom := by simp only [Category.assoc]
    _ = (discreteSourceMapping W).map (SSet.coherentIso.stage 1).ι.op ≫
        (discreteSourceMapping W).map SSet.coherentIso.forwardIso.hom.op ≫
          (discreteYonedaIso W 1).hom := by rw [mappingTowerCone_π_ι W hW 0]
    _ = EquivalenceMapping.edgeEvaluation W SSet.coherentIso.forwardMap := by
      rw [← Category.assoc, ← (discreteSourceMapping W).map_comp, ← op_comp,
        SSet.coherentIso.forwardIso_hom_ι]
      rfl
    _ = _ := (evaluation_ι W hW SSet.coherentIso.forwardMap).symm

@[implicit_reducible]
private def selectedMappingTowerMap {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) : mappingTower W hW ⟶ mappingTower V hV where
  app n := EquivalenceMapping.targetMap q hW hV (SSet.coherentIso.stage (n.unop + 1))
  naturality := by
    intro n m f
    exact (EquivalenceMapping.restriction_targetMap q hW hV (shiftedStages.map f.unop)).symm

/-- Every original target arrow acts on every original selected tower object. -/
def mappingTowerMap {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) : mappingTower W hW ⟶ mappingTower V hV :=
  selectedMappingTowerMap q hW hV

/-- Every target-map component is the same existing original target action. -/
theorem mappingTowerMap_app {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) (n : ℕ) :
    (mappingTowerMap q hW hV).app (op n) =
      EquivalenceMapping.targetMap q hW hV (SSet.coherentIso.stage (n + 1)) := rfl

/-- The canonical cone preserves the original full-E target-map square at every stage. -/
theorem mappingTowerCone_naturality_target {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) (n : ℕ) :
    (discreteSourceMappingMap q).app (op SSet.coherentIso) ≫ (mappingTowerCone V hV).π.app (op n) =
      (mappingTowerCone W hW).π.app (op n) ≫ (mappingTowerMap q hW hV).app (op n) := by
  apply (cancel_mono (EquivalenceMapping.subcomplex V hV (SSet.coherentIso.stage (n + 1))).ι).mp
  calc
    _ = (discreteSourceMappingMap q).app (op SSet.coherentIso) ≫
        ((mappingTowerCone V hV).π.app (op n) ≫
          (EquivalenceMapping.subcomplex V hV (SSet.coherentIso.stage (n + 1))).ι) :=
      Category.assoc _ _ _
    _ = (discreteSourceMappingMap q).app (op SSet.coherentIso) ≫
        (discreteSourceMapping V).map (SSet.coherentIso.stage (n + 1)).ι.op := by
      rw [mappingTowerCone_π_ι]
    _ = (discreteSourceMapping W).map (SSet.coherentIso.stage (n + 1)).ι.op ≫
        (discreteSourceMappingMap q).app (op (SSet.coherentIso.stage (n + 1) : SSet.{u})) :=
      ((discreteSourceMappingMap q).naturality (SSet.coherentIso.stage (n + 1)).ι.op).symm
    _ = ((mappingTowerCone W hW).π.app (op n) ≫
        (EquivalenceMapping.subcomplex W hW (SSet.coherentIso.stage (n + 1))).ι) ≫
          (discreteSourceMappingMap q).app (op (SSet.coherentIso.stage (n + 1) : SSet.{u})) := by
      rw [mappingTowerCone_π_ι]
    _ = (mappingTowerCone W hW).π.app (op n) ≫
        ((mappingTowerMap q hW hV).app (op n) ≫
          (EquivalenceMapping.subcomplex V hV (SSet.coherentIso.stage (n + 1))).ι) := by
      rw [mappingTowerMap_app, EquivalenceMapping.targetMap_ι, Category.assoc]
    _ = _ := (Category.assoc _ _ _).symm

/-- The forward zero isomorphism retains the original whole target square. -/
theorem mappingTowerZeroIso_naturality_target {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    (mappingTowerMap q hW hV).app (op 0) ≫ (mappingTowerZeroIso V hV).hom =
      (mappingTowerZeroIso W hW).hom ≫ SegalHomotopy.equivalenceMap q hW hV := by
  change EquivalenceMapping.targetMap q hW hV (SSet.coherentIso.stage 1) ≫
      (EquivalenceMapping.restriction V hV SSet.coherentIso.forwardIso.hom ≫
        (EquivalenceMapping.yonedaIsoOne V hV).hom) =
    (EquivalenceMapping.restriction W hW SSet.coherentIso.forwardIso.hom ≫
      (EquivalenceMapping.yonedaIsoOne W hW).hom) ≫ _
  rw [← Category.assoc, EquivalenceMapping.restriction_targetMap, Category.assoc,
    EquivalenceMapping.yonedaIsoOne_naturality_target, ← Category.assoc]

/-- The inverse zero isomorphism retains the original other target square. -/
theorem mappingTowerZeroIso_inv_naturality_target {W V : SimplicialSpace.{u}} (q : W ⟶ V)
    (hW : segalSpaces W) (hV : segalSpaces V) :
    SegalHomotopy.equivalenceMap q hW hV ≫ (mappingTowerZeroIso V hV).inv =
      (mappingTowerZeroIso W hW).inv ≫ (mappingTowerMap q hW hV).app (op 0) := by
  apply (cancel_mono (mappingTowerZeroIso V hV).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    mappingTowerZeroIso_naturality_target, Iso.inv_hom_id_assoc]

end SimplicialSpace.FullEEquivalence
