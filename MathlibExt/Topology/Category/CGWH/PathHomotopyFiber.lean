/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Path
public import MathlibExt.Topology.Category.CGWH.BasedFiber
public import MathlibExt.Topology.Category.PointedCGWH.Basic

/-!
# Native mapping-path fibers in CGWH

This file constructs ending paths and explicit mapping-path fibers from the
native CGWH path functor.  It packages the constructions functorially and
compares strict fibers to mapping-path fibers by constant paths.  Everything
here is independent of the selected model structure.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits

namespace CGWH.BasedArrow

/-- A based arrow determines the pointed object given by its base and chosen
point. -/
noncomputable abbrev pointedBase :
    CGWH.BasedArrow.{u, v} ⥤ PointedCGWH.{u, v} where
  obj F := Under.mk F.point
  map {F G} phi := Under.homMk phi.right.right (by
    change F.point ≫ phi.right.right = G.point
    exact StructuredArrow.w phi)
  map_id F := by
    apply Under.UnderMorphism.ext
    rfl
  map_comp phi psi := by
    apply Under.UnderMorphism.ext
    rfl

end CGWH.BasedArrow

namespace PointedCGWH

/-- Paths ending at the selected point of a pointed CGWH space. -/
noncomputable abbrev endingPath :
    PointedCGWH.{u, v} ⥤ CGWH.{u, v} where
  obj X := pullback (CGWH.pathEvalOne.app X.right) X.hom
  map {X Y} g := pullback.lift
    (pullback.fst (CGWH.pathEvalOne.app X.right) X.hom ≫
      CGWH.path.map g.right)
    (pullback.snd (CGWH.pathEvalOne.app X.right) X.hom)
    (by
      rw [Category.assoc, CGWH.pathEvalOne.naturality]
      rw [← Category.assoc, pullback.condition]
      rw [Category.assoc]
      simp only [Functor.id_map]
      rw [Under.w g])
  map_id X := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      simp
    · rw [pullback.lift_snd]
      simp
  map_comp {X Y Z} g h := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      rw [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, pullback.lift_fst]
      simp [CGWH.path.map_comp, Category.assoc]
    · rw [pullback.lift_snd]
      rw [Category.assoc, pullback.lift_snd]
      rw [pullback.lift_snd]

/-- An ending path projects to its underlying native path. -/
noncomputable abbrev endingPathToPath :
    endingPath.{u, v} ⟶
      pointedToCGWH.{u, v} ⋙ CGWH.path.{u, v} where
  app X := pullback.fst (CGWH.pathEvalOne.app X.right) X.hom
  naturality X Y g := by
    change endingPath.map g ≫
        pullback.fst (CGWH.pathEvalOne.app Y.right) Y.hom =
      pullback.fst (CGWH.pathEvalOne.app X.right) X.hom ≫
        CGWH.path.map g.right
    exact pullback.lift_fst _ _ _

/-- An ending path projects to the point object. -/
noncomputable abbrev endingPathToPoint :
    endingPath.{u, v} ⟶
      (Functor.const PointedCGWH.{u, v}).obj CGWH.point.{u, v} where
  app X := pullback.snd (CGWH.pathEvalOne.app X.right) X.hom
  naturality X Y g := by
    change endingPath.map g ≫
        pullback.snd (CGWH.pathEvalOne.app Y.right) Y.hom =
      pullback.snd (CGWH.pathEvalOne.app X.right) X.hom ≫
        𝟙 CGWH.point.{u, v}
    simp

/-- The starting point of an ending path. -/
noncomputable abbrev endingPathStart :
    endingPath.{u, v} ⟶ pointedToCGWH.{u, v} where
  app X := endingPathToPath.app X ≫ CGWH.pathEvalZero.app X.right
  naturality X Y g := by
    change endingPath.map g ≫
        (pullback.fst (CGWH.pathEvalOne.app Y.right) Y.hom ≫
          CGWH.pathEvalZero.app Y.right) =
      (pullback.fst (CGWH.pathEvalOne.app X.right) X.hom ≫
        CGWH.pathEvalZero.app X.right) ≫ g.right
    rw [← Category.assoc, pullback.lift_fst, Category.assoc,
      CGWH.pathEvalZero.naturality]
    simp only [Functor.id_map, Category.assoc]

/-- The selected point determines the constant ending path. -/
noncomputable abbrev endingPathPoint :
    (Functor.const PointedCGWH.{u, v}).obj CGWH.point.{u, v} ⟶
      endingPath.{u, v} where
  app X := pullback.lift
    (X.hom ≫ CGWH.pathConstant.app X.right)
    (𝟙 CGWH.point.{u, v})
    (by
      calc
        (X.hom ≫ CGWH.pathConstant.app X.right) ≫
            CGWH.pathEvalOne.app X.right = X.hom := by
          rw [Category.assoc, CGWH.pathConstant_evalOne,
            Category.comp_id]
        _ = 𝟙 CGWH.point.{u, v} ≫ X.hom :=
          (Category.id_comp X.hom).symm)
  naturality X Y g := by
    change (𝟙 CGWH.point.{u, v}) ≫
        pullback.lift
          (Y.hom ≫ CGWH.pathConstant.app Y.right)
          (𝟙 CGWH.point.{u, v}) _ =
      pullback.lift
          (X.hom ≫ CGWH.pathConstant.app X.right)
          (𝟙 CGWH.point.{u, v}) _ ≫ endingPath.map g
    apply pullback.hom_ext
    · rw [Category.id_comp]
      rw [pullback.lift_fst]
      rw [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, pullback.lift_fst]
      have hConstant : g.right ≫ CGWH.pathConstant.app Y.right =
          CGWH.pathConstant.app X.right ≫ CGWH.path.map g.right := by
        simpa only [Functor.id_map] using
          CGWH.pathConstant.naturality g.right
      rw [← Under.w g, Category.assoc, hConstant,
        ← Category.assoc]
    · rw [Category.id_comp]
      rw [pullback.lift_snd]
      rw [Category.assoc, pullback.lift_snd]
      rw [pullback.lift_snd]

/-- The path projection followed by time-zero evaluation is the start map. -/
theorem endingPathToPath_evalZero (X : PointedCGWH.{u, v}) :
    endingPathToPath.app X ≫ CGWH.pathEvalZero.app X.right =
      endingPathStart.app X :=
  rfl

/-- The path projection followed by time-one evaluation is the selected
point. -/
theorem endingPathToPath_evalOne (X : PointedCGWH.{u, v}) :
    endingPathToPath.app X ≫ CGWH.pathEvalOne.app X.right =
      endingPathToPoint.app X ≫ X.hom :=
  pullback.condition

/-- The canonical constant ending path starts at the selected point. -/
theorem endingPathPoint_start (X : PointedCGWH.{u, v}) :
    endingPathPoint.app X ≫ endingPathStart.app X = X.hom := by
  unfold endingPathPoint endingPathStart endingPathToPath
  change pullback.lift
        (X.hom ≫ CGWH.pathConstant.app X.right)
        (𝟙 CGWH.point.{u, v}) _ ≫
      (pullback.fst (CGWH.pathEvalOne.app X.right) X.hom ≫
        CGWH.pathEvalZero.app X.right) = X.hom
  rw [← Category.assoc, pullback.lift_fst, Category.assoc,
    CGWH.pathConstant_evalZero, Category.comp_id]

/-- The path of the canonical ending point is the constant path. -/
theorem endingPathPoint_toPath (X : PointedCGWH.{u, v}) :
    endingPathPoint.app X ≫ endingPathToPath.app X =
      X.hom ≫ CGWH.pathConstant.app X.right := by
  unfold endingPathPoint endingPathToPath
  exact pullback.lift_fst _ _ _

/-- The point projection of the canonical ending point is the identity. -/
theorem endingPathPoint_toPoint (X : PointedCGWH.{u, v}) :
    endingPathPoint.app X ≫ endingPathToPoint.app X =
      𝟙 CGWH.point.{u, v} := by
  unfold endingPathPoint endingPathToPoint
  exact pullback.lift_snd _ _ _

end PointedCGWH

namespace CGWH

/-- The cospan defining the mapping-path fiber of a based arrow. -/
noncomputable abbrev pathFiberCospan :
    BasedArrow.{u, v} ⥤ (WalkingCospan ⥤ CGWH.{u, v}) where
  obj F := cospan F.map
    (PointedCGWH.endingPathStart.app (BasedArrow.pointedBase.obj F))
  map {F G} phi := cospanHomMk
    phi.right.right phi.right.left
    (PointedCGWH.endingPath.map (BasedArrow.pointedBase.map phi))
    (Arrow.w phi.right).symm
    (by
      change PointedCGWH.endingPathStart.app
            (BasedArrow.pointedBase.obj F) ≫ phi.right.right =
        PointedCGWH.endingPath.map (BasedArrow.pointedBase.map phi) ≫
          PointedCGWH.endingPathStart.app
            (BasedArrow.pointedBase.obj G)
      exact (PointedCGWH.endingPathStart.naturality
        (BasedArrow.pointedBase.map phi)).symm)
  map_id F := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · rfl
    · rfl
    · exact PointedCGWH.endingPath.map_id
        (BasedArrow.pointedBase.obj F)
  map_comp {F G H} phi psi := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · rfl
    · rfl
    · dsimp only [cospanHomMk]
      change PointedCGWH.endingPath.map
          (BasedArrow.pointedBase.map (phi ≫ psi)) =
        PointedCGWH.endingPath.map (BasedArrow.pointedBase.map phi) ≫
          PointedCGWH.endingPath.map (BasedArrow.pointedBase.map psi)
      rw [BasedArrow.pointedBase.map_comp,
        PointedCGWH.endingPath.map_comp]

/-- The functor assigning to a based arrow its explicit mapping-path fiber. -/
noncomputable abbrev mappingPathFiber :
    BasedArrow.{u, v} ⥤ CGWH.{u, v} :=
  pathFiberCospan ⋙ lim

/-- The mapping-path fiber projects to the total space. -/
noncomputable abbrev mappingPathFiberToTotal :
    mappingPathFiber.{u, v} ⟶
      StructuredArrow.proj CGWH.point.{u, v}
          (Arrow.rightFunc : Arrow CGWH.{u, v} ⥤ CGWH.{u, v}) ⋙
        Arrow.leftFunc where
  app F := limit.π (pathFiberCospan.obj F) WalkingCospan.left
  naturality F G phi := by
    change lim.map (pathFiberCospan.map phi) ≫
        limit.π (pathFiberCospan.obj G) WalkingCospan.left =
      limit.π (pathFiberCospan.obj F) WalkingCospan.left ≫
        phi.right.left
    rw [limit.map_π]
    rfl

/-- The mapping-path fiber projects to the ending-path object. -/
noncomputable abbrev mappingPathFiberToEndingPath :
    mappingPathFiber.{u, v} ⟶
      BasedArrow.pointedBase.{u, v} ⋙
        PointedCGWH.endingPath.{u, v} where
  app F := limit.π (pathFiberCospan.obj F) WalkingCospan.right
  naturality F G phi := by
    change lim.map (pathFiberCospan.map phi) ≫
        limit.π (pathFiberCospan.obj G) WalkingCospan.right =
      limit.π (pathFiberCospan.obj F) WalkingCospan.right ≫
        PointedCGWH.endingPath.map (BasedArrow.pointedBase.map phi)
    rw [limit.map_π]
    rfl

/-- The path coordinate of the mapping-path fiber. -/
noncomputable abbrev mappingPathFiberPath :
    mappingPathFiber.{u, v} ⟶
      BasedArrow.pointedBase.{u, v} ⋙
        (PointedCGWH.pointedToCGWH.{u, v} ⋙ path.{u, v}) :=
  mappingPathFiberToEndingPath ≫
    Functor.whiskerLeft BasedArrow.pointedBase
      PointedCGWH.endingPathToPath

/-- The point coordinate of the mapping-path fiber. -/
noncomputable abbrev mappingPathFiberToPoint :
    mappingPathFiber.{u, v} ⟶
      BasedArrow.pointedBase.{u, v} ⋙
        (Functor.const PointedCGWH.{u, v}).obj CGWH.point.{u, v} :=
  mappingPathFiberToEndingPath ≫
    Functor.whiskerLeft BasedArrow.pointedBase
      PointedCGWH.endingPathToPoint

/-- The total and ending-path projections satisfy the cospan equation. -/
theorem mappingPathFiberToTotal_map (F : BasedArrow.{u, v}) :
    mappingPathFiberToTotal.app F ≫ F.map =
      mappingPathFiberToEndingPath.app F ≫
        PointedCGWH.endingPathStart.app (BasedArrow.pointedBase.obj F) := by
  change limit.π (pathFiberCospan.obj F) WalkingCospan.left ≫
      (pathFiberCospan.obj F).map WalkingCospan.Hom.inl =
    limit.π (pathFiberCospan.obj F) WalkingCospan.right ≫
      (pathFiberCospan.obj F).map WalkingCospan.Hom.inr
  rw [limit.w, limit.w]

/-- The path coordinate starts at the image of the total coordinate. -/
theorem mappingPathFiberPath_evalZero (F : BasedArrow.{u, v}) :
    mappingPathFiberPath.app F ≫ pathEvalZero.app F.base =
      mappingPathFiberToTotal.app F ≫ F.map := by
  unfold mappingPathFiberPath mappingPathFiberToEndingPath
  unfold PointedCGWH.endingPathToPath
  change (limit.π (pathFiberCospan.obj F) WalkingCospan.right ≫
      pullback.fst (pathEvalOne.app F.base) F.point) ≫
      pathEvalZero.app F.base = mappingPathFiberToTotal.app F ≫ F.map
  rw [Category.assoc]
  exact (mappingPathFiberToTotal_map F).symm

/-- The path coordinate ends at the chosen point. -/
theorem mappingPathFiberPath_evalOne (F : BasedArrow.{u, v}) :
    mappingPathFiberPath.app F ≫ pathEvalOne.app F.base =
      mappingPathFiberToPoint.app F ≫ F.point := by
  unfold mappingPathFiberPath mappingPathFiberToPoint
  unfold mappingPathFiberToEndingPath
  unfold PointedCGWH.endingPathToPath PointedCGWH.endingPathToPoint
  change (limit.π (pathFiberCospan.obj F) WalkingCospan.right ≫
      pullback.fst (pathEvalOne.app F.base) F.point) ≫
      pathEvalOne.app F.base =
    (limit.π (pathFiberCospan.obj F) WalkingCospan.right ≫
      pullback.snd (pathEvalOne.app F.base) F.point) ≫ F.point
  rw [Category.assoc, pullback.condition, Category.assoc]

/-- Constant ending paths define a natural transformation from strict-fiber
cospans to mapping-path-fiber cospans. -/
noncomputable abbrev basedToPathFiberCospan :
    basedFiberCospanFunctor.{u, v} ⟶ pathFiberCospan.{u, v} where
  app F := by
    unfold basedFiberCospanFunctor
    exact cospanHomMk (𝟙 F.base) (𝟙 F.total)
      (PointedCGWH.endingPathPoint.app (BasedArrow.pointedBase.obj F))
      (by
        change F.map ≫ 𝟙 F.base = 𝟙 F.total ≫ F.map
        simp)
      (by
        change F.point ≫ 𝟙 F.base =
          PointedCGWH.endingPathPoint.app
              (BasedArrow.pointedBase.obj F) ≫
            PointedCGWH.endingPathStart.app
              (BasedArrow.pointedBase.obj F)
        simpa using (PointedCGWH.endingPathPoint_start
          (BasedArrow.pointedBase.obj F)).symm)
  naturality F G phi := by
    unfold basedFiberCospanFunctor
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · change phi.right.right ≫ 𝟙 G.base =
        𝟙 F.base ≫ phi.right.right
      simp
    · change phi.right.left ≫ 𝟙 G.total =
        𝟙 F.total ≫ phi.right.left
      simp
    · change (𝟙 CGWH.point.{u, v}) ≫
          PointedCGWH.endingPathPoint.app
            (BasedArrow.pointedBase.obj G) =
        PointedCGWH.endingPathPoint.app
            (BasedArrow.pointedBase.obj F) ≫
          PointedCGWH.endingPath.map (BasedArrow.pointedBase.map phi)
      simpa using PointedCGWH.endingPathPoint.naturality
        (BasedArrow.pointedBase.map phi)

/-- Include a strict fiber into the mapping-path fiber by constant paths. -/
noncomputable abbrev strictFiberToMappingPathFiber :
    strictFiberFunctor.{u, v} ⟶ mappingPathFiber.{u, v} :=
  Functor.whiskerRight basedToPathFiberCospan lim

/-- The strict inclusion preserves the total-space projection. -/
theorem strictFiberToMappingPathFiber_toTotal
    (F : BasedArrow.{u, v}) :
    strictFiberToMappingPathFiber.app F ≫
      mappingPathFiberToTotal.app F =
      strictFiberToTotalNatTrans.app F := by
  rw [strictFiberToTotalNatTrans_app]
  unfold strictFiberToMappingPathFiber mappingPathFiberToTotal
  unfold basedFiberCospanFunctor
  unfold basedFiberCospan
  unfold basedToPathFiberCospan
  change lim.map (basedToPathFiberCospan.app F) ≫
      limit.π (pathFiberCospan.obj F) WalkingCospan.left =
    limit.π (cospan F.map F.point) WalkingCospan.left
  rw [limit.map_π]
  change limit.π (cospan F.map F.point) WalkingCospan.left ≫
      𝟙 F.total = _
  simp

/-- The strict inclusion preserves the point projection. -/
theorem strictFiberToMappingPathFiber_toPoint
    (F : BasedArrow.{u, v}) :
    strictFiberToMappingPathFiber.app F ≫
      mappingPathFiberToPoint.app F =
      strictFiberToPointNatTrans.app F := by
  rw [strictFiberToPointNatTrans_app]
  unfold strictFiberToMappingPathFiber mappingPathFiberToPoint
  unfold mappingPathFiberToEndingPath
  unfold basedFiberCospanFunctor
  unfold basedFiberCospan
  unfold basedToPathFiberCospan
  change lim.map (basedToPathFiberCospan.app F) ≫
      (limit.π (pathFiberCospan.obj F) WalkingCospan.right ≫
        PointedCGWH.endingPathToPoint.app
          (BasedArrow.pointedBase.obj F)) =
    limit.π (cospan F.map F.point) WalkingCospan.right
  rw [← Category.assoc, limit.map_π]
  change (limit.π (cospan F.map F.point)
      WalkingCospan.right ≫
        PointedCGWH.endingPathPoint.app
          (BasedArrow.pointedBase.obj F)) ≫
      PointedCGWH.endingPathToPoint.app
        (BasedArrow.pointedBase.obj F) = _
  rw [Category.assoc,
    PointedCGWH.endingPathPoint_toPoint]
  exact Category.comp_id _

/-- The strict inclusion has the constant path at the chosen point. -/
theorem strictFiberToMappingPathFiber_path
    (F : BasedArrow.{u, v}) :
    strictFiberToMappingPathFiber.app F ≫
        mappingPathFiberPath.app F =
      strictFiberToPointNatTrans.app F ≫ F.point ≫
        pathConstant.app F.base := by
  rw [strictFiberToPointNatTrans_app]
  unfold strictFiberToMappingPathFiber mappingPathFiberPath
  unfold mappingPathFiberToEndingPath
  unfold basedFiberCospanFunctor
  unfold basedFiberCospan
  unfold basedToPathFiberCospan
  change lim.map (basedToPathFiberCospan.app F) ≫
      (limit.π (pathFiberCospan.obj F) WalkingCospan.right ≫
        PointedCGWH.endingPathToPath.app
          (BasedArrow.pointedBase.obj F)) =
    limit.π (cospan F.map F.point) WalkingCospan.right ≫
      F.point ≫ pathConstant.app F.base
  rw [← Category.assoc, limit.map_π]
  change (limit.π (cospan F.map F.point)
      WalkingCospan.right ≫
        PointedCGWH.endingPathPoint.app
          (BasedArrow.pointedBase.obj F)) ≫
      PointedCGWH.endingPathToPath.app
        (BasedArrow.pointedBase.obj F) = _
  rw [Category.assoc,
    PointedCGWH.endingPathPoint_toPath]
  change limit.π (cospan F.map F.point) WalkingCospan.right ≫
      F.point ≫ pathConstant.app F.base = _
  rfl

end CGWH
