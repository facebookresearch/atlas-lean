/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.CGWH.BasedContraction
import MathlibExt.Topology.Category.PointedCGWH.BasedFiber
import MathlibExt.Topology.Category.PointedCGWH.ZeroMappingPathFiber

/-!
# Maps from strict fibers to based path loops

An explicit based contraction of the total space constructs a pointed map from the
strict fiber to the zero mapping-path fiber of the base. Its path component is the
projected contraction, and the map is natural in commutative squares preserving the
basepoints, lifted points and contractions.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits

namespace PointedCGWH

private noncomputable def strictFiberEndingPath
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (over : e ≫ p = b)
    (H : CGWH.BasedContraction E e) :
    CGWH.strictFiber p b ⟶ pullback (CGWH.pathEvalOne.app B) b :=
  pullback.lift
    (CGWH.strictFiberToTotal p b ≫ H.projectedPath p)
    (CGWH.strictFiberToPoint p b)
    (by
      change CGWH.strictFiberToTotal p b ≫ H.projectedPath p ≫
          CGWH.pathEvalOne.app B = CGWH.strictFiberToPoint p b ≫ b
      rw [H.projectedPath_evalOne p b over]
      rw [← Category.assoc]
      have hpoint :
          CGWH.strictFiberToTotal p b ≫ CGWH.point_isTerminal.from E =
            CGWH.strictFiberToPoint p b :=
        CGWH.point_isTerminal.hom_ext _ _
      rw [hpoint])

private theorem strictFiberEndingPath_toPath
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (over : e ≫ p = b)
    (H : CGWH.BasedContraction E e) :
    strictFiberEndingPath p b e over H ≫
        pullback.fst (CGWH.pathEvalOne.app B) b =
      CGWH.strictFiberToTotal p b ≫ H.projectedPath p :=
  pullback.lift_fst _ _ _

private noncomputable def strictFiberToPathLoopRight
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (over : e ≫ p = b)
    (H : CGWH.BasedContraction E e) :
    CGWH.strictFiber p b ⟶
      pullback b
        (pullback.fst (CGWH.pathEvalOne.app B) b ≫
          CGWH.pathEvalZero.app B) :=
  pullback.lift
    (CGWH.strictFiberToPoint p b)
    (strictFiberEndingPath p b e over H)
    (by
      change CGWH.strictFiberToPoint p b ≫ b =
        strictFiberEndingPath p b e over H ≫
          (pullback.fst (CGWH.pathEvalOne.app B) b ≫
            CGWH.pathEvalZero.app B)
      rw [← Category.assoc, strictFiberEndingPath_toPath]
      rw [Category.assoc, H.projectedPath_evalZero]
      exact (CGWH.strictFiber_condition p b).symm)

private theorem strictFiberToPathLoopRight_point
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (over : e ≫ p = b)
    (H : CGWH.BasedContraction E e) :
    CGWH.strictFiberPoint p b e over ≫
        strictFiberToPathLoopRight p b e over H =
      zeroMappingPathFiberPoint.app (Under.mk b) := by
  let zeroPoint : CGWH.point.{u, v} ⟶
        pullback b
          (pullback.fst (CGWH.pathEvalOne.app B) b ≫
            CGWH.pathEvalZero.app B) :=
    zeroMappingPathFiberPoint.app (Under.mk b)
  have zeroPoint_toTotal :
      zeroPoint ≫ pullback.fst b
          (pullback.fst (CGWH.pathEvalOne.app B) b ≫
            CGWH.pathEvalZero.app B) = 𝟙 CGWH.point.{u, v} := by
    change zeroMappingPathFiberPoint.app (Under.mk b) ≫
        CGWH.mappingPathFiberToTotal.app (zeroBasedArrow.obj (Under.mk b)) =
      𝟙 CGWH.point.{u, v}
    exact zeroMappingPathFiber_point_toTotal (Under.mk b)
  have zeroPoint_path :
      zeroPoint ≫ pullback.snd b
          (pullback.fst (CGWH.pathEvalOne.app B) b ≫
            CGWH.pathEvalZero.app B) ≫
        pullback.fst (CGWH.pathEvalOne.app B) b =
      b ≫ CGWH.pathConstant.app B := by
    change zeroMappingPathFiberPoint.app (Under.mk b) ≫
        CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj (Under.mk b)) =
      b ≫ CGWH.pathConstant.app B
    exact zeroMappingPathFiber_point_path (Under.mk b)
  have right_toTotal :
      strictFiberToPathLoopRight p b e over H ≫
          pullback.fst b
            (pullback.fst (CGWH.pathEvalOne.app B) b ≫
              CGWH.pathEvalZero.app B) =
        CGWH.strictFiberToPoint p b :=
    pullback.lift_fst _ _ _
  have right_toEndingPath :
      strictFiberToPathLoopRight p b e over H ≫
          pullback.snd b
            (pullback.fst (CGWH.pathEvalOne.app B) b ≫
              CGWH.pathEvalZero.app B) =
        strictFiberEndingPath p b e over H :=
    pullback.lift_snd _ _ _
  change CGWH.strictFiberPoint p b e over ≫
      strictFiberToPathLoopRight p b e over H = zeroPoint
  apply pullback.hom_ext
  · rw [Category.assoc, right_toTotal,
      CGWH.strictFiberPoint_toPoint, zeroPoint_toTotal]
  · apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [← Category.assoc
          (strictFiberToPathLoopRight p b e over H)
          (pullback.snd b
            (pullback.fst (CGWH.pathEvalOne.app B) b ≫
              CGWH.pathEvalZero.app B))
          (pullback.fst (CGWH.pathEvalOne.app B) b),
        right_toEndingPath,
        strictFiberEndingPath_toPath]
      rw [← Category.assoc, CGWH.strictFiberPoint_toTotal,
        H.projectedPath_fixed p b over]
      simpa only [Category.assoc] using zeroPoint_path.symm
    · exact CGWH.point_isTerminal.hom_ext _ _

/-- The model-free pointed map from the strict fiber to the explicit zero
mapping-path fiber supplied by an explicit based contraction. -/
noncomputable def strictFiberToPathLoop
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (over : e ≫ p = b)
    (H : CGWH.BasedContraction E e) :
    strictFiberPointed p b e over ⟶ zeroMappingPathFiber.obj (Under.mk b) :=
  Under.homMk (strictFiberToPathLoopRight p b e over H)
    (strictFiberToPathLoopRight_point p b e over H)

/-- The total coordinate of the F0 map is the point projection. -/
theorem strictFiberToPathLoop_toTotal
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (over : e ≫ p = b)
    (H : CGWH.BasedContraction E e) :
    (strictFiberToPathLoop p b e over H).right ≫
        CGWH.mappingPathFiberToTotal.app (zeroBasedArrow.obj (Under.mk b)) =
      CGWH.strictFiberToPoint p b :=
  pullback.lift_fst _ _ _

/-- The path coordinate of the F0 map is the projected contraction path. -/
theorem strictFiberToPathLoop_path
    {E B : CGWH.{u, v}} (p : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (over : e ≫ p = b)
    (H : CGWH.BasedContraction E e) :
    (strictFiberToPathLoop p b e over H).right ≫
        CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj (Under.mk b)) =
      CGWH.strictFiberToTotal p b ≫ H.projectedPath p := by
  change strictFiberToPathLoopRight p b e over H ≫
      (pullback.snd b
          (pullback.fst (CGWH.pathEvalOne.app B) b ≫
            CGWH.pathEvalZero.app B) ≫
        pullback.fst (CGWH.pathEvalOne.app B) b) = _
  rw [← Category.assoc]
  unfold strictFiberToPathLoopRight
  rw [pullback.lift_snd,
    strictFiberEndingPath_toPath]

private noncomputable def zeroMappingPathFiberMapRight
    {B B' : CGWH.{u, v}}
    {b : CGWH.point.{u, v} ⟶ B}
    {b' : CGWH.point.{u, v} ⟶ B'}
    (d : B ⟶ B') (base : b ≫ d = b') :
    pullback b
          (pullback.fst (CGWH.pathEvalOne.app B) b ≫
            CGWH.pathEvalZero.app B) ⟶
      pullback b'
          (pullback.fst (CGWH.pathEvalOne.app B') b' ≫
            CGWH.pathEvalZero.app B') :=
  CGWH.mappingPathFiber.map
    (zeroBasedArrow.map
      (Under.homMk d base :
        (Under.mk b : PointedCGWH.{u, v}) ⟶ Under.mk b'))

private theorem zeroMappingPathFiberMapRight_path
    {B B' : CGWH.{u, v}}
    {b : CGWH.point.{u, v} ⟶ B}
    {b' : CGWH.point.{u, v} ⟶ B'}
    (d : B ⟶ B') (base : b ≫ d = b') :
    (zeroMappingPathFiberMapRight d base ≫
        pullback.snd b'
          (pullback.fst (CGWH.pathEvalOne.app B') b' ≫
            CGWH.pathEvalZero.app B')) ≫
      pullback.fst (CGWH.pathEvalOne.app B') b' =
    (pullback.snd b
          (pullback.fst (CGWH.pathEvalOne.app B) b ≫
            CGWH.pathEvalZero.app B) ≫
        pullback.fst (CGWH.pathEvalOne.app B) b) ≫
      CGWH.path.map d := by
  let pointedMap : (Under.mk b : PointedCGWH.{u, v}) ⟶ Under.mk b' :=
    Under.homMk d base
  change CGWH.mappingPathFiber.map (zeroBasedArrow.map pointedMap) ≫
      CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj (Under.mk b')) =
    CGWH.mappingPathFiberPath.app (zeroBasedArrow.obj (Under.mk b)) ≫
      CGWH.path.map d
  exact CGWH.mappingPathFiberPath.naturality (zeroBasedArrow.map pointedMap)

private theorem strictFiberToPathLoopRight_naturality_toTotal
    {E B E' B' : CGWH.{u, v}}
    {p : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {e : CGWH.point.{u, v} ⟶ E} (over : e ≫ p = b)
    (H : CGWH.BasedContraction E e)
    {p' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    {e' : CGWH.point.{u, v} ⟶ E'} (over' : e' ≫ p' = b')
    (H' : CGWH.BasedContraction E' e')
    (a : E ⟶ E') (d : B ⟶ B')
    (square : a ≫ p' = p ≫ d) (base : b ≫ d = b')
    :
    (CGWH.strictFiberMap a d square base ≫
          strictFiberToPathLoopRight p' b' e' over' H') ≫
        pullback.fst b'
          (pullback.fst (CGWH.pathEvalOne.app B') b' ≫
            CGWH.pathEvalZero.app B') =
      (strictFiberToPathLoopRight p b e over H ≫
          zeroMappingPathFiberMapRight d base) ≫
        pullback.fst b'
          (pullback.fst (CGWH.pathEvalOne.app B') b' ≫
            CGWH.pathEvalZero.app B') := by
  have zeroMap_toTotal :
      zeroMappingPathFiberMapRight d base ≫
          pullback.fst b'
            (pullback.fst (CGWH.pathEvalOne.app B') b' ≫
              CGWH.pathEvalZero.app B') =
        pullback.fst b
          (pullback.fst (CGWH.pathEvalOne.app B) b ≫
            CGWH.pathEvalZero.app B) := by
    change CGWH.mappingPathFiber.map
          (zeroBasedArrow.map
            (Under.homMk d base :
              (Under.mk b : PointedCGWH.{u, v}) ⟶ Under.mk b')) ≫
        CGWH.mappingPathFiberToTotal.app (zeroBasedArrow.obj (Under.mk b')) =
      CGWH.mappingPathFiberToTotal.app (zeroBasedArrow.obj (Under.mk b))
    rw [CGWH.mappingPathFiberToTotal.naturality]
    rfl
  simp only [Category.assoc]
  unfold strictFiberToPathLoopRight
  rw [pullback.lift_fst, CGWH.strictFiberMap_toPoint,
    zeroMap_toTotal, pullback.lift_fst]

private theorem strictFiberToPathLoopRight_naturality_toPath
    {E B E' B' : CGWH.{u, v}}
    {p : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {e : CGWH.point.{u, v} ⟶ E} (over : e ≫ p = b)
    (H : CGWH.BasedContraction E e)
    {p' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    {e' : CGWH.point.{u, v} ⟶ E'} (over' : e' ≫ p' = b')
    (H' : CGWH.BasedContraction E' e')
    (a : E ⟶ E') (d : B ⟶ B')
    (square : a ≫ p' = p ≫ d) (base : b ≫ d = b')
    (contraction : H.path ≫ CGWH.path.map a = a ≫ H'.path) :
    (CGWH.strictFiberMap a d square base ≫
          strictFiberToPathLoopRight p' b' e' over' H') ≫
        pullback.snd b'
          (pullback.fst (CGWH.pathEvalOne.app B') b' ≫
            CGWH.pathEvalZero.app B') ≫
        pullback.fst (CGWH.pathEvalOne.app B') b' =
      (strictFiberToPathLoopRight p b e over H ≫
          zeroMappingPathFiberMapRight d base) ≫
        pullback.snd b'
          (pullback.fst (CGWH.pathEvalOne.app B') b' ≫
            CGWH.pathEvalZero.app B') ≫
        pullback.fst (CGWH.pathEvalOne.app B') b' := by
  have projectedPath_naturality :
      H.projectedPath p ≫ CGWH.path.map d = a ≫ H'.projectedPath p' := by
    unfold CGWH.BasedContraction.projectedPath
    rw [Category.assoc, ← CGWH.path.map_comp, ← square,
      CGWH.path.map_comp, ← Category.assoc, contraction, Category.assoc]
  simp only [Category.assoc]
  unfold strictFiberToPathLoopRight
  rw [← Category.assoc
      (pullback.lift (CGWH.strictFiberToPoint p' b')
        (strictFiberEndingPath p' b' e' over' H') _)
      (pullback.snd b'
        (pullback.fst (CGWH.pathEvalOne.app B') b' ≫
          CGWH.pathEvalZero.app B'))
      (pullback.fst (CGWH.pathEvalOne.app B') b'),
    pullback.lift_snd, strictFiberEndingPath_toPath]
  rw [← Category.assoc (zeroMappingPathFiberMapRight d base)
      (pullback.snd b'
        (pullback.fst (CGWH.pathEvalOne.app B') b' ≫
          CGWH.pathEvalZero.app B'))
      (pullback.fst (CGWH.pathEvalOne.app B') b'),
    zeroMappingPathFiberMapRight_path]
  rw [← Category.assoc
      (pullback.lift (CGWH.strictFiberToPoint p b)
        (strictFiberEndingPath p b e over H) _)
      (pullback.snd b
        (pullback.fst (CGWH.pathEvalOne.app B) b ≫
          CGWH.pathEvalZero.app B) ≫
        pullback.fst (CGWH.pathEvalOne.app B) b)
      (CGWH.path.map d)]
  rw [← Category.assoc
      (pullback.lift (CGWH.strictFiberToPoint p b)
        (strictFiberEndingPath p b e over H) _)
      (pullback.snd b
        (pullback.fst (CGWH.pathEvalOne.app B) b ≫
          CGWH.pathEvalZero.app B))
      (pullback.fst (CGWH.pathEvalOne.app B) b),
    pullback.lift_snd, strictFiberEndingPath_toPath]
  rw [← Category.assoc (CGWH.strictFiberMap a d square base)
      (CGWH.strictFiberToTotal p' b') (H'.projectedPath p'),
    CGWH.strictFiberMap_toTotal]
  simp only [Category.assoc]
  rw [projectedPath_naturality]

/-- F0 is natural for a nonidentity square preserving the basepoint, lifted
point and explicit contraction. -/
theorem strictFiberToPathLoop_naturality
    {E B E' B' : CGWH.{u, v}}
    {p : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {e : CGWH.point.{u, v} ⟶ E} (over : e ≫ p = b)
    (H : CGWH.BasedContraction E e)
    {p' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    {e' : CGWH.point.{u, v} ⟶ E'} (over' : e' ≫ p' = b')
    (H' : CGWH.BasedContraction E' e')
    (a : E ⟶ E') (d : B ⟶ B')
    (square : a ≫ p' = p ≫ d) (base : b ≫ d = b')
    (point : e ≫ a = e')
    (contraction : H.path ≫ CGWH.path.map a = a ≫ H'.path) :
    strictFiberPointedMap over over' a d square base point ≫
        strictFiberToPathLoop p' b' e' over' H' =
      strictFiberToPathLoop p b e over H ≫
        zeroMappingPathFiber.map
          (Under.homMk d base :
            (Under.mk b : PointedCGWH.{u, v}) ⟶ Under.mk b') := by
  apply Under.UnderMorphism.ext
  change CGWH.strictFiberMap a d square base ≫
      strictFiberToPathLoopRight p' b' e' over' H' =
    strictFiberToPathLoopRight p b e over H ≫
      zeroMappingPathFiberMapRight d base
  apply pullback.hom_ext
  · exact strictFiberToPathLoopRight_naturality_toTotal
      over H over' H' a d square base
  · apply pullback.hom_ext
    · exact strictFiberToPathLoopRight_naturality_toPath
        over H over' H' a d square base contraction
    · exact CGWH.point_isTerminal.hom_ext _ _

end PointedCGWH
