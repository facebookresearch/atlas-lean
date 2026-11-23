/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.KTheory.Ring.SteinbergPlusFiberSequence
import MathlibExt.AlgebraicTopology.SimplicialSet.GroupoidNerveHomotopyGroup
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWUnit

/-!
# Injectivity of the original plus-fiber boundary

The original ordinary BGL has trivial cube-based second homotopy group at
every point. Its one-object group nerve has unique pointed two-simplices;
the realization--singular unit and the original cube comparison transfer
this fact to the ordinary space. Actual path transports cover every point.

The actual mapping-path total space therefore also has trivial second
homotopy group. Exactness at the base of the original Kan sequence then
proves injectivity of the existing cube-π₂-to-fiber-fundamental-group map.

This supplies the injective left map in the low-degree sequence used in
Weibel, *The K-book*, IV.1.7, printed pages 264–265 (official PDF pages
272–273). The original plus inclusion, ending-path fiber, point, and
connecting homomorphism are retained.
-/

noncomputable section

open CategoryTheory Opposite Simplicial
open scoped Simplicial Topology

universe u

namespace AlgebraicKTheory.StableGL

private local instance singularKan (X : TopCat.{u}) :
    SSet.KanComplex (TopCat.toSSet.obj X) := TopCat.toSSet_obj_kanComplex X

/-- The actual ordinary BGL has trivial cube-based second homotopy group at every point. -/
theorem ordinaryBGL_piTwo_subsingleton (R : Type u) [Ring R] (x : ordinaryBGL R) :
    Subsingleton (HomotopyGroup.Pi 2 (ordinaryBGL R) x) := by
  let K := classifyingNerve R
  let a := classifyingVertex R
  let _ : SSet.KanComplex K := SSet.kanComplex_nerve_of_groupoid (ClassifyingCategory R)
  let _ : Subsingleton (SSet.KanComplex.π 2 K a) :=
    SSet.piTwo_nerve_subsingleton (ClassifyingCategory R) a
  let _ : SSet.KanComplex ((Functor.id SSet.{u}).obj K) := by
    change SSet.KanComplex K
    infer_instance
  let _ : Subsingleton (SSet.KanComplex.π 2 ((Functor.id SSet.{u}).obj K) a) := by
    change Subsingleton (SSet.KanComplex.π 2 K a)
    infer_instance
  let _ : SSet.KanComplex ((SSet.toTop.{u} ⋙ TopCat.toSSet.{u}).obj K) := by
    change SSet.KanComplex (TopCat.toSSet.obj (ordinaryBGL R))
    infer_instance
  let U := sSetTopAdj.unit.app K
  let b := U.app (op ⦋0⦌) a
  let E := SSet.KanComplex.W.homotopyGroupIso U (SSet.KanComplex.W.sSetTopAdj_unit_app K) 1 a
  let _ : Subsingleton (SSet.KanComplex.π 2 (TopCat.toSSet.obj (ordinaryBGL R)) b) :=
    E.symm.injective.subsingleton
  let y : ordinaryBGL R := TopCat.toSSetObj₀Equiv b
  have hy : TopCat.toSSetObj₀Equiv.symm y = b := Equiv.symm_apply_apply _ _
  have hSingular : Subsingleton (SSet.KanComplex.π 2
      (TopCat.toSSet.obj (ordinaryBGL R)) (TopCat.toSSetObj₀Equiv.symm y)) := by
    rw [hy]
    infer_instance
  let _ := hSingular
  let _ : Subsingleton (HomotopyGroup.Pi 2 (ordinaryBGL R) y) :=
    (TopCat.homotopyGroupSingularMulEquiv 1 (ordinaryBGL R) y).injective.subsingleton
  let _ : PathConnectedSpace (ordinaryBGL R) := ordinaryBGLPathConnected R
  let T := TopCat.homotopyGroupBasepointChangeMulEquiv 1 (ordinaryBGL R)
    (PathConnectedSpace.somePath y x)
  exact T.symm.injective.subsingleton

/-- The unchanged original plus-fiber connecting homomorphism is injective. -/
theorem independentPlusFiberConnectingHom_injective (R : Type u) [Ring R] :
    Function.Injective (independentPlusFiberConnectingHom R) :=
  TopCat.homotopyFiberConnectingHom_injective (independentBGLCellInclusion R)
    (ordinaryBGLBasepoint R) (independentBGLCellPoint R) (independentBGLCellInclusion_point R)
    (ordinaryBGL_piTwo_subsingleton R (ordinaryBGLBasepoint R))

end AlgebraicKTheory.StableGL

end
