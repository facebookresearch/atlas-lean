/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.Clusters
import Code.Lattice.JordanEnclosure
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.ContourLinksExits
import Code.Lattice.TurningNumber
import Code.Lattice.CornerBalance
import Code.Lattice.OrbitEncloses
import Code.Lattice.OrbitLoopBridge
import Code.Lattice.JordanSingleCycle

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

















noncomputable def mpl_orbitFaceLoop (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (faceBoundaryGraph K).Walk (dartFace a.1) (dartFace a.1) :=
  (dartOrbitFaceWalk K a.1 a.2 (dartOrbitPeriod K a)).copy rfl
    (by rw [orbit_iterate_period_eq K a])


theorem mpl_orbitFaceLoop_length (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitFaceLoop K a).length = dartOrbitPeriod K a := by
  rw [mpl_orbitFaceLoop, SimpleGraph.Walk.length_copy, dartOrbitFaceWalk_length]


theorem mpl_orbitFaceLoop_length_pos (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 0 < (mpl_orbitFaceLoop K a).length := by
  rw [mpl_orbitFaceLoop_length]; exact dartOrbitPeriod_pos K hK a




theorem mpl_orbitFaceLoop_edges_bdEdge (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {f g : Site 2}
    (h : s(f, g) ∈ (mpl_orbitFaceLoop K a).edges) :
    bdEdge K (sharedPrimalEdge f g) := by
  rw [mpl_orbitFaceLoop, SimpleGraph.Walk.edges_copy] at h
  exact dartOrbitFaceWalk_edges_bdEdge K a.1 a.2 _ h











noncomputable def mpl_orbitLoop (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (hypercubicLattice 2).Walk (dartFace a.1) (dartFace a.1) :=
  (mpl_orbitFaceLoop K a).mapLe (faceBoundaryGraph_le K)


theorem mpl_orbitLoop_support (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).support = (mpl_orbitFaceLoop K a).support := by
  unfold mpl_orbitLoop
  exact SimpleGraph.Walk.support_mapLe_eq_support _ _


theorem mpl_orbitLoop_edges (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).edges = (mpl_orbitFaceLoop K a).edges := by
  unfold mpl_orbitLoop
  exact SimpleGraph.Walk.edges_mapLe_eq_edges _ _


theorem mpl_orbitLoop_length (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).length = dartOrbitPeriod K a := by
  rw [mpl_orbitLoop]
  have h1 : ((mpl_orbitFaceLoop K a).mapLe (faceBoundaryGraph_le K)).length
      = (mpl_orbitFaceLoop K a).length :=
    SimpleGraph.Walk.length_map (p := mpl_orbitFaceLoop K a)
      (f := Hom.ofLE (faceBoundaryGraph_le K))
  rw [h1]; exact mpl_orbitFaceLoop_length K a


theorem mpl_orbitLoop_length_pos (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 0 < (mpl_orbitLoop K a).length := by
  rw [mpl_orbitLoop_length]; exact dartOrbitPeriod_pos K hK a


theorem mpl_orbitLoop_edges_bdEdge (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    {f g : Site 2} (h : s(f, g) ∈ (mpl_orbitLoop K a).edges) :
    bdEdge K (sharedPrimalEdge f g) := by
  rw [mpl_orbitLoop_edges] at h
  exact mpl_orbitFaceLoop_edges_bdEdge K a h














theorem mpl_orbitFaceLoop_isCycle (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    (mpl_orbitFaceLoop K a).IsCycle :=
  orbitFaceWalk_isCycle K a.1 a.2 (dartOrbitPeriod K a) hp (orbit_iterate_period_eq K a) hinj







theorem mpl_orbitLoop_isCycle (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1))
      (Set.Iio (dartOrbitPeriod K a))) :
    (mpl_orbitLoop K a).IsCycle :=
  (mpl_orbitFaceLoop_isCycle K a hp hinj).mapLe (faceBoundaryGraph_le K)

















theorem mpl_dartFace_ucDart0 : dartFace ucDart0 = ![0, 0] := by
  rw [dartFace_of_dir_right _ ucDart0_dir, ucDart0_tail]; funext i; fin_cases i <;> simp


theorem mpl_dartFace_ucDart1 : dartFace ucDart1 = ![0, -1] := by
  rw [dartFace_of_dir_down _ ucDart1_dir, ucDart1_tail]; funext i; fin_cases i <;> simp


theorem mpl_dartFace_ucDart2 : dartFace ucDart2 = ![-1, -1] := by
  rw [dartFace_of_dir_left _ ucDart2_dir, ucDart2_tail]; funext i; fin_cases i <;> simp


theorem mpl_dartFace_ucDart3 : dartFace ucDart3 = ![-1, 0] := by
  rw [dartFace_of_dir_up _ ucDart3_dir, ucDart3_tail]; funext i; fin_cases i <;> simp


theorem mpl_dartFace_iterate_ucDart0 :
    dartFace ((dartNext unitCell)^[0] ucDart0) = (![0, 0] : Site 2) := mpl_dartFace_ucDart0
theorem mpl_dartFace_iterate_ucDart1 :
    dartFace ((dartNext unitCell)^[1] ucDart0) = (![0, -1] : Site 2) := by
  rw [iterate_ucDart_1]; exact mpl_dartFace_ucDart1
theorem mpl_dartFace_iterate_ucDart2 :
    dartFace ((dartNext unitCell)^[2] ucDart0) = (![-1, -1] : Site 2) := by
  rw [iterate_ucDart_2]; exact mpl_dartFace_ucDart2
theorem mpl_dartFace_iterate_ucDart3 :
    dartFace ((dartNext unitCell)^[3] ucDart0) = (![-1, 0] : Site 2) := by
  rw [iterate_ucDart_3]; exact mpl_dartFace_ucDart3
theorem mpl_dartFace_iterate_ucDart4 :
    dartFace ((dartNext unitCell)^[4] ucDart0) = (![0, 0] : Site 2) := by
  rw [iterate_ucDart_4]; exact mpl_dartFace_ucDart0







theorem mpl_unitCell_faceLoop_edges :
    (mpl_orbitFaceLoop unitCell ucBase).edges
      = [s((![0, 0] : Site 2), ![0, -1]), s((![0, -1] : Site 2), ![-1, -1]),
          s((![-1, -1] : Site 2), ![-1, 0]), s((![-1, 0] : Site 2), ![0, 0])] := by
  rw [mpl_orbitFaceLoop, SimpleGraph.Walk.edges_copy]
  have hbase : ucBase.1 = ucDart0 := rfl
  rw [orbitFaceWalk_edges, unitCell_orbitPeriod_eq_four]
  change (List.range 4).map (fun k => s(dartFace ((dartNext unitCell)^[k] ucBase.1),
      dartFace ((dartNext unitCell)^[k + 1] ucBase.1))) = _
  rw [hbase]
  change [s(dartFace ((dartNext unitCell)^[0] ucDart0),
            dartFace ((dartNext unitCell)^[0 + 1] ucDart0)),
      s(dartFace ((dartNext unitCell)^[1] ucDart0), dartFace ((dartNext unitCell)^[1 + 1] ucDart0)),
      s(dartFace ((dartNext unitCell)^[2] ucDart0), dartFace ((dartNext unitCell)^[2 + 1] ucDart0)),
      s(dartFace ((dartNext unitCell)^[3] ucDart0), dartFace ((dartNext unitCell)^[3 + 1] ucDart0))]
      = _
  rw [mpl_dartFace_iterate_ucDart0, mpl_dartFace_iterate_ucDart1, mpl_dartFace_iterate_ucDart2,
    mpl_dartFace_iterate_ucDart3, mpl_dartFace_iterate_ucDart4]






theorem mpl_unitCell_rayCount_eq_one :
    jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase) = 1 := by
  classical
  rw [jec_rayCount, mpl_orbitLoop_edges, mpl_unitCell_faceLoop_edges]
  simp only [List.countP_cons, List.countP_nil]
  have h1 : decide (jec_rayEdge (![0, 0] : Site 2) s((![0, 0] : Site 2), ![0, -1])) = false := by
    simp only [decide_eq_false_iff_not, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have h2 : decide (jec_rayEdge (![0, 0] : Site 2) s((![0, -1] : Site 2), ![-1, -1])) = false := by
    simp only [decide_eq_false_iff_not, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have h3 : decide (jec_rayEdge (![0, 0] : Site 2) s((![-1, -1] : Site 2), ![-1, 0])) = true := by
    simp only [decide_eq_true_eq, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have h4 : decide (jec_rayEdge (![0, 0] : Site 2) s((![-1, 0] : Site 2), ![0, 0])) = false := by
    simp only [decide_eq_false_iff_not, jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  rw [h1, h2, h3, h4]
  decide











theorem mpl_unitCell_tailOdd :
    ∃ i : ℕ, ¬ Even (jec_rayCount ((dartNext unitCell)^[i] ucBase.1).tail
      (mpl_orbitLoop unitCell ucBase)) := by
  refine ⟨0, ?_⟩
  have htail : ((dartNext unitCell)^[0] ucBase.1).tail = (![0, 0] : Site 2) := by
    change ucDart0.tail = (![0, 0] : Site 2)
    exact ucDart0_tail
  rw [htail, mpl_unitCell_rayCount_eq_one]
  decide










































end Lattice

end StatMech
