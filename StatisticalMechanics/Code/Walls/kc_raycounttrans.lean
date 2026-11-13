/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.WindingEarInduction

open Set SimpleGraph Function
open StatMech.Lattice

namespace StatMech.Walls













theorem kc_rayCount_of_perm {a b : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (Vc' : (hypercubicLattice 2).Walk b b) (z : Site 2)
    (hperm : List.Perm Vc.edges Vc'.edges) :
    jec_rayCount z Vc = jec_rayCount z Vc' := by
  classical
  rw [jec_rayCount, jec_rayCount]
  exact List.Perm.countP_eq _ hperm


















theorem kc_dartFace_trans (w : Site 2) (e : Dart) :
    dartFace (transDart w e) = dartFace e + w := by
  unfold dartFace
  rw [transDart_tail, transDart_dir]
  funext i
  fin_cases i
  · change e.tail 0 + w 0 + Lattice.negPart (e.dir 0) + Lattice.negPart (rot90Fun e.dir 0)
      = (e.tail 0 + Lattice.negPart (e.dir 0) + Lattice.negPart (rot90Fun e.dir 0)) + w 0
    ring
  · change e.tail 1 + w 1 + Lattice.negPart (e.dir 1) + Lattice.negPart (rot90Fun e.dir 1)
      = (e.tail 1 + Lattice.negPart (e.dir 1) + Lattice.negPart (rot90Fun e.dir 1)) + w 1
    ring




theorem kc_rayEdge_trans (w z x y : Site 2) :
    jec_rayEdge (z + w) s(x + w, y + w) ↔ jec_rayEdge z s(x, y) := by
  rw [jec_rayEdge_mk, jec_rayEdge_mk]; simp only [Pi.add_apply]; omega












theorem kc_rayCount_trans (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2) :
    jec_rayCount (z + w) (mpl_orbitLoop (transSet w K) (transSub K w a))
      = jec_rayCount z (mpl_orbitLoop K a) := by
  classical
  rw [jec_rayCount, jec_rayCount, wei_mpl_orbitLoop_edges_eq, wei_mpl_orbitLoop_edges_eq]
  rw [transSub_val, dartOrbitPeriod_trans]
  
  have hmap : (List.range (dartOrbitPeriod K a)).map
        (fun k => s(dartFace ((dartNext (transSet w K))^[k] (transDart w a.1)),
          dartFace ((dartNext (transSet w K))^[k + 1] (transDart w a.1))))
      = (List.range (dartOrbitPeriod K a)).map
        (fun k => s(dartFace ((dartNext K)^[k] a.1) + w,
          dartFace ((dartNext K)^[k + 1] a.1) + w)) := by
    apply List.map_congr_left
    intro k _
    rw [iterate_dartNext_trans, iterate_dartNext_trans, kc_dartFace_trans, kc_dartFace_trans]
  rw [hmap, List.countP_map, List.countP_map]
  apply List.countP_congr
  intro k _
  simp only [Function.comp_apply, decide_eq_true_eq]
  exact kc_rayEdge_trans w z _ _










theorem kc_rayCount_trans_and_perm :
    (∀ (K : Set (Site 2)) (w : Site 2) (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2),
        jec_rayCount (z + w) (mpl_orbitLoop (transSet w K) (transSub K w a))
          = jec_rayCount z (mpl_orbitLoop K a))
    ∧ (∀ {a b : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
        (Vc' : (hypercubicLattice 2).Walk b b) (z : Site 2),
        List.Perm Vc.edges Vc'.edges → jec_rayCount z Vc = jec_rayCount z Vc') :=
  ⟨kc_rayCount_trans, fun Vc Vc' z h => kc_rayCount_of_perm Vc Vc' z h⟩





theorem kc_rayCount_trans' (K : Set (Site 2)) (w : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2) :
    jec_rayCount z (mpl_orbitLoop K a)
      = jec_rayCount (z + w) (mpl_orbitLoop (transSet w K) (transSub K w a)) :=
  (kc_rayCount_trans K w a z).symm

end StatMech.Walls
