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
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.PlanarTopology
import Code.Lattice.CrossingParity
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.ContourAnchor
import Code.Lattice.EnclosingLength
import Code.Lattice.LeftFace
import Code.Lattice.ContourLinksExits
import Code.Percolation.PcUpperUncond

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}













noncomputable def dartOrbitFaceWalk (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    (n : ℕ) → (faceBoundaryGraph K).Walk (dartFace e) (dartFace ((dartNext K)^[n] e))
  | 0 => SimpleGraph.Walk.nil
  | (n + 1) =>
      ((dartOrbitFaceWalk K e he n).concat
        (dartFace_step_adj K _ (iterate_isBoundaryDart K e he n))).copy rfl (by
          rw [Function.iterate_succ_apply'])


theorem dartOrbitFaceWalk_length (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) : (dartOrbitFaceWalk K e he n).length = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [dartOrbitFaceWalk, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_concat, ih]



theorem dartOrbitFaceWalk_support (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) : (dartOrbitFaceWalk K e he n).support
      = (List.range (n + 1)).map (fun k => dartFace ((dartNext K)^[k] e)) := by
  induction n with
  | zero => simp [dartOrbitFaceWalk]
  | succ m ih =>
    rw [dartOrbitFaceWalk, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_concat, ih,
      List.range_succ (n := m + 1), List.map_append]
    simp [Function.iterate_succ_apply']




theorem dartFace_iterate_mem_dartOrbitFaceWalk_support (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) {n k : ℕ} (hk : k ≤ n) :
    dartFace ((dartNext K)^[k] e) ∈ (dartOrbitFaceWalk K e he n).support := by
  rw [dartOrbitFaceWalk_support]
  rw [List.mem_map]
  exact ⟨k, List.mem_range.mpr (by omega), rfl⟩












theorem dartOrbitFaceWalk_edges_bdEdge (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) {f g : Site 2} (h : s(f, g) ∈ (dartOrbitFaceWalk K e he n).edges) :
    bdEdge K (sharedPrimalEdge f g) := by
  have hadj : (faceBoundaryGraph K).Adj f g := (dartOrbitFaceWalk K e he n).adj_of_mem_edges h
  exact faceBoundaryGraph_sharedPrimalEdge_bdEdge K hadj












noncomputable def dartOrbitFaceLoop (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : (faceBoundaryGraph K).Walk (dartFace e) (dartFace e) :=
  (dartOrbitFaceWalk K e he (dartNext_periodic K hK e he).choose).copy rfl (by
    rw [(dartNext_periodic K hK e he).choose_spec.2])



theorem dartOrbitFaceLoop_length_pos (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : 0 < (dartOrbitFaceLoop K hK e he).length := by
  rw [dartOrbitFaceLoop, SimpleGraph.Walk.length_copy, dartOrbitFaceWalk_length]
  exact (dartNext_periodic K hK e he).choose_spec.1




theorem dartOrbitFaceLoop_edges_bdEdge (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {f g : Site 2} (h : s(f, g) ∈ (dartOrbitFaceLoop K hK e he).edges) :
    bdEdge K (sharedPrimalEdge f g) := by
  rw [dartOrbitFaceLoop, SimpleGraph.Walk.edges_copy] at h
  exact dartOrbitFaceWalk_edges_bdEdge K e he _ h












noncomputable def exitOrbitFaceLoop (hfin : (cluster 2 ω (origin 2)).Finite) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
      (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin) :=
  (dartOrbitFaceLoop (cluster 2 ω (origin 2)) hfin (exitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin)).copy
      (dartFace_exitDart (ω := ω) hfin) (dartFace_exitDart (ω := ω) hfin)


theorem exitOrbitFaceLoop_length_pos (hfin : (cluster 2 ω (origin 2)).Finite) :
    0 < (exitOrbitFaceLoop (ω := ω) hfin).length := by
  rw [exitOrbitFaceLoop, SimpleGraph.Walk.length_copy]
  exact dartOrbitFaceLoop_length_pos _ _ _ _














theorem orbitEdges_subset_bdBarrier (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    ∀ ⦃f g : Site 2⦄, s(f, g) ∈ (dartOrbitFaceLoop K hK e he).edges →
      bdEdge K (sharedPrimalEdge f g) :=
  fun _ _ h => dartOrbitFaceLoop_edges_bdEdge K hK e he h


















theorem orbit_separates_origin (_hfin : (cluster 2 ω (origin 2)).Finite) {z : Site 2}
    (hz : z ∉ cluster 2 ω (origin 2)) :
    ¬ (latticeMinusBarrier (cluster 2 ω (origin 2))).Reachable (origin 2) z :=
  cluster_separated_from_exterior (origin 2) hz







theorem orbit_origin_crossCount_odd (_hfin : (cluster 2 ω (origin 2)).Finite) {z : Site 2}
    (hz : z ∉ cluster 2 ω (origin 2)) (w : (hypercubicLattice 2).Walk (origin 2) z) :
    ¬ Even (crossCount (cluster 2 ω (origin 2)) w) :=
  origin_crossCount_odd (origin 2) hz w










theorem iterate_eq_mod_of_period {α : Type*} (f : α → α) (x : α) {p : ℕ}
    (hp : f^[p] x = x) (n : ℕ) : f^[n] x = f^[n % p] x := by
  have hper : Function.IsPeriodicPt f p x := hp
  conv_lhs => rw [← Nat.mod_add_div n p, Function.iterate_add_apply]
  rw [(hper.mul_const (n / p)).eq]





theorem dartFace_iterate_mem_dartOrbitFaceLoop_support (K : Set (Site 2)) (hK : K.Finite)
    (e : Dart) (he : IsBoundaryDart K e) (n : ℕ) :
    dartFace ((dartNext K)^[n] e) ∈ (dartOrbitFaceLoop K hK e he).support := by
  classical
  set p := (dartNext_periodic K hK e he).choose with hp
  have hpspec := (dartNext_periodic K hK e he).choose_spec
  have hpper : (dartNext K)^[p] e = e := hpspec.2
  have hppos : 0 < p := hpspec.1
  
  have heq : (dartNext K)^[n] e = (dartNext K)^[n % p] e :=
    iterate_eq_mod_of_period (dartNext K) e hpper n
  have hlt : n % p ≤ p := le_of_lt (Nat.mod_lt _ hppos)
  rw [heq]
  
  rw [dartOrbitFaceLoop, SimpleGraph.Walk.support_copy]
  exact dartFace_iterate_mem_dartOrbitFaceWalk_support K e he hlt


















theorem exitOrbitFaceLoop_mem_leftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ExitDartsSameOrbit ω hfin) :
    leftExitFaceDown (ω := ω) hfin ∈ (exitOrbitFaceLoop (ω := ω) hfin).support := by
  classical
  obtain ⟨n, hn⟩ := h
  
  have hface : dartFace ((dartNext (cluster 2 ω (origin 2)))^[n] (exitDart (ω := ω) hfin))
      = leftExitFaceDown (ω := ω) hfin := by
    rw [hn]; exact dartFace_leftExitDart (ω := ω) hfin
  
  have hmem := dartFace_iterate_mem_dartOrbitFaceLoop_support (cluster 2 ω (origin 2)) hfin
    (exitDart (ω := ω) hfin) (exitDart_isBoundaryDart (ω := ω) hfin) n
  rw [hface] at hmem
  
  rw [exitOrbitFaceLoop, SimpleGraph.Walk.support_copy]
  exact hmem




theorem exitOrbitFaceLoop_exists_leftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ExitDartsSameOrbit ω hfin) :
    ∃ w ∈ (exitOrbitFaceLoop (ω := ω) hfin).support, w 0 ≤ 0 :=
  ⟨leftExitFaceDown (ω := ω) hfin, exitOrbitFaceLoop_mem_leftFace (ω := ω) hfin h,
    leftExitFaceDown_coord0_nonpos (ω := ω) hfin⟩





















def CanonicalOrbitCycle (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  (exitOrbitFaceLoop (ω := ω) hfin).IsCycle ∧ ExitDartsSameOrbit ω hfin






theorem cycleHasLeftFace_of_canonicalOrbit (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : CanonicalOrbitCycle ω hfin) : CycleHasLeftFace ω hfin := by
  obtain ⟨hcyc, hsame⟩ := h
  exact ⟨exitOrbitFaceLoop (ω := ω) hfin, hcyc,
    exitOrbitFaceLoop_exists_leftFace (ω := ω) hfin hsame⟩







theorem pcAnchoredEnclosure_of_canonicalOrbit
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        CanonicalOrbitCycle ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure :=
  pcAnchoredEnclosure_of_cycleHasLeftFace
    (fun ω hfin => cycleHasLeftFace_of_canonicalOrbit (ω := ω) hfin (h ω hfin))









theorem pc_lt_one_orbit
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        CanonicalOrbitCycle ω hfin) :
    (StatMech.Percolation.pc 2 : ℝ) < 1 := by
  have := StatMech.Percolation.pc_lt_one_of_enclosure (pcAnchoredEnclosure_of_canonicalOrbit h)
  exact_mod_cast this

end Lattice

end StatMech
