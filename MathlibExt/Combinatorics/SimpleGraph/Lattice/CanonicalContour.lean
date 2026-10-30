/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import MathlibExt.Probability.Configuration.ConfigSpace
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanZ2
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanEnclosure
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarTopology
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CrossingParity
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ContourAnchor
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.DartDef
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.DartNext
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.DartInjective
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.DartOrbit
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ContourLinksExits
public import MathlibExt.Probability.Percolation.PcUpperEnclosure

/-!
# The canonical contour of a finite cluster

For a finite open cluster of the origin, the canonical contour is the boundary orbit of the exit
dart on the positive axis. Its darts are distinct, and their primal edges are closed; under the
Bernoulli bond measure the event that all these edges are closed has probability `(1 - p)^ℓ`, where
`ℓ` is the orbit period. The faces to the left of the darts form a closed walk in the face-boundary
graph based at the upper exit face.

## Main definitions

* `StatMech.Lattice.dartPrimalEdge e`: the undirected edge of a dart.
* `StatMech.Lattice.canonicalContour hfin`: the orbit walk of the exit dart.
* `StatMech.Lattice.canonicalContourDarts hfin`: the darts of one period of this orbit.
* `StatMech.Lattice.closedDartContourEvent hfin`: the event that all edges of the canonical contour
  are closed.
* `StatMech.Lattice.CanonicalContourWinds ω hfin`: the orbit period exceeds the exit index.
* `StatMech.Lattice.canonicalFaceWalk hfin`: the closed walk of faces along the canonical contour.

## Main results

* `StatMech.Lattice.canonicalContourDarts_nodup`: the darts of the canonical contour are distinct.
* `StatMech.Lattice.measure_closedDartContourEvent_period`: the closed-contour event has probability
  `(1 - p)` to the power of the orbit period.
* `StatMech.Lattice.pc_lt_one_via_canonicalContour`: `p_c(ℤ²) < 1`, assuming `AnchoredCycleExists`
  for every finite origin cluster.
-/

@[expose] public section

open Finset Set SimpleGraph Function MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin percolationEvent mem_percolationEvent)

variable {ω : ConfigSpace (Sym2 (Site 2))}

/-- The undirected lattice edge underlying a dart. -/
def dartPrimalEdge (e : Dart) : Sym2 (Site 2) := s(e.tail, e.head)

@[simp] theorem dartPrimalEdge_eq (e : Dart) : dartPrimalEdge e = s(e.tail, e.head) := rfl

theorem boundaryDart_primalEdge_isClosed (o : Site 2) {e : Dart}
    (he : IsBoundaryDart (cluster 2 ω o) e) :
    ω (dartPrimalEdge e) = false := by
  have hbd : (e.tail, e.head) ∈ edgeBoundary 2 (cluster 2 ω o) := by
    rw [mem_edgeBoundary]
    exact ⟨e.adj, iff_of_true he.1 he.2⟩
  exact cluster_edgeBoundary_isClosed o hbd

/-- The canonical contour of a finite origin cluster: the closed walk around the boundary orbit
of the exit dart on the positive axis. -/
noncomputable def canonicalContour (hfin : (cluster 2 ω (origin 2)).Finite) :
    (dartSuccGraph (cluster 2 ω (origin 2))).Walk
      ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩
      ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ :=
  dartOrbitWalk (cluster 2 ω (origin 2))
    ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩

theorem canonicalContour_length_eq (hfin : (cluster 2 ω (origin 2)).Finite) :
    (canonicalContour (ω := ω) hfin).length
      = dartOrbitPeriod (cluster 2 ω (origin 2))
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ :=
  dartOrbitWalk_length _ _

theorem canonicalContour_length_pos (hfin : (cluster 2 ω (origin 2)).Finite) :
    0 < (canonicalContour (ω := ω) hfin).length :=
  dartOrbitWalk_length_pos _ hfin _

theorem exitDart_tail_on_posAxis (hfin : (cluster 2 ω (origin 2)).Finite) :
    (exitDart (ω := ω) hfin).tail = ![(exitIndex (ω := ω) hfin : ℤ), 0] := by
  rw [exitDart_tail]; rfl

theorem orbitDart_isBoundaryDart (hfin : (cluster 2 ω (origin 2)).Finite) (n : ℕ) :
    IsBoundaryDart (cluster 2 ω (origin 2))
      ((dartNext (cluster 2 ω (origin 2)))^[n] (exitDart (ω := ω) hfin)) :=
  iterate_isBoundaryDart (cluster 2 ω (origin 2)) (exitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin) n

theorem orbitDart_primalEdge_isClosed (hfin : (cluster 2 ω (origin 2)).Finite) (n : ℕ) :
    ω (dartPrimalEdge ((dartNext (cluster 2 ω (origin 2)))^[n] (exitDart (ω := ω) hfin)))
      = false :=
  boundaryDart_primalEdge_isClosed (origin 2) (orbitDart_isBoundaryDart (ω := ω) hfin n)

/-- The darts of one period of the boundary orbit of the exit dart. -/
noncomputable def canonicalContourDarts (hfin : (cluster 2 ω (origin 2)).Finite) : List Dart :=
  (List.range (dartOrbitPeriod (cluster 2 ω (origin 2))
      ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩)).map
    (fun k => (dartNext (cluster 2 ω (origin 2)))^[k + 1] (exitDart (ω := ω) hfin))

theorem mem_canonicalContourDarts_iff (hfin : (cluster 2 ω (origin 2)).Finite) (D : Dart) :
    D ∈ canonicalContourDarts (ω := ω) hfin ↔
      ∃ k < dartOrbitPeriod (cluster 2 ω (origin 2))
            ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩,
        (dartNext (cluster 2 ω (origin 2)))^[k + 1] (exitDart (ω := ω) hfin) = D := by
  unfold canonicalContourDarts
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, List.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩; exact ⟨k, List.mem_range.mpr hk, rfl⟩

/-- The primal edges of the canonical contour. -/
noncomputable def canonicalPrimalEdgeFinset (hfin : (cluster 2 ω (origin 2)).Finite) :
    Finset (Sym2 (Site 2)) :=
  ((canonicalContourDarts (ω := ω) hfin).map dartPrimalEdge).toFinset

/-- The set of configurations in which every primal edge of the canonical contour of `ω` is
closed. -/
def closedDartContourEvent (hfin : (cluster 2 ω (origin 2)).Finite) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {η | ∀ D ∈ canonicalContourDarts (ω := ω) hfin, η (dartPrimalEdge D) = false}

theorem mem_closedDartContourEvent_canonical (hfin : (cluster 2 ω (origin 2)).Finite) :
    ω ∈ closedDartContourEvent (ω := ω) hfin := by
  intro D hD
  rw [mem_canonicalContourDarts_iff] at hD
  obtain ⟨k, _, rfl⟩ := hD
  exact orbitDart_primalEdge_isClosed (ω := ω) hfin (k + 1)

theorem closedDartContourEvent_eq_pi (hfin : (cluster 2 ω (origin 2)).Finite) :
    closedDartContourEvent (ω := ω) hfin
      = ((canonicalPrimalEdgeFinset (ω := ω) hfin : Finset (Sym2 (Site 2)))
            : Set (Sym2 (Site 2))).pi (fun _ => ({false} : Set Bool)) := by
  ext η
  simp only [closedDartContourEvent, canonicalPrimalEdgeFinset, Set.mem_ofPred_eq, Set.mem_pi,
    List.coe_toFinset, List.mem_map, Set.mem_singleton_iff, forall_exists_index, and_imp]
  constructor
  · rintro h e D hD rfl; exact h D hD
  · intro h D hD; exact h _ D hD rfl

theorem measure_closedDartContourEvent (p : ℝ≥0) (hp : p ≤ 1)
    (hfin : (cluster 2 ω (origin 2)).Finite) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedDartContourEvent (ω := ω) hfin)
      = ((1 - p : ℝ≥0) : ℝ≥0∞) ^ (canonicalPrimalEdgeFinset (ω := ω) hfin).card := by
  rw [closedDartContourEvent_eq_pi, StatMech.Percolation.cylinder_all_closed]

theorem dartPrimalEdge_injOn_boundaryDarts (K : Set (Site 2)) {e f : Dart}
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f)
    (h : dartPrimalEdge e = dartPrimalEdge f) : e = f := by
  rw [dartPrimalEdge_eq, dartPrimalEdge_eq, Sym2.eq_iff] at h
  rcases h with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · exact Dart.ext ht hh
  · exact absurd he.1 (by rw [ht]; exact hf.2)

theorem canonicalContourDarts_nodup (hfin : (cluster 2 ω (origin 2)).Finite) :
    (canonicalContourDarts (ω := ω) hfin).Nodup := by
  unfold canonicalContourDarts
  apply List.Nodup.map_on (l := List.range _)
  · intro j hj k hk h
    simp only [List.mem_range] at hj hk
    have hpe : dartOrbitPeriod (cluster 2 ω (origin 2))
        ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩
        = Function.minimalPeriod (dartNextSub (cluster 2 ω (origin 2)))
            ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ := rfl
    have hpos : 0 < Function.minimalPeriod (dartNextSub (cluster 2 ω (origin 2)))
        ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ :=
      dartOrbitPeriod_pos (cluster 2 ω (origin 2)) hfin _
    have hsub : (dartNextSub (cluster 2 ω (origin 2)))^[j + 1]
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩
        = (dartNextSub (cluster 2 ω (origin 2)))^[k + 1]
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ := by
      apply Subtype.ext
      rw [dartNextSub_iterate_val, dartNextSub_iterate_val]; exact h
    have := iterate_inj_on_Icc_minimalPeriod (dartNextSub (cluster 2 ω (origin 2)))
      ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩
      (j := j + 1) (k := k + 1) hpos
      (by omega) (by omega) (by omega) (by omega) hsub
    omega
  · exact List.nodup_range

theorem canonicalPrimalEdge_list_nodup (hfin : (cluster 2 ω (origin 2)).Finite) :
    ((canonicalContourDarts (ω := ω) hfin).map dartPrimalEdge).Nodup := by
  apply List.Nodup.map_on _ (canonicalContourDarts_nodup (ω := ω) hfin)
  intro D1 hD1 D2 hD2 heq
  rw [mem_canonicalContourDarts_iff] at hD1 hD2
  obtain ⟨k1, _, rfl⟩ := hD1
  obtain ⟨k2, _, rfl⟩ := hD2
  exact dartPrimalEdge_injOn_boundaryDarts (cluster 2 ω (origin 2))
    (orbitDart_isBoundaryDart (ω := ω) hfin (k1 + 1))
    (orbitDart_isBoundaryDart (ω := ω) hfin (k2 + 1)) heq

theorem canonicalPrimalEdgeFinset_card (hfin : (cluster 2 ω (origin 2)).Finite) :
    (canonicalPrimalEdgeFinset (ω := ω) hfin).card
      = dartOrbitPeriod (cluster 2 ω (origin 2))
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ := by
  unfold canonicalPrimalEdgeFinset
  rw [List.toFinset_card_of_nodup (canonicalPrimalEdge_list_nodup (ω := ω) hfin),
    List.length_map]
  unfold canonicalContourDarts
  rw [List.length_map, List.length_range]

theorem measure_closedDartContourEvent_period (p : ℝ≥0) (hp : p ≤ 1)
    (hfin : (cluster 2 ω (origin 2)).Finite) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) (closedDartContourEvent (ω := ω) hfin)
      = ((1 - p : ℝ≥0) : ℝ≥0∞) ^ (dartOrbitPeriod (cluster 2 ω (origin 2))
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩) := by
  rw [measure_closedDartContourEvent p hp hfin, canonicalPrimalEdgeFinset_card]

/-- The period of the canonical contour exceeds the exit index, the length condition of an
anchored enclosure. -/
def CanonicalContourWinds (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  exitIndex (ω := ω) hfin
    < dartOrbitPeriod (cluster 2 ω (origin 2))
        ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩

/-- The walk of faces to the left of the first `n` successors of a boundary dart. -/
noncomputable def canonicalFaceWalkAux (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) :
    (n : ℕ) → (faceBoundaryGraph K).Walk (dartFace e) (dartFace ((dartNext K)^[n] e))
  | 0 => SimpleGraph.Walk.nil
  | (n + 1) =>
      (canonicalFaceWalkAux K e he n).concat (by
        rw [Function.iterate_succ_apply']
        exact dartFace_step_adj K _ (iterate_isBoundaryDart K e he n))

theorem canonicalFaceWalkAux_length (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    (n : ℕ) : (canonicalFaceWalkAux K e he n).length = n := by
  induction n with
  | zero => rfl
  | succ m ih => simp only [canonicalFaceWalkAux, SimpleGraph.Walk.length_concat, ih]

/-- The closed walk of faces to the left of the darts of the canonical contour, based at the
upper exit face. -/
noncomputable def canonicalFaceWalk (hfin : (cluster 2 ω (origin 2)).Finite) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk
      (exitFaceUp (ω := ω) hfin) (exitFaceUp (ω := ω) hfin) := by
  refine (canonicalFaceWalkAux (cluster 2 ω (origin 2)) (exitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin)
    (dartOrbitPeriod (cluster 2 ω (origin 2))
      ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩)).copy
    (dartFace_exitDart (ω := ω) hfin) ?_
  have hret : (dartNext (cluster 2 ω (origin 2)))^[dartOrbitPeriod (cluster 2 ω (origin 2))
        ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩]
        (exitDart (ω := ω) hfin) = exitDart (ω := ω) hfin := by
    have := dartOrbitPeriod_iterate (cluster 2 ω (origin 2))
      ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩
    have h2 := congrArg Subtype.val this
    rwa [dartNextSub_iterate_val] at h2
  rw [hret, dartFace_exitDart (ω := ω) hfin]

theorem canonicalFaceWalk_length (hfin : (cluster 2 ω (origin 2)).Finite) :
    (canonicalFaceWalk (ω := ω) hfin).length
      = dartOrbitPeriod (cluster 2 ω (origin 2))
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ := by
  unfold canonicalFaceWalk
  rw [SimpleGraph.Walk.length_copy, canonicalFaceWalkAux_length]

theorem canonicalFaceWalk_basepoint_mem_anchorFinset (hfin : (cluster 2 ω (origin 2)).Finite)
    (hwind : CanonicalContourWinds ω hfin) :
    exitFaceUp (ω := ω) hfin ∈ StatMech.Percolation.anchorFinset
      (canonicalFaceWalk (ω := ω) hfin).length := by
  rw [canonicalFaceWalk_length]
  exact exitFaceUp_mem_anchorFinset (ω := ω) hfin hwind

/-- `p_c(ℤ²) < 1`, under the hypothesis that `AnchoredCycleExists` holds for every configuration
with a finite origin cluster. The hypothesis is not proved here. -/
theorem pc_lt_one_via_canonicalContour
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        AnchoredCycleExists ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  StatMech.Percolation.pc_lt_one_of_enclosure (pcAnchoredEnclosure_of_anchoredCycle hres)

end Lattice

end StatMech
