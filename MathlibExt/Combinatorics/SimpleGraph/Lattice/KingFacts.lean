/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnectedSingleton

/-!
# King moves along boundary orbits

A king move joins two distinct sites of `ℤ²` that differ by at most one in each coordinate. Lattice
neighbours are king neighbours, so connectivity in `Kᶜ` implies king connectivity in `Kᶜ`; this is
the condition `BoundaryKingConnected K`, which therefore holds for every `K`. Along a boundary orbit
of `K`, the head of the successor of a dart is either the same site or a king neighbour of the head.

## Main results

* `StatMech.Lattice.kf_hyperAdj_kingAdj`: lattice neighbours are king neighbours.
* `StatMech.Lattice.kf_boundaryKingConnected`: `BoundaryKingConnected K` holds for every `K`.
* `StatMech.Lattice.kf_dartNext_head_kingAdj_or_eq`: the head of `dartNext K e` equals `e.head` or
  is a king neighbour of it.
* `StatMech.Lattice.kf_interfaceConnected_of_orbitResidues`: `OrbitKingTransport K` and
  `OrbitVertexSaturate K` imply `InterfaceConnected K`. The first hypothesis fails for every finite
  nonempty `K` (see the docstring).
-/

@[expose] public section

open SimpleGraph Function

namespace StatMech

namespace Lattice

/-- Lattice neighbours in `ℤ²` are king neighbours. -/
theorem kf_hyperAdj_kingAdj (x y : Site 2) (h : (hypercubicLattice 2).Adj x y) : KingAdj x y := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h
  refine ⟨fun hxy => by rw [hxy] at h; simp at h, fun i => by fin_cases i <;> simp_all <;> omega⟩

/-- The square lattice restricted to `Kᶜ` is a subgraph of the king-move graph on `Kᶜ`. -/
theorem kf_induce_le_kingGraph (K : Set (Site 2)) :
    (hypercubicLattice 2).induce (Kᶜ : Set (Site 2)) ≤ boundaryKingGraph K := by
  intro a b hab
  rw [boundaryKingGraph_adj]
  exact kf_hyperAdj_kingAdj _ _ hab

/-- The condition `BoundaryKingConnected K` holds for every set `K`: sites joined by a lattice path
in `Kᶜ` are joined by king moves in `Kᶜ`. -/
theorem kf_boundaryKingConnected (K : Set (Site 2)) : BoundaryKingConnected K := by
  intro u w hu hw hreach
  exact hreach.mono (kf_induce_le_kingGraph K)

/-- For a dart `e`, the site `e.tail - r e.dir` beside its tail (with `r` the counterclockwise
quarter turn) is a king neighbour of `e.head`. -/
theorem kf_cornerHead_king (e : Dart) :
    KingAdj e.head (e.tail + (-rot90Fun e.dir)) := by
  have hd : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
  refine ⟨?_, ?_⟩
  · intro hcon
    rw [hd] at hcon
    have : e.dir = -rot90Fun e.dir := add_left_cancel hcon
    exact neg_rot90Fun_dartDir_ne_dartDir e this.symm
  · intro i
    rw [hd]
    have hsimp : ((e.tail + e.dir) i) - ((e.tail + (-rot90Fun e.dir)) i)
        = e.dir i - (-rot90Fun e.dir) i := by
      rw [Pi.add_apply, Pi.add_apply]; ring
    rw [hsimp]
    set g := e.dir with hg
    rcases ifc_unit_four_cases g (hg ▸ unitWt_dir e) with h | h | h | h <;>
      rw [h] <;> (fin_cases i <;> simp [rot90Fun])

/-- The head of the successor `dartNext K e` is either `e.head` itself or a king neighbour of
`e.head`. -/
theorem kf_dartNext_head_kingAdj_or_eq (K : Set (Site 2)) (e : Dart) :
    (dartNext K e).head = e.head ∨ KingAdj e.head (dartNext K e).head := by
  classical
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · left; exact (dartNext_front_head K e hA).1
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · right
      rw [dartNext_straight_head K e hA hB]
      apply kf_hyperAdj_kingAdj
      rw [hypercubicLattice_adj]
      have hco : ∀ i, (e.head i - (e.head + (-rot90Fun e.dir)) i) = -(-rot90Fun e.dir) i := by
        intro i; rw [Pi.add_apply]; ring
      simp_rw [hco]
      rw [Fin.sum_univ_two]
      set g := e.dir with hg
      rcases ifc_unit_four_cases g (hg ▸ unitWt_dir e) with h | h | h | h <;>
        rw [h] <;> simp [rot90Fun]
    · right
      rw [dartNext_left_head K e hA hB]
      exact kf_cornerHead_king e

/-- If `d` is in the orbit of `e`, so is its successor `dartNext K d`. -/
theorem kf_sameOrbit_step (K : Set (Site 2)) {e d : Dart} (h : SameOrbit K e d) :
    SameOrbit K e (dartNext K d) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩

/-- Every site reached by the orbit of `e` has a reached site equal to it or king-adjacent to it,
namely the head of the next dart of the orbit. -/
theorem kf_orbitKingTransport_step (K : Set (Site 2)) (e : Dart)
    {u : Site 2} (ho : OrbitReached K e u) :
    ∃ v : Site 2, (v = u ∨ KingAdj u v) ∧ OrbitReached K e v := by
  obtain ⟨d, hd, hdh, hsame⟩ := ho
  refine ⟨(dartNext K d).head, ?_, ?_⟩
  · rcases kf_dartNext_head_kingAdj_or_eq K d with hfix | hking
    · left; rw [hfix, hdh]
    · right; rw [← hdh]; exact hking
  · exact ⟨dartNext K d, dartNext_isBoundaryDart K d hd, rfl, kf_sameOrbit_step K hsame⟩

/-- `OrbitKingTransport K` and `OrbitVertexSaturate K` imply `InterfaceConnected K`; the third
condition of `interfaceConnected_of_kingResidues` holds by `kf_boundaryKingConnected`. Vacuity
warning: `OrbitKingTransport K` fails for every finite nonempty `K`
(`ifg_not_orbitKingTransport_of_finite`): if `c ∈ K` has the largest first coordinate, the dart
from `c` to `c + (1,0)` is a boundary dart, and the neighbour `c + (2,0)` of its head has no lattice
neighbour in `K`, so no boundary dart has it as head. So for finite `K` this lemma only covers
`K = ∅`. -/
theorem kf_interfaceConnected_of_orbitResidues (K : Set (Site 2))
    (htr : OrbitKingTransport K) (hsat : OrbitVertexSaturate K) :
    InterfaceConnected K :=
  interfaceConnected_of_kingResidues K htr (kf_boundaryKingConnected K) hsat

end Lattice

end StatMech
