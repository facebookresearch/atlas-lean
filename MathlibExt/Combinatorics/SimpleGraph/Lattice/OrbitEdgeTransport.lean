/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitDartsOrbit
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitKingConnected

/-!
# Transport of boundary orbits along lattice paths

A boundary orbit of `K` moves from one head to the next by a straight step or a turn. This file
records these steps, the reduction of `InterfaceConnected K` to transport of the orbit along lattice
edges of `Kᶜ` (`UnitEdgeOrbitTransport`) plus `OrbitVertexSaturate`, and a proof that
`UnitEdgeOrbitTransport` fails for every finite nonempty set, so that reduction is empty there. It
then applies `InterfaceConnected` to the origin cluster: when the heads of both exit darts lie
outside a box containing the cluster, the exit darts share an orbit and the exit faces are joined
in the face-boundary graph.

## Main definitions

* `StatMech.Lattice.UnitEdgeOrbitTransport K`: if the orbit of a boundary dart reaches a site
  outside `K`, it reaches every lattice neighbour of that site outside `K`.

## Main results

* `StatMech.Lattice.icb_interfaceConnected_of_unitEdgeTransport`: `UnitEdgeOrbitTransport K` and
  `OrbitVertexSaturate K` imply `InterfaceConnected K`.
* `StatMech.Lattice.icb_not_unitEdgeTransport_of_finite`: `UnitEdgeOrbitTransport K` is false for
  every finite nonempty `K`.
* `StatMech.Lattice.icb_exitFaces_reachable_of_traceSurjective`: for the origin cluster, under
  `InterfaceConnected` and with both exit heads outside a box containing the cluster, the two exit
  faces are connected in the face-boundary graph (via `exitDart_sameOrbit_of_far`).
-/

@[expose] public section

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}

/-- Straight step. Let `d` be a boundary dart in the orbit of `e`, and write `r` for the
counterclockwise quarter turn. If `d.head - r d.dir` is outside `K` and `d.tail - r d.dir` is in
`K`, the orbit of `e` reaches `d.head - r d.dir`. -/
theorem icb_orbitReached_straight_step (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (hsame : SameOrbit K e d)
    (hfront : d.head + (-rot90Fun d.dir) ∉ K)
    (hside : d.tail + (-rot90Fun d.dir) ∈ K) :
    OrbitReached K e (d.head + (-rot90Fun d.dir)) := by
  refine ⟨dartNext K d, dartNext_isBoundaryDart K d hd, ?_, ?_⟩
  · exact dartNext_straight_head K d hfront hside
  · obtain ⟨n, hn⟩ := hsame; exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩

/-- Corner step. Let `d` be a boundary dart in the orbit of `e`. If both `d.head - r d.dir` and
`d.tail - r d.dir` are outside `K`, the orbit of `e` reaches `d.tail - r d.dir`. -/
theorem icb_orbitReached_corner_step (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (hsame : SameOrbit K e d)
    (hfront : d.head + (-rot90Fun d.dir) ∉ K)
    (hside : d.tail + (-rot90Fun d.dir) ∉ K) :
    OrbitReached K e (d.tail + (-rot90Fun d.dir)) := by
  refine ⟨dartNext K d, dartNext_isBoundaryDart K d hd, ?_, ?_⟩
  · exact dartNext_left_head K d hfront hside
  · obtain ⟨n, hn⟩ := hsame; exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩

/-- The orbit of `e` reaches the head of the successor of any of its darts, and that head equals the
head of the dart or is a king neighbour of it. -/
theorem icb_orbitReached_wallStep (K : Set (Site 2)) (e d : Dart)
    (hd : IsBoundaryDart K d) (hsame : SameOrbit K e d) :
    OrbitReached K e (dartNext K d).head ∧
      ((dartNext K d).head = d.head ∨ KingAdj d.head (dartNext K d).head) := by
  refine ⟨⟨dartNext K d, dartNext_isBoundaryDart K d hd, rfl, ?_⟩,
    kf_dartNext_head_kingAdj_or_eq K d⟩
  obtain ⟨n, hn⟩ := hsame; exact ⟨n + 1, by rw [Function.iterate_succ_apply', hn]⟩

/-- If the orbit of a boundary dart of `K` reaches a site `u ∉ K`, it reaches every lattice
neighbour `v ∉ K` of `u`. This fails for every finite nonempty `K`
(`icb_not_unitEdgeTransport_of_finite`): a site outside `K` with no neighbour in `K` is never the
head of a boundary dart. -/
def UnitEdgeOrbitTransport (K : Set (Site 2)) : Prop :=
  ∀ (e : Dart), IsBoundaryDart K e →
    ∀ {u v : Site 2} (_hu : u ∉ K) (_hv : v ∉ K),
      (hypercubicLattice 2).Adj u v →
      OrbitReached K e u → OrbitReached K e v

/-- Under `UnitEdgeOrbitTransport K`, the set of sites reached by an orbit is closed under lattice
paths in `Kᶜ`. -/
theorem icb_orbitReached_of_complReachable (K : Set (Site 2)) (htr : UnitEdgeOrbitTransport K)
    (e : Dart) (he : IsBoundaryDart K e) {u w : Site 2} (hu : u ∉ K) (hw : w ∉ K)
    (hreach : ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨u, hu⟩ ⟨w, hw⟩)
    (hou : OrbitReached K e u) : OrbitReached K e w := by
  obtain ⟨p⟩ := hreach
  suffices H : ∀ (a b : ↥(Kᶜ : Set (Site 2))), ((hypercubicLattice 2).induce Kᶜ).Walk a b →
      OrbitReached K e (a : Site 2) → OrbitReached K e (b : Site 2) from
    H ⟨u, hu⟩ ⟨w, hw⟩ p hou
  intro a b q
  induction q with
  | nil => intro h; exact h
  | @cons a b c hadj q' ih =>
    intro hoa
    have hadj' : (hypercubicLattice 2).Adj (a : Site 2) (b : Site 2) := hadj
    exact ih (htr e he a.2 b.2 hadj' hoa)

/-- `UnitEdgeOrbitTransport K` and `OrbitVertexSaturate K` imply `InterfaceConnected K`. Vacuity
warning: the first hypothesis fails for every finite nonempty `K`
(`icb_not_unitEdgeTransport_of_finite`), so for finite `K` this lemma only covers `K = ∅`. -/
theorem icb_interfaceConnected_of_unitEdgeTransport (K : Set (Site 2))
    (htr : UnitEdgeOrbitTransport K) (hsat : OrbitVertexSaturate K) :
    InterfaceConnected K := by
  intro e f he hf hreach
  have hbase : OrbitReached K e e.head := orbitReached_self K e he
  have hfhead : OrbitReached K e f.head :=
    icb_orbitReached_of_complReachable K htr e he he.2 hf.2 hreach hbase
  exact hsat e he hfhead f hf rfl

/-- `UnitEdgeOrbitTransport` fails for the single site `0`: the orbit reaches `(1,0)` but not its
neighbour `(2,0)`. -/
theorem icb_unitEdgeTransport_false :
    ¬ UnitEdgeOrbitTransport ({(0 : Site 2)} : Set (Site 2)) := by
  intro htr
  have hg : unitWt (![1, 0] : Site 2) = 1 := by simp only [unitWt, Fin.sum_univ_two]; decide
  set e : Dart := mkDart (0 : Site 2) (![1, 0] : Site 2) hg with he_def
  have hhead : e.head = (![1, 0] : Site 2) := by rw [he_def, mkDart_head]; simp
  have htail : e.tail = (0 : Site 2) := by rw [he_def, mkDart_tail]
  have hbd : IsBoundaryDart ({(0 : Site 2)} : Set (Site 2)) e := by
    refine ⟨by rw [htail]; exact Set.mem_singleton _, ?_⟩
    rw [hhead]; intro hc; simp only [Set.mem_singleton_iff] at hc
    have := congrFun hc 0; simp at this
  have hou : OrbitReached ({(0 : Site 2)} : Set (Site 2)) e (![1, 0] : Site 2) := by
    have := orbitReached_self ({(0 : Site 2)} : Set (Site 2)) e hbd; rwa [hhead] at this
  have hu : (![1, 0] : Site 2) ∉ ({(0 : Site 2)} : Set (Site 2)) := by
    intro hc; simp only [Set.mem_singleton_iff] at hc; have := congrFun hc 0; simp at this
  have hv : (![2, 0] : Site 2) ∉ ({(0 : Site 2)} : Set (Site 2)) := by
    intro hc; simp only [Set.mem_singleton_iff] at hc; have := congrFun hc 0; simp at this
  have hadj : (hypercubicLattice 2).Adj (![1, 0] : Site 2) (![2, 0] : Site 2) := by
    rw [adj_iff_unitWt_sub]
    change unitWt ((![1, 0] : Site 2) - (![2, 0] : Site 2)) = 1
    simp only [unitWt, Fin.sum_univ_two]; decide
  obtain ⟨d, hd, hdh, _⟩ := htr e hbd hu hv hadj hou
  have htaild : d.tail = (0 : Site 2) := by simpa using hd.1
  have hdir : d.dir = (![2, 0] : Site 2) := by rw [Dart.dir_def, hdh, htaild]; abel
  have hwt := unitWt_dir d
  rw [hdir] at hwt
  rw [show unitWt (![2, 0] : Site 2) = 2 by simp only [unitWt, Fin.sum_univ_two]; decide] at hwt
  exact absurd hwt (by decide)

/-- `UnitEdgeOrbitTransport K` fails for every finite nonempty `K`: the orbit of the boundary dart
of `ifg_exists_unreached_neighbor` reaches its head but not the lattice neighbour `v`. -/
theorem icb_not_unitEdgeTransport_of_finite (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty) : ¬ UnitEdgeOrbitTransport K := by
  intro htr
  obtain ⟨e, he, v, hv, hadj, hno⟩ := ifg_exists_unreached_neighbor K hK hne
  obtain ⟨d, hd, hdh, -⟩ := htr e he he.2 hv hadj (orbitReached_self K e he)
  exact hno d hd hdh

/-- Under the hypotheses of `exitDart_sameOrbit_of_far`, the upper face of the right
exit and the lower face of the left exit are connected in the face-boundary graph of the origin
cluster. -/
theorem icb_exitFaces_reachable_of_traceSurjective (hfin : (cluster 2 ω (origin 2)).Finite)
    (hsurj : InterfaceConnected (cluster 2 ω (origin 2)))
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    (faceBoundaryGraph (cluster 2 ω (origin 2))).Reachable
      (exitFaceUp (ω := ω) hfin) (leftExitFaceDown (ω := ω) hfin) :=
  exitFaces_reachable_of_sameOrbit (ω := ω) hfin
    (exitDart_sameOrbit_of_far (ω := ω) hfin hsurj R hR hr hl)

end Lattice

end StatMech
