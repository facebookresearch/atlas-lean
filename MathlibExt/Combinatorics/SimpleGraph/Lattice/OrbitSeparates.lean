/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitDartsOrbit
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnectedSingleton

/-!
# Separating boundary orbits and `InterfaceConnected` for clusters

The edges of a boundary orbit of `K` are the lattice edges crossed by its darts. If deleting the
edges of every boundary orbit of a cluster separates the tail of each of its darts from the head
(`OrbitSeparates`), the cluster satisfies `InterfaceConnected`: a boundary dart whose head is
connected to the head of `e` outside the cluster must itself cross an edge of the orbit of `e`.
An orbit that contains every boundary edge of `K` separates. Both properties are checked for a
single site.

## Main definitions

* `StatMech.Lattice.IsOrbitEdge K e x y`: some dart in the orbit of `e` runs along the edge
  `{x, y}`.
* `StatMech.Lattice.latticeMinusOrbit K e`: the square lattice with the edges of the orbit of `e`
  deleted.
* `StatMech.Lattice.OrbitSeparates K e`: in `latticeMinusOrbit K e`, the tail of `e` cannot reach
  its head.
* `StatMech.Lattice.OrbitCoversBoundaryEdges K e`: every boundary edge of `K` is an edge of the
  orbit of `e`.

## Main results

* `StatMech.Lattice.obs_interfaceConnected_of_orbitSeparates`: if every boundary orbit of a cluster
  separates, the cluster satisfies `InterfaceConnected`.
* `StatMech.Lattice.obs_orbitSeparates_of_coversBoundary`: an orbit containing every boundary edge
  separates.
* `StatMech.Lattice.obs_orbitSeparates_singleton`: every boundary orbit of a single site separates.
* `StatMech.Lattice.obs_exitDartsSameOrbit_of_orbitSeparates`: for the origin cluster, separating
  orbits and exit heads far away give `ExitDartsSameOrbit`.
-/

@[expose] public section

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}

/-- Some dart in the orbit of `e` under `dartNext K` runs along the lattice edge `{x, y}`, in either
direction. -/
def IsOrbitEdge (K : Set (Site 2)) (e : Dart) (x y : Site 2) : Prop :=
  ∃ d : Dart, SameOrbit K e d ∧
    ((d.tail = x ∧ d.head = y) ∨ (d.tail = y ∧ d.head = x))

theorem obs_isOrbitEdge_symm (K : Set (Site 2)) (e : Dart) {x y : Site 2}
    (h : IsOrbitEdge K e x y) : IsOrbitEdge K e y x := by
  obtain ⟨d, hd, hc⟩ := h; exact ⟨d, hd, hc.symm⟩

/-- The square lattice with the edges of the boundary orbit of `e` deleted. -/
noncomputable def latticeMinusOrbit (K : Set (Site 2)) (e : Dart) : SimpleGraph (Site 2) where
  Adj x y := (hypercubicLattice 2).Adj x y ∧ ¬ IsOrbitEdge K e x y
  symm := ⟨by
    intro x y ⟨hadj, hno⟩
    exact ⟨hadj.symm, fun h => hno (obs_isOrbitEdge_symm K e h)⟩⟩
  loopless := ⟨fun _ h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem latticeMinusOrbit_adj (K : Set (Site 2)) (e : Dart) (x y : Site 2) :
    (latticeMinusOrbit K e).Adj x y ↔
      (hypercubicLattice 2).Adj x y ∧ ¬ IsOrbitEdge K e x y := Iff.rfl

/-- An edge of the orbit of a boundary dart is crossed by a boundary dart of that orbit. -/
theorem obs_orbitEdge_isBoundaryDart (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) {x y : Site 2} (h : IsOrbitEdge K e x y) :
    ∃ d : Dart, IsBoundaryDart K d ∧ SameOrbit K e d ∧
      ((d.tail = x ∧ d.head = y) ∨ (d.tail = y ∧ d.head = x)) := by
  obtain ⟨d, hd, hcase⟩ := h
  obtain ⟨n, hn⟩ := hd
  have hbd : IsBoundaryDart K d := by rw [← hn]; exact iterate_isBoundaryDart K e he n
  exact ⟨d, hbd, ⟨n, hn⟩, hcase⟩

/-- An edge of a boundary orbit of `K` has exactly one endpoint in `K`. -/
theorem obs_orbitEdge_one_in_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (h : IsOrbitEdge K e x y) : (x ∈ K ↔ y ∉ K) := by
  obtain ⟨d, hbd, _, hcase⟩ := obs_orbitEdge_isBoundaryDart K e he h
  rcases hcase with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · subst ht hh; exact ⟨fun _ => hbd.2, fun _ => hbd.1⟩
  · subst ht hh; exact ⟨fun hx => absurd hx hbd.2, fun hy => absurd hbd.1 hy⟩

/-- An edge with both endpoints in `K` is not an edge of a boundary orbit of `K`. -/
theorem obs_not_orbitEdge_of_both_in_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (hx : x ∈ K) (hy : y ∈ K) : ¬ IsOrbitEdge K e x y := fun h =>
  (obs_orbitEdge_one_in_K K e he h).mp hx hy

/-- An edge with both endpoints outside `K` is not an edge of a boundary orbit of `K`. -/
theorem obs_not_orbitEdge_of_both_not_in_K (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (hx : x ∉ K) (hy : y ∉ K) : ¬ IsOrbitEdge K e x y := fun h => by
  have hiff := obs_orbitEdge_one_in_K K e he h
  exact hy (by by_contra hyk; exact hx (hiff.mpr hyk))

/-- Sites connected by a lattice path in `Kᶜ` stay connected after the edges of a boundary orbit are
deleted. -/
theorem obs_orbitReachable_of_complReachable (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) {u w : Site 2} (hu : u ∉ K) (hw : w ∉ K)
    (h : ((hypercubicLattice 2).induce Kᶜ).Reachable ⟨u, hu⟩ ⟨w, hw⟩) :
    (latticeMinusOrbit K e).Reachable u w := by
  obtain ⟨p⟩ := h
  suffices H : ∀ (a b : ↥(Kᶜ : Set (Site 2))), ((hypercubicLattice 2).induce Kᶜ).Walk a b →
      (latticeMinusOrbit K e).Reachable (a : Site 2) (b : Site 2) from H ⟨u, hu⟩ ⟨w, hw⟩ p
  intro a b q
  induction q with
  | nil => exact Reachable.refl _
  | @cons a b c hadj q' ih =>
    have hadj' : (hypercubicLattice 2).Adj (a : Site 2) (b : Site 2) := hadj
    have hno : ¬ IsOrbitEdge K e (a : Site 2) (b : Site 2) :=
      obs_not_orbitEdge_of_both_not_in_K K e he a.2 b.2
    exact (SimpleGraph.Adj.reachable ((latticeMinusOrbit_adj K e _ _).mpr ⟨hadj', hno⟩)).trans ih

/-- Sites joined by an open path starting in the cluster of `o` stay connected after the edges of a
boundary orbit of that cluster are deleted. -/
theorem obs_orbitReachable_of_connected (o : Site 2) (e : Dart)
    (he : IsBoundaryDart (cluster 2 ω o) e) {x y : Site 2}
    (hx : x ∈ cluster 2 ω o) (hxy : Connected 2 ω x y) :
    (latticeMinusOrbit (cluster 2 ω o) e).Reachable x y := by
  obtain ⟨p⟩ := hxy
  suffices H : ∀ (a b : Site 2), (openSubgraph 2 ω).Walk a b → a ∈ cluster 2 ω o →
      (latticeMinusOrbit (cluster 2 ω o) e).Reachable a b from H x y p hx
  intro a b q
  induction q with
  | nil => intro _; exact Reachable.refl _
  | @cons a b c hadj q' ih =>
    intro ha
    have hadjL : (hypercubicLattice 2).Adj a b := hadj.1
    have hab_open : Connected 2 ω a b := ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩
    have hb : b ∈ cluster 2 ω o := by rw [mem_cluster] at ha ⊢; exact ha.trans hab_open
    have hno : ¬ IsOrbitEdge (cluster 2 ω o) e a b :=
      obs_not_orbitEdge_of_both_in_K (cluster 2 ω o) e he ha hb
    exact
      (SimpleGraph.Adj.reachable ((latticeMinusOrbit_adj _ e _ _).mpr ⟨hadjL, hno⟩)).trans (ih hb)

/-- If the edge of a boundary dart `f` is an edge of the orbit of `e`, then `f` lies in the orbit of
`e`. -/
theorem obs_sameOrbit_of_orbitEdge_boundary (K : Set (Site 2)) (e f : Dart)
    (he : IsBoundaryDart K e) (hf : IsBoundaryDart K f)
    (h : IsOrbitEdge K e f.tail f.head) : SameOrbit K e f := by
  obtain ⟨d, hbd, hso, hcase⟩ := obs_orbitEdge_isBoundaryDart K e he h
  rcases hcase with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · have heq : d = f := Dart.ext ht hh
    rwa [heq] at hso
  · exfalso
    have hdtail : d.tail ∈ K := hbd.1
    rw [ht] at hdtail
    exact hf.2 hdtail

/-- Deleting the edges of the boundary orbit of `e` separates the tail of `e` from its head. -/
def OrbitSeparates (K : Set (Site 2)) (e : Dart) : Prop :=
  ¬ (latticeMinusOrbit K e).Reachable e.tail e.head

/-- If every boundary orbit of the cluster of `o` separates, the cluster satisfies
`InterfaceConnected`. This is a discrete form of the fact that each boundary contour of a planar
cluster is a closed curve with the cluster on one side. The hypothesis is proved here only for
single sites (`obs_orbitSeparates_singleton`); for a general finite cluster it is a discrete Jordan
curve statement for each boundary contour and is not proved. -/
theorem obs_interfaceConnected_of_orbitSeparates (o : Site 2)
    (hsep : ∀ e : Dart, IsBoundaryDart (cluster 2 ω o) e → OrbitSeparates (cluster 2 ω o) e) :
    InterfaceConnected (cluster 2 ω o) := by
  intro e f he hf hreach
  set K := cluster 2 ω o with hK
  have hReachTail : (latticeMinusOrbit K e).Reachable e.tail f.tail := by
    have h1 : (latticeMinusOrbit K e).Reachable o e.tail :=
      obs_orbitReachable_of_connected o e he (self_mem_cluster ω o) he.1
    have h2 : (latticeMinusOrbit K e).Reachable o f.tail :=
      obs_orbitReachable_of_connected o e he (self_mem_cluster ω o) hf.1
    exact h1.symm.trans h2
  have hReachHead : (latticeMinusOrbit K e).Reachable e.head f.head :=
    obs_orbitReachable_of_complReachable K e he he.2 hf.2 hreach
  have hsepe : ¬ (latticeMinusOrbit K e).Reachable e.tail e.head := hsep e he
  by_cases hOE : IsOrbitEdge K e f.tail f.head
  · exact obs_sameOrbit_of_orbitEdge_boundary K e f he hf hOE
  · exfalso
    have hadjLMO : (latticeMinusOrbit K e).Adj f.tail f.head :=
      (latticeMinusOrbit_adj K e _ _).mpr ⟨f.adj, hOE⟩
    exact hsepe ((hReachTail.trans hadjLMO.reachable).trans hReachHead.symm)

/-- Every boundary edge of `K` is an edge of the orbit of `e`, so `K` has a single boundary orbit.
This fails when `K` has more than one boundary contour, for instance when `K` surrounds a hole. -/
def OrbitCoversBoundaryEdges (K : Set (Site 2)) (e : Dart) : Prop :=
  ∀ {x y : Site 2}, (hypercubicLattice 2).Adj x y → bdEdge K s(x, y) → IsOrbitEdge K e x y

/-- If the orbit of `e` covers every boundary edge of `K`, deleting its edges removes every boundary
edge of `K`. -/
theorem obs_latticeMinusOrbit_le_barrier (K : Set (Site 2)) (e : Dart)
    (hcov : OrbitCoversBoundaryEdges K e) :
    latticeMinusOrbit K e ≤ latticeMinusBarrier K := by
  intro x y h
  obtain ⟨hadj, hno⟩ := h
  exact ⟨hadj, fun hbd => hno (hcov hadj hbd)⟩

/-- An orbit containing every boundary edge of `K` separates the tail of `e` from its head. -/
theorem obs_orbitSeparates_of_coversBoundary (K : Set (Site 2)) (e : Dart)
    (he : IsBoundaryDart K e) (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitSeparates K e := by
  intro hreach
  have hbarrier : (latticeMinusBarrier K).Reachable e.tail e.head :=
    hreach.mono (obs_latticeMinusOrbit_le_barrier K e hcov)
  exact not_reachable_latticeMinusBarrier K he.1 he.2 hbarrier

/-- The boundary orbit of a single site contains its four boundary edges. -/
theorem obs_orbitCoversBoundaryEdges_singleton (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    OrbitCoversBoundaryEdges ({c} : Set (Site 2)) e := by
  intro x y hadj hbd
  rw [bdEdge_mk] at hbd
  simp only [Set.mem_singleton_iff] at hbd
  by_cases hx : x = c
  · have hy : y ≠ c := by have := hbd.mp hx; simpa using this
    have hadjcy : (hypercubicLattice 2).Adj c y := by rw [← hx]; exact hadj
    refine ⟨⟨c, y, hadjcy⟩, ?_, Or.inl ⟨hx.symm, rfl⟩⟩
    exact ifc_singleton_sameOrbit c e ⟨c, y, hadjcy⟩ he
      ⟨Set.mem_singleton _, by simpa using hy⟩
  · have hy : y = c := by
      by_contra hyne
      exact hx (hbd.mpr hyne)
    have hadjcx : (hypercubicLattice 2).Adj c x := by rw [← hy]; exact hadj.symm
    refine ⟨⟨c, x, hadjcx⟩, ?_, Or.inr ⟨hy.symm, rfl⟩⟩
    exact ifc_singleton_sameOrbit c e ⟨c, x, hadjcx⟩ he
      ⟨Set.mem_singleton _, by simpa using hx⟩

/-- Every boundary orbit of a single site separates. -/
theorem obs_orbitSeparates_singleton (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    OrbitSeparates ({c} : Set (Site 2)) e :=
  obs_orbitSeparates_of_coversBoundary ({c} : Set (Site 2)) e he
    (obs_orbitCoversBoundaryEdges_singleton c e he)

/-- For the origin cluster, if every boundary orbit separates and the heads of both exit darts lie
outside a box containing the cluster, the two exit darts share an orbit. -/
theorem obs_exitDartsSameOrbit_of_orbitSeparates (hfin : (cluster 2 ω (origin 2)).Finite)
    (hsep : ∀ e : Dart, IsBoundaryDart (cluster 2 ω (origin 2)) e →
        OrbitSeparates (cluster 2 ω (origin 2)) e)
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    ExitDartsSameOrbit ω hfin :=
  exitDart_sameOrbit_of_far (ω := ω) hfin
    (obs_interfaceConnected_of_orbitSeparates (origin 2) hsep) R hR hr hl

end Lattice

end StatMech
