/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitSeparates
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingWitness

/-!
# Separation by a boundary orbit through its winding region

The darts of a boundary orbit of a finite set `K` trace a closed walk of dual faces, the orbit loop.
Its winding region is the set of sites with odd ray count with respect to that loop. If the edge of
`e` is a boundary edge of the winding region (`OrbitWindsBdEdge`) and every boundary edge of the
winding region is an edge of the orbit (`OrbitFillsWinding`), then deleting the orbit edges
separates the tail of `e` from its head. Applied to every boundary dart of a finite origin cluster,
this gives `InterfaceConnected`. Both conditions follow when `K` and the winding region have the
same boundary edges and the orbit contains every boundary edge of `K`.

## Main definitions

* `StatMech.Lattice.osp_windingRegion K hK e he`: the sites with odd ray count with respect to the
  orbit loop of `e`.
* `StatMech.Lattice.OrbitWindsBdEdge K hK e he`: the edge of `e` has exactly one endpoint in the
  winding region.
* `StatMech.Lattice.OrbitFillsWinding K hK e he`: every boundary edge of the winding region is an
  edge of the orbit of `e`.

## Main results

* `StatMech.Lattice.osp_orbitSeparates_of_residues`: the two conditions imply `OrbitSeparates K e`.
* `StatMech.Lattice.osp_orbitSeparates_of_match_cover`: equal boundary edges of `K` and the winding
  region, together with `OrbitCoversBoundaryEdges`, imply `OrbitSeparates K e`.
* `StatMech.Lattice.osp_interfaceConnected_of_residues`: if the two conditions hold for every
  boundary dart of a finite origin cluster, the cluster satisfies `InterfaceConnected`.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}

/-- The winding region of the boundary orbit of `e`: the sites whose ray count with respect to the
orbit loop of `e` is odd. -/
noncomputable def osp_windingRegion (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : Set (Site 2) :=
  jec_leftRegion (olb_orbitLoop K hK e he)

@[simp] theorem osp_mem_windingRegion (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (z : Site 2) :
    z ∈ osp_windingRegion K hK e he ↔ ¬ Even (jec_rayCount z (olb_orbitLoop K hK e he)) :=
  Iff.rfl

/-- The edge of `e` has exactly one endpoint in the winding region of the orbit of `e`. -/
def OrbitWindsBdEdge (K : Set (Site 2)) (hK : K.Finite) (e : Dart) (he : IsBoundaryDart K e) :
    Prop :=
  bdEdge (osp_windingRegion K hK e he) s(e.tail, e.head)

/-- Every boundary edge of the winding region of the orbit of `e` is an edge of that orbit. -/
def OrbitFillsWinding (K : Set (Site 2)) (hK : K.Finite) (e : Dart) (he : IsBoundaryDart K e) :
    Prop :=
  ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
    bdEdge (osp_windingRegion K hK e he) s(x, y) → IsOrbitEdge K e x y

/-- If the edge of `e` is a boundary edge of the winding region and every boundary edge of the
winding region is an orbit edge, then the orbit of `e` separates the tail of `e` from its head: a
path avoiding the orbit edges would stay on one side of the winding region. -/
theorem osp_orbitSeparates_of_residues (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hF1 : OrbitWindsBdEdge K hK e he) (hF2 : OrbitFillsWinding K hK e he) :
    OrbitSeparates K e := by
  set S := osp_windingRegion K hK e he with hSdef
  intro hreach
  have hle : latticeMinusOrbit K e ≤ latticeMinusBarrier S := by
    intro x y h
    obtain ⟨hadj, hno⟩ := h
    exact ⟨hadj, fun hbd => hno (hF2 x y hadj hbd)⟩
  obtain ⟨w⟩ := hreach.mono hle
  have hsame : (e.tail ∈ S ↔ e.head ∈ S) := latticeMinusBarrier_sameSide S w
  have hF1' : (e.tail ∈ S ↔ e.head ∉ S) := by
    unfold OrbitWindsBdEdge at hF1; rw [← hSdef, bdEdge_mk] at hF1; exact hF1
  by_cases ht : e.tail ∈ S
  · exact (hF1'.mp ht) (hsame.mp ht)
  · have hh : ¬ (e.head ∉ S) := fun hno => ht (hF1'.mpr hno)
    push Not at hh
    exact ht (hsame.mpr hh)

theorem osp_orbitWindsBdEdge_iff (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) :
    OrbitWindsBdEdge K hK e he ↔
      (e.tail ∈ osp_windingRegion K hK e he ↔ e.head ∉ osp_windingRegion K hK e he) := by
  unfold OrbitWindsBdEdge; rw [bdEdge_mk]

/-- An edge of a boundary orbit of `K` is a boundary edge of `K`. -/
theorem osp_orbitEdge_bdEdge (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e)
    {x y : Site 2} (h : IsOrbitEdge K e x y) : bdEdge K s(x, y) := by
  rw [bdEdge_mk]; exact obs_orbitEdge_one_in_K K e he h

/-- Every edge of a boundary orbit of a single site `c` has `c` as an endpoint. -/
theorem osp_singleton_orbitEdge_endpoint (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) {x y : Site 2}
    (h : IsOrbitEdge ({c} : Set (Site 2)) e x y) : x = c ∨ y = c := by
  obtain ⟨d, hbd, _hso, hcase⟩ := obs_orbitEdge_isBoundaryDart ({c} : Set (Site 2)) e he h
  have hdc : d.tail = c := by
    have : d.tail ∈ ({c} : Set (Site 2)) := hbd.1
    rwa [Set.mem_singleton_iff] at this
  rcases hcase with ⟨ht, _hh⟩ | ⟨ht, _hh⟩
  · left; rw [← ht]; exact hdc
  · right; rw [← ht]; exact hdc

/-- The edge from `c` to `c + (1,0)` is an edge of every boundary orbit of the single site `c`. -/
theorem osp_singleton_posAxisEdge_isOrbitEdge (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    IsOrbitEdge ({c} : Set (Site 2)) e c (c + ![1, 0]) := by
  have hadj : (hypercubicLattice 2).Adj c (c + ![1, 0]) := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hne : (c + ![1, 0] : Site 2) ≠ c := by
    intro hcon
    have : (c + ![1, 0] : Site 2) 0 = c 0 := by rw [hcon]
    simp at this
  set d : Dart := ⟨c, c + ![1, 0], hadj⟩ with hd
  have hdbd : IsBoundaryDart ({c} : Set (Site 2)) d :=
    ⟨Set.mem_singleton _, by rw [Set.mem_singleton_iff]; exact hne⟩
  exact ⟨d, ifc_singleton_sameOrbit c e d he hdbd, Or.inl ⟨rfl, rfl⟩⟩

/-- For a single site `c`, the site `c + (1,0)` lies on exactly one orbit edge, the one to `c`; so
the orbit edges, as a primal edge set, do not form a closed walk. -/
theorem osp_singleton_orbitEdges_not_even_degree (c : Site 2) (e : Dart)
    (he : IsBoundaryDart ({c} : Set (Site 2)) e) :
    IsOrbitEdge ({c} : Set (Site 2)) e c (c + ![1, 0]) ∧
      (∀ y : Site 2, IsOrbitEdge ({c} : Set (Site 2)) e (c + ![1, 0]) y → y = c) := by
  refine ⟨osp_singleton_posAxisEdge_isOrbitEdge c e he, ?_⟩
  intro y h
  rcases osp_singleton_orbitEdge_endpoint c e he h with h1 | h1
  · exfalso
    have : (c + ![1, 0] : Site 2) 0 = c 0 := by rw [h1]
    simp at this
  · exact h1

/-- If `K` and the winding region of the orbit of `e` have the same boundary edges, the edge of `e`
is a boundary edge of the winding region. -/
theorem osp_orbitWindsBdEdge_of_match (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he)) :
    OrbitWindsBdEdge K hK e he := by
  have hbdK : bdEdge K s(e.tail, e.head) := by
    rw [bdEdge_mk]; exact ⟨fun _ => he.2, fun _ => he.1⟩
  exact (hmatch s(e.tail, e.head)).mp hbdK

/-- If `K` and the winding region of the orbit of `e` have the same boundary edges and the orbit of
`e` contains every boundary edge of `K`, the orbit fills the boundary of the winding region. -/
theorem osp_orbitFillsWinding_of_match (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he))
    (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitFillsWinding K hK e he := by
  intro x y hadj hbd
  have hbdK : bdEdge K s(x, y) := (hmatch s(x, y)).mpr hbd
  exact hcov hadj hbdK

/-- If `K` and the winding region of the orbit of `e` have the same boundary edges and the orbit of
`e` contains every boundary edge of `K`, the orbit separates. For finite `K` the first hypothesis
forces `K` to equal the winding region whenever the latter is finite (their symmetric difference has
no boundary edge), and the second says that `K` has a single boundary orbit; so these hypotheses can
only hold when `K` has no holes. -/
theorem osp_orbitSeparates_of_match_cover (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he))
    (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitSeparates K e :=
  osp_orbitSeparates_of_residues K hK e he
    (osp_orbitWindsBdEdge_of_match K hK e he hmatch)
    (osp_orbitFillsWinding_of_match K hK e he hmatch hcov)

/-- If every boundary dart of a finite origin cluster satisfies `OrbitWindsBdEdge` and
`OrbitFillsWinding`, the cluster satisfies `InterfaceConnected`. Neither hypothesis is proved here
for any cluster. -/
theorem osp_interfaceConnected_of_residues (hfin : (cluster 2 ω (origin 2)).Finite)
    (hF1 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      OrbitWindsBdEdge (cluster 2 ω (origin 2)) hfin e he)
    (hF2 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      OrbitFillsWinding (cluster 2 ω (origin 2)) hfin e he) :
    InterfaceConnected (cluster 2 ω (origin 2)) :=
  obs_interfaceConnected_of_orbitSeparates (origin 2)
    (fun e he => osp_orbitSeparates_of_residues (cluster 2 ω (origin 2)) hfin e he (hF1 e he)
      (hF2 e he))

/-- Under the hypotheses of `osp_interfaceConnected_of_residues`, if the heads of both exit darts
lie outside a box containing the cluster, the two exit darts share an orbit. -/
theorem osp_exitDartsSameOrbit_of_residues (hfin : (cluster 2 ω (origin 2)).Finite)
    (hF1 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      OrbitWindsBdEdge (cluster 2 ω (origin 2)) hfin e he)
    (hF2 : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      OrbitFillsWinding (cluster 2 ω (origin 2)) hfin e he)
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    ExitDartsSameOrbit ω hfin :=
  obs_exitDartsSameOrbit_of_orbitSeparates (ω := ω) hfin
    (fun e he => osp_orbitSeparates_of_residues (cluster 2 ω (origin 2)) hfin e he (hF1 e he)
      (hF2 e he)) R hR hr hl

end Lattice

end StatMech
