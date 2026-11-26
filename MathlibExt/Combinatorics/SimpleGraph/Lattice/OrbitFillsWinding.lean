/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingSeparates

/-!
# Filling the winding region of a boundary orbit

`OrbitFillsWinding` asks that every boundary edge of the winding region of a boundary orbit be an
edge of the orbit. When the orbit contains every boundary edge of `K`, this is equivalent to the
reverse inclusion of boundary edges, `OrbitWindingRevMatch`: every boundary edge of the winding
region is a boundary edge of `K`.

## Main definitions

* `StatMech.Lattice.OrbitWindingRevMatch K hK e he`: every boundary edge of the winding region of
  the orbit of `e` is a boundary edge of `K`.

## Main results

* `StatMech.Lattice.ofw_orbitFillsWinding_iff_via_coverage`: if the orbit of `e` contains every
  boundary edge of `K`, `OrbitFillsWinding` is equivalent to `OrbitWindingRevMatch`.
* `StatMech.Lattice.ofw_traceSurjective_of_revMatch_cover`: for a finite origin cluster, equal
  boundary edges of the cluster and each winding region, together with orbits covering every
  boundary edge, give `InterfaceConnected`.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}

/-- Every boundary edge of the winding region of the orbit of `e` (the sites with odd ray count with
respect to the orbit loop) is a boundary edge of `K`. This is one half of `pww_BdEdgeMatch`. -/
def OrbitWindingRevMatch (K : Set (Site 2)) (hK : K.Finite) (e : Dart) (he : IsBoundaryDart K e) :
    Prop :=
  ∀ x y : Site 2, (hypercubicLattice 2).Adj x y →
    bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(x, y) → bdEdge K s(x, y)

/-- `OrbitWindingRevMatch` and `OrbitCoversBoundaryEdges` imply `OrbitFillsWinding`. -/
theorem ofw_orbitFillsWinding_of_revMatch (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hrev : OrbitWindingRevMatch K hK e he)
    (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitFillsWinding K hK e he := by
  intro x y hadj hbd
  have hbdK : bdEdge K s(x, y) := hrev x y hadj hbd
  exact hcov hadj hbdK

/-- Equal boundary edges of `K` and the winding region imply `OrbitWindingRevMatch`. -/
theorem ofw_revMatch_of_match (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he)) :
    OrbitWindingRevMatch K hK e he := by
  intro x y _hadj hbd
  exact (hmatch s(x, y)).mpr hbd

/-- If the orbit of `e` contains every boundary edge of `K`, then `OrbitFillsWinding` holds if and
only if `OrbitWindingRevMatch` does. -/
theorem ofw_orbitFillsWinding_iff_via_coverage (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitFillsWinding K hK e he ↔ OrbitWindingRevMatch K hK e he := by
  constructor
  · intro hF2 x y hadj hbd
    exact osp_orbitEdge_bdEdge K e he (hF2 x y hadj hbd)
  · intro hrev
    exact ofw_orbitFillsWinding_of_revMatch K hK e he hrev hcov

/-- If, for every boundary dart `e` of a finite origin cluster, the cluster and the winding region
of the orbit of `e` have the same boundary edges and the orbit of `e` contains every boundary edge
of the cluster, then the cluster satisfies `InterfaceConnected`. The covering hypothesis says the
cluster has a single boundary orbit, and with the first hypothesis it forces the cluster to be the
winding region when the latter is finite; so the hypotheses can only hold for clusters without
holes. They are not proved here for any cluster. -/
theorem ofw_traceSurjective_of_revMatch_cover (hfin : (cluster 2 ω (origin 2)).Finite)
    (hmatch : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      pww_BdEdgeMatch (cluster 2 ω (origin 2))
        (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he))
    (hcov : ∀ (e : Dart), IsBoundaryDart (cluster 2 ω (origin 2)) e →
      OrbitCoversBoundaryEdges (cluster 2 ω (origin 2)) e) :
    InterfaceConnected (cluster 2 ω (origin 2)) :=
  obs_interfaceConnected_of_orbitSeparates (origin 2)
    (fun e he => osp_orbitSeparates_of_match_cover (cluster 2 ω (origin 2)) hfin e he
      (hmatch e he) (hcov e he))

end Lattice

end StatMech
