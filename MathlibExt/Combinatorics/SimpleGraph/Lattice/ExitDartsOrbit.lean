/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceOrbit

/-!
# The two exit darts of a finite origin cluster lie on one boundary orbit

Let the open cluster of the origin in a bond configuration `ω` on `ℤ²` be finite. Its right exit
dart `exitDart` and left exit dart `leftExitDart` are the boundary darts crossing the last cluster
edge on the positive and the negative horizontal axis. Following boundary darts with `dartNext`
traces the boundary contours of the cluster. This file relates two statements: the left exit dart
lies on the boundary orbit of the right one (`ExitDartsSameOrbit`), and the heads of the two exit
darts lie in the same connected component of the complement of the cluster. The first implies the
second; the converse holds when the cluster is interface connected. Both hold when both heads lie
outside a box containing the cluster, because the exterior of a box is connected.

## Main definitions

* `StatMech.Lattice.exitDart_headSameComponent ω hfin`: the heads of the two exit darts are joined
  by a lattice path avoiding the origin cluster.

## Main results

* `StatMech.Lattice.exitDart_sameOrbit_iff_headSameComponent`: for an interface-connected cluster,
  the exit darts share a boundary orbit if and only if their heads lie in one component of the
  complement.
* `StatMech.Lattice.exitDart_headSameComponent_of_far`,
  `StatMech.Lattice.exitDart_sameOrbit_of_far`: both statements hold when the two heads lie outside
  a box containing the cluster.
-/

@[expose] public section

open Finset Set SimpleGraph Function

namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}

/-- The heads of the right and left exit darts of the finite origin cluster lie in the same
connected component of the lattice with the cluster removed. -/
def exitDart_headSameComponent (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
    ⟨(exitDart (ω := ω) hfin).head, (exitDart_isBoundaryDart (ω := ω) hfin).2⟩
    ⟨(leftExitDart (ω := ω) hfin).head, (leftExitDart_isBoundaryDart (ω := ω) hfin).2⟩

/-- For an interface-connected finite origin cluster, the left exit dart lies on the boundary orbit
of the right exit dart if and only if the heads of the two darts lie in one connected component of
the complement of the cluster. The forward direction holds without interface connectedness
(`StatMech.Lattice.head_compl_of_exitDartsSameOrbit`). Interface connectedness is a hypothesis; the
library proves it only for one-site sets (`StatMech.Lattice.ifc_interfaceConnected`). -/
theorem exitDart_sameOrbit_iff_headSameComponent (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2))) :
    ExitDartsSameOrbit ω hfin ↔ exitDart_headSameComponent ω hfin :=
  ⟨head_compl_of_exitDartsSameOrbit (ω := ω) hfin,
    exitDartsSameOrbit_of_interfaceConnected (ω := ω) hfin hInt⟩

/-- If the cluster lies in `box 2 R` and both exit-dart heads lie in the exterior of that box, the
heads are joined by a path avoiding the cluster, since the exterior of a box is connected. -/
theorem exitDart_headSameComponent_of_far (hfin : (cluster 2 ω (origin 2)).Finite)
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    exitDart_headSameComponent ω hfin := by
  have hkey := exterior_reachable_in_compl (d := 2) (by norm_num)
    (cluster 2 ω (origin 2)) R hR hr hl
  exact complReachable_congr (G := hypercubicLattice 2) (S := (cluster 2 ω (origin 2))ᶜ)
    rfl rfl hkey

/-- For an interface-connected finite origin cluster in the box `box 2 R` whose exit-dart heads both
lie outside the box, the two exit darts lie on one boundary orbit. The hypotheses hold, for example,
for the one-site cluster `{0}` with `R = 0`. -/
theorem exitDart_sameOrbit_of_far (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hr : (exitDart (ω := ω) hfin).head ∈ exterior 2 R)
    (hl : (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R) :
    ExitDartsSameOrbit ω hfin :=
  exitDartsSameOrbit_of_interfaceConnected (ω := ω) hfin hInt
    (exitDart_headSameComponent_of_far (ω := ω) hfin R hR hr hl)

end Lattice

end StatMech
