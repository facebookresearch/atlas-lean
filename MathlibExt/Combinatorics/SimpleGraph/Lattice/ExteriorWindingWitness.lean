/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExteriorConnected

/-!
# Winding witnesses from the corrected exterior hypotheses

The hypotheses `exc_OffSupportReachesExterior` and `exc_SupportOddInK` give the inclusion of the
inside of the face loop of a boundary orbit in `K`. When the orbit has period at least three and
no pinched face, the loop is a cycle, so some site has odd ray count; that site lies in `K`, which
gives a winding witness for that orbit.

The results are conditional on the cycle and exterior hypotheses for the given orbit. These cannot
hold for every boundary orbit of every finite set: assumed for all sets with at least two sites
covered by their orbit footprint, they would give `eaw_LoopWindsRegion`, which is false
(`StatMech.Lattice.not_eaw_LoopWindsRegion`, the counterexample being the ring of four neighbours
of the origin).

## Main results

* `StatMech.Lattice.ecd_leftRegion_subset_of_exc`: the inside of the loop is contained in `K`.
* `StatMech.Lattice.ecd_windingWitness_of_cycle_exc`: a winding witness for one orbit.
* `StatMech.Lattice.ecd_loopWindsRegion_conjuncts_of_exc`: the conjuncts of `eaw_LoopWindsRegion`
  for one orbit.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

/-- Under `exc_OffSupportReachesExterior` and `exc_SupportOddInK`, the inside of the face loop is
contained in `K`. -/
theorem ecd_leftRegion_subset_of_exc (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hoff : exc_OffSupportReachesExterior K a) (hsupp : exc_SupportOddInK K a) :
    jec_leftRegion (mpl_orbitLoop K a) ⊆ K := by
  intro z hz
  rw [jec_mem_leftRegion] at hz
  exact exc_interiorSubset_of_reaches_and_support K a hoff hsupp z hz

/-- If the orbit of `a` has period at least three and no pinched face, the two exterior hypotheses
give a winding witness: a site of `K` with odd ray count. -/
theorem ecd_windingWitness_of_cycle_exc (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a)
    (hoff : exc_OffSupportReachesExterior K a) (hsupp : exc_SupportOddInK K a) :
    wei_WindingWitness K a :=
  eaw_windingWitness_of_cycle_interior K a hp hnp
    (exc_interiorSubset_of_reaches_and_support K a hoff hsupp)

/-- The three conjuncts of `eaw_LoopWindsRegion` for one orbit, from the cycle hypotheses and the
exterior hypotheses. -/
theorem ecd_loopWindsRegion_conjuncts_of_exc (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a)
    (hoff : exc_OffSupportReachesExterior K a) (hsupp : exc_SupportOddInK K a) :
    3 ≤ dartOrbitPeriod K a ∧ OrbitFaceNoPinch K a ∧ eaw_InteriorSubset K a :=
  ⟨hp, hnp, exc_interiorSubset_of_reaches_and_support K a hoff hsupp⟩

end Lattice

end StatMech
