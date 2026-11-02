/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.PivotalSurfaceFactor

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.PivotalSurfaceFactor`

* `pivotal_surface_event_eq_withinConn` and `pivotal_surface_factor` applied to a surface
  `0 ∈ S ⊆ Λ_{n-1}` and a boundary pair;
* at `p = 0` the factorization still holds (the measure is the point mass on the empty
  configuration).
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.PivotalSurfaceFactor

open _root_.StatMech _root_.StatMech.Percolation _root_.StatMech.Lattice

-- The event identity.
example (d n : ℕ) (S : Finset (Site d)) (hS : origin d ∈ S)
    (hbox : (S : Set (Site d)) ⊆ box d (n - 1)) (hn : 1 ≤ n) (e : Site d × Site d)
    (he : e ∈ boundaryEdges d S) :
    pivotalEvent s(e.1, e.2) (boxCrossingEvent d n) ∩ surfaceEvent d n S =
      withinConnEvent d S (origin d) e.1 ∩ surfaceEvent d n S :=
  pivotal_surface_event_eq_withinConn hS hbox hn he

-- The factorization of the probability.
example (d n : ℕ) (p : NNReal) (hp : p ≤ 1) (S : Finset (Site d)) (hS : origin d ∈ S)
    (hbox : (S : Set (Site d)) ⊆ box d (n - 1)) (hn : 1 ≤ n) (e : Site d × Site d)
    (he : e ∈ boundaryEdges d S) :
    (bernoulliProductMeasure p hp).real
        (pivotalEvent s(e.1, e.2) (boxCrossingEvent d n) ∩ surfaceEvent d n S) =
      (bernoulliProductMeasure p hp).real (withinConnEvent d S (origin d) e.1) *
        (bernoulliProductMeasure p hp).real (surfaceEvent d n S) :=
  pivotal_surface_factor p hp hS hbox hn he

-- The same at `p = 0`.
example (d n : ℕ) (S : Finset (Site d)) (hS : origin d ∈ S)
    (hbox : (S : Set (Site d)) ⊆ box d (n - 1)) (hn : 1 ≤ n) (e : Site d × Site d)
    (he : e ∈ boundaryEdges d S) :
    (bernoulliProductMeasure 0 zero_le_one).real
        (pivotalEvent s(e.1, e.2) (boxCrossingEvent d n) ∩ surfaceEvent d n S) =
      (bernoulliProductMeasure 0 zero_le_one).real (withinConnEvent d S (origin d) e.1) *
        (bernoulliProductMeasure 0 zero_le_one).real (surfaceEvent d n S) :=
  pivotal_surface_factor 0 zero_le_one hS hbox hn he

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.PivotalSurfaceFactor
