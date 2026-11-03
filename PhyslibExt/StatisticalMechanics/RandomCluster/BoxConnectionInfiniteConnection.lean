/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.TwoPointInfinite
public import PhyslibExt.StatisticalMechanics.RandomCluster.TwoPointConnectivity

/-!
# Box connections imply connections in the infinite lattice

An open path inside a finite box is an open path in `ℤ^d`, so box two-point probabilities are
bounded by infinite-volume two-point probabilities.

## i. Overview

The open subgraph of the box, computed from the restriction of a configuration on `ℤ^d`, maps into
the open subgraph of the whole lattice by the inclusion of vertices. Hence the box connection event
is contained in the infinite-volume connection event, and for any probability measure on
configurations of `ℤ^d` its probability is at most the infinite-volume two-point function.

Both results are proved unconditionally, for every probability measure on configurations.

## ii. Key results

- `boxConnEvent_subset_connected` : a connection inside the box is a connection in `ℤ^d`.
- `measureReal_boxConnEvent_le_infiniteTwoPointReal` : the box two-point probability is at most the
  infinite-volume one.

## iii. Table of contents

- A. Box connections and infinite connections

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open MeasureTheory SimpleGraph

namespace StatMech.FK

noncomputable section

open StatMech.Lattice

/-! ## A. Box connections and infinite connections -/

/-- If `x` and `y` are joined by an open path inside the box, they are joined in `ℤ^d`. -/
lemma boxConnEvent_subset_connected (d n : Nat)
    (x y : boxVerts d n) :
    boxConnEvent d n x y ⊆
      {omega | StatMech.Lattice.Connected d omega x.1 y.1} := by
  intro omega hreach
  let f : openSub (boxGraph d n) (boxRestrict d n omega) →g
      openSubgraph d omega :=
    { toFun := Subtype.val
      map_rel' := fun {u v} huv => by
        refine ⟨huv.1, ?_⟩
        simpa [boxRestrict, edgeIncl] using huv.2 }
  exact hreach.map f

/-- For any probability measure on configurations of `ℤ^d`, the probability that `x` and `y` are
connected inside the box is at most the probability that they are connected in `ℤ^d`. -/
theorem measureReal_boxConnEvent_le_infiniteTwoPointReal
    (d n : Nat)
    (mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d))))
    (x y : boxVerts d n) :
    (mu : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxConnEvent d n x y) ≤
      infiniteTwoPointReal
        (mu : Measure (ConfigSpace (Sym2 (Site d)))) x.1 y.1 := by
  exact measureReal_mono (boxConnEvent_subset_connected d n x y)

end

end StatMech.FK
