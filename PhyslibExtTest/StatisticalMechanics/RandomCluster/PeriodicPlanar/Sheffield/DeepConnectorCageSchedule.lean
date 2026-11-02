/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DeepConnectorCageSchedule

/-!
# Tests for `Sheffield.DeepConnectorCageSchedule`

Module under test: `Sheffield.DeepConnectorCageSchedule` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* Refutation: `PeriodicPlanarDualPair.false_of_forall_symmetricBandDeepConnectorCageCertificate`
  shows that no dual pair has a symmetric-band cage certificate for every band and row pair
  (the negation of `hcage`, for any `B ≥ 0` and base vertex).
* `PeriodicPlanarDualPair.SymmetricBandDeepConnectorCageCertificate` and the two vacuous
  consequences elaborate (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace DeepConnectorCageSchedule

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar

variable {V W : Type} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- No family of symmetric-band cage certificates covers all bands (`B = 0`).
example (D : PeriodicPlanarDualPair P Pdual) (rPrimal Rdeep rDual : ℝ) (x0 : V) :
    IsEmpty ((band : ℕ) → (L U : Finset V) → (width : ℕ) →
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices Rdeep →
      (U : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices Rdeep →
      U = L.image (P.shift (verticalShift (1 + 2 * (band : ℤ)))) →
      PeriodicPlanarDualPair.SymmetricBandDeepConnectorCageCertificate D 0 rPrimal Rdeep rDual
        band width L U) :=
  ⟨PeriodicPlanarDualPair.false_of_forall_symmetricBandDeepConnectorCageCertificate D le_rfl x0⟩

open PeriodicPlanarDualPair in
example := @complementaryDual_rightHalfPlane_measure_eq_zero_of_symmetricBandCages

open PeriodicPlanarDualPair in
example := @freeBufferedInfiniteVolume_complementaryDual_rightHalfPlane_zero_of_symmetricBandCages

end DeepConnectorCageSchedule
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
