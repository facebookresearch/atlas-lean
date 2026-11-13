/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Walls.bc4_core
import Code.Walls.bc7distinctwitnessclusters

open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation

namespace StatMech

namespace Walls

variable {d : ℕ}
















theorem bc8_cutCluster_distinct_of_baseClusters (ω : ConfigSpace (Sym2 (Site d)))
    {x₁ x₂ x₃ : Site d}
    (hi1 : (cluster d ω x₁).Infinite) (hi2 : (cluster d ω x₂).Infinite)
    (hi3 : (cluster d ω x₃).Infinite)
    (hd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hd23 : cluster d ω x₂ ≠ cluster d ω x₃) :
    ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧
      x₃' ∈ cluster d ω x₃ ∧
      (cluster d (removeSite 0 ω) x₁').Infinite ∧
      (cluster d (removeSite 0 ω) x₂').Infinite ∧
      (cluster d (removeSite 0 ω) x₃').Infinite ∧
      cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' ∧
      cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₃' ∧
      cluster d (removeSite 0 ω) x₂' ≠ cluster d (removeSite 0 ω) x₃' :=
  bc7_threeArms_cutInfinite_distinct ω hi1 hi2 hi3 hd12 hd13 hd23











def bc8_DistinctCutClusters (d n : ℕ) : Prop :=
  ∀ ω ∈ threeMeetBox d n,
    ∃ x₁ x₂ x₃ : Site d, x₁ ∈ box d n ∧ x₂ ∈ box d n ∧ x₃ ∈ box d n ∧
      (cluster d ω x₁).Infinite ∧ (cluster d ω x₂).Infinite ∧ (cluster d ω x₃).Infinite ∧
      cluster d ω x₁ ≠ cluster d ω x₂ ∧ cluster d ω x₁ ≠ cluster d ω x₃ ∧
      cluster d ω x₂ ≠ cluster d ω x₃ ∧
      ∃ x₁' x₂' x₃' : Site d, x₁' ∈ cluster d ω x₁ ∧ x₂' ∈ cluster d ω x₂ ∧
        x₃' ∈ cluster d ω x₃ ∧
        (cluster d (removeSite 0 ω) x₁').Infinite ∧
        (cluster d (removeSite 0 ω) x₂').Infinite ∧
        (cluster d (removeSite 0 ω) x₃').Infinite ∧
        cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' ∧
        cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₃' ∧
        cluster d (removeSite 0 ω) x₂' ≠ cluster d (removeSite 0 ω) x₃'










theorem bc8_distinctCutClusters (n : ℕ) : bc8_DistinctCutClusters d n :=
  bc7_distinctWitnessClusters n













theorem bc8_threeArmClusters_distinct (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hω : ω ∈ threeMeetBox d n) :
    ∃ x₁' x₂' x₃' : Site d,
      (cluster d (removeSite 0 ω) x₁').Infinite ∧
      (cluster d (removeSite 0 ω) x₂').Infinite ∧
      (cluster d (removeSite 0 ω) x₃').Infinite ∧
      cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₂' ∧
      cluster d (removeSite 0 ω) x₁' ≠ cluster d (removeSite 0 ω) x₃' ∧
      cluster d (removeSite 0 ω) x₂' ≠ cluster d (removeSite 0 ω) x₃' := by
  obtain ⟨_x₁, _x₂, _x₃, _hb1, _hb2, _hb3, _hi1, _hi2, _hi3, _hd12, _hd13, _hd23,
      x₁', x₂', x₃', _hx₁', _hx₂', _hx₃', hinf₁, hinf₂, hinf₃, hcd12, hcd13, hcd23⟩ :=
    bc8_distinctCutClusters n ω hω
  exact ⟨x₁', x₂', x₃', hinf₁, hinf₂, hinf₃, hcd12, hcd13, hcd23⟩









theorem bc8_distinctCutClusters_eq (n : ℕ) :
    bc8_DistinctCutClusters d n = bc7_DistinctWitnessClusters d n := rfl

end Walls

end StatMech
