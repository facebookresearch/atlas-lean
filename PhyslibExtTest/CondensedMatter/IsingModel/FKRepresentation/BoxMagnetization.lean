/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.BoxMagnetization

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.HisingBoxClose`

* `hbx_hisingBox` at `d = 2`, `β = 1`, `n = 1`: the lattice magnetization in `Λ_1` is the wired
  Edwards–Sokal one-point function of the box graph `Λ_2` at `p = 1 - e^{-2}`;
* `hbx_hisingBox` discharges the hypothesis `hisingBox` of `mfc_magPercoId`
  (`MagnetizationCorrespondence`), giving `m*(1) = θ_FK(1 - e^{-2}, 2)` on `ℤ²` and hence
  `m*(1) ≥ 0`.

The conditional transition lemmas `hbx_ising_transition`, `hbx_isingBetaC_eq` (and
`mfc_ising_transition`, `mfc_isingBetaC_eq`) also assume `∀ β, 0 ≤ m*(β)`, which is proved only for
`β ≥ 0` (`IsingFK.magnetization_nonneg`); they are not tested here. Their unconditional
replacements are tested in `FKRepresentation.PcUpperAllDimensions`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.HisingBoxClose

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.IsingFK _root_.StatMech.FK

-- The finite-volume identity in `Λ_1 ⊆ ℤ²` at `β = 1`.
example : fvMagnetization 2 1 1 =
    esWiredOnePoint (boxGraph 2 2) (boxBoundary 2 2) (0 : Fin 2) (pOfBeta 1) (boxOrigin 2 2) :=
  hbx_hisingBox 2 1 one_pos 1 le_rfl

-- `m*(1) = θ_FK(pOfBeta 1)` on `ℤ²`, with `hisingBox` discharged.
example (hp : 0 < pOfBeta 1) (hp1 : pOfBeta 1 < 1) :
    magnetization 2 1 = FK.fkTheta 2 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) :=
  mfc_magPercoId 2 (by norm_num) (hbx_hisingBox 2) 1 one_pos hp hp1

-- Consequence: `m*(1) ≥ 0` on `ℤ²` from the FK representation.
example : 0 ≤ magnetization 2 1 := by
  have hp : 0 < pOfBeta 1 := Ising.pOfBeta_pos one_pos
  have hp1 : pOfBeta 1 < 1 := Ising.pOfBeta_lt_one 1
  rw [mfc_magPercoId 2 (by norm_num) (hbx_hisingBox 2) 1 one_pos hp hp1]
  exact FK.fkTheta_nonneg 2 hp hp1 _

end PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.HisingBoxClose
