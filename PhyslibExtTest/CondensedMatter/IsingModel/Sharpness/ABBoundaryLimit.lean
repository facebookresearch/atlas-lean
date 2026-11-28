/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABBoundaryLimit

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABBoundaryLimit`

* `abbl_abfaMag_le_abbMag_le` for the box `Λ_1 ⊂ ℤ²` at `β = h = 1`, and its upper half as an
  explicit error bound `e^{-2}`;
* `abbl_tendsto_abbMag_shifted` on `ℤ²` at `β = h = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABBoundaryLimit

open _root_.StatMech _root_.StatMech.Sharpness _root_.StatMech.Lattice

-- The two box magnetizations are within `e^{-2}` of each other on `Λ_1 ⊂ ℤ²`.
example : abfaMag (sctBoxGraph 2 1) (abbCoupling 2 1) (sctBoxOrigin 2 1) 1 1 ≤ abbMag 2 1 1 1 ∧
    abbMag 2 1 1 1 ≤
      abfaMag (sctBoxGraph 2 1) (abbCoupling 2 1) (sctBoxOrigin 2 1) 1 1 + Real.exp (-2) := by
  have h := abbl_abfaMag_le_abbMag_le (d := 2) (n := 1) one_pos 1 1 zero_le_one zero_le_one
  norm_num at h ⊢
  exact h

-- The boundary-target magnetization converges to the magnetization of `ℤ²` with a ghost.
example : Filter.Tendsto (fun n => abbMag 2 (n + 1) 1 1) Filter.atTop
    (nhds (abigMag (hypercubicLattice 2) (abblLatticeCoupling 2) 0 1 1)) :=
  abbl_tendsto_abbMag_shifted 2 1 1 zero_le_one one_pos

-- The limit is the same as the limit of the box magnetizations along any shift.
example (d : ℕ) (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 < h) :
    Filter.Tendsto (fun n => abbMag d (n + 1 + 1) β h) Filter.atTop
      (nhds (abigMag (hypercubicLattice d) (abblLatticeCoupling d) 0 β h)) :=
  (abbl_tendsto_abbMag_shifted d β h hβ hh).comp (Filter.tendsto_add_atTop_nat 1)

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABBoundaryLimit
