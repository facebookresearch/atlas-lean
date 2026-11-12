/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.MagNonneg
public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.MagnetizationFK

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.MagNonneg`

* The hypothesis of `magnetization_nonneg_of_fv` (nonnegative finite-volume magnetization in every
  plus box) is satisfiable: `IsingFK.fv_integral_origin_nonneg` proves it for every `β ≥ 0`, so
  the lemma yields `0 ≤ m*(β)` on `ℤ²` at `β = 1`.
* Combined with `magnetization_le_one`: `m*(β) ∈ [0, 1]` for every `d` and every `β ≥ 0`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.MagNonneg

open MeasureTheory
open _root_.StatMech _root_.StatMech.Ising

-- The box hypothesis holds at `β = 1`, so `magnetization_nonneg_of_fv` gives `0 ≤ m*(1)` on `ℤ²`.
example : 0 ≤ magnetization 2 1 :=
  magnetization_nonneg_of_fv 2 1 (fun n => IsingFK.fv_integral_origin_nonneg 2 zero_le_one n)

-- Together with `magnetization_le_one`, the magnetization lies in `[0, 1]` for `β ≥ 0`.
example (d : ℕ) (β : ℝ) (hβ : 0 ≤ β) : magnetization d β ∈ Set.Icc 0 1 :=
  ⟨magnetization_nonneg_of_fv d β (fun n => IsingFK.fv_integral_origin_nonneg d hβ n),
    magnetization_le_one d β⟩

end PhyslibExtTest.CondensedMatter.IsingModel.MagNonneg
