/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.MagnetizationFK

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.MagnetizationFK`

* `magnetization_nonneg` at `β = 0` and `β = 1/2` in `d = 3`, and at `β = 2` in `d = 2`; together
  with `abs_magnetization_le_one` this places `m*(β)` in `[0, 1]`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.MagnetizationFK

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.IsingFK

-- At infinite temperature the spontaneous magnetization of `ℤ³` is nonnegative.
example : 0 ≤ magnetization 3 0 := magnetization_nonneg 3 le_rfl

-- At `β = 1/2` the spontaneous magnetization of `ℤ³` is nonnegative.
example : 0 ≤ magnetization 3 (1 / 2) := magnetization_nonneg 3 (by norm_num)

-- At `β = 2` the spontaneous magnetization of `ℤ²` lies in `[0, 1]`.
example : magnetization 2 2 ∈ Set.Icc 0 1 :=
  ⟨magnetization_nonneg 2 (by norm_num), (abs_le.mp (abs_magnetization_le_one 2 2)).2⟩

end PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.MagnetizationFK
