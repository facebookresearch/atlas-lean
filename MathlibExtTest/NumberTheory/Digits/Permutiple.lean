/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.Permutiple
import Mathlib.GroupTheory.Perm.Cycle.Concrete

open MetaMathlibExt

-- Rearranging 87912 to 78912 = 4 * 19728 gives residue 3 at the digit 1.
example : ((1 : ℤ) + 6 * 2) % 10 ≤ 3 := by
  let d : Fin 5 → ℕ := ![2, 1, 9, 7, 8]
  let π : Equiv.Perm (Fin 5) := Equiv.swap 3 4
  let τ : Equiv.Perm (Fin 5) := c[0, 3, 2, 4, 1]
  have hq : IsPermutiple 4 10 (d ∘ π) τ := by
    unfold IsPermutiple
    decide +revert
  exact permutiple_basePerm_residue_le 4 10 (by decide) (by decide)
    d Fin.revPerm π τ isPermutiple_87912 hq 1

-- In base two, 1001 = 3 * 0011 gives a negative integer before reduction modulo two.
example : (-1 : ℤ) % 2 ≤ 2 := by
  let d : Fin 4 → ℕ := ![1, 0, 0, 1]
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 1 3
  have hp : IsPermutiple 3 2 d σ := by
    unfold IsPermutiple
    decide +revert
  exact permutiple_basePerm_residue_le 3 2 (by decide) (by decide) d σ 1 σ hp hp 1
