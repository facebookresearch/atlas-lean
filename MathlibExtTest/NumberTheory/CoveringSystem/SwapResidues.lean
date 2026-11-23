/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.Simproc.Factors
import MathlibExt.NumberTheory.CoveringSystem.SwapResidues

/-! # Tests for swapping residues in a covering system -/

-- Swap 0 and 2 modulo 3 using a negative shift. The class of even integers and the
-- class 1 mod 6 stay fixed. The moduli 6 and 18 distinguish the two swapped families.
example : Int.IsCoveringSystem {(0, 2), (1, 6), (-13, 6), (21, 18), (27, 18), (33, 18)} := by
  let C : Finset (ℤ × ℕ) := {(0, 2), (1, 6), (3, 6), (5, 18), (11, 18), (17, 18)}
  have hC : Int.IsCoveringSystem C := by
    intro z
    simp [C, Int.ModEq]
    omega
  have hf : (18 : ℕ).primeFactorsList = [2, 3, 3] := by simp
  have h := MetaMathlibExt.isCoveringSystem_swap_residues_mod_prime C hC (by decide)
    (L := 18) (p := 3) (by decide) (by decide) (by decide)
    (a₁ := 0) (a₂ := 2) (by decide) (by decide) (-16) (by
      rw [← Nat.primeFactorsList_count_eq, hf]
      decide) (by
      intro q hq hqL hq₃
      have hmem := (Nat.mem_primeFactorsList (by decide : 18 ≠ 0)).mpr ⟨hq, hqL⟩
      rw [hf] at hmem
      have : q = 2 := by simpa [hq₃] using hmem
      subst q
      rw [← Nat.primeFactorsList_count_eq, hf]
      decide)
  convert h using 1
  decide
