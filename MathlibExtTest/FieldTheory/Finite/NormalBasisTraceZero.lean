/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import MathlibExt.FieldTheory.Finite.NormalBasisTraceZero

open MetaMathlibExt

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

-- In degree one, the single coefficient detects trace zero over the base field itself.
example (a : ZMod 2) : a = 0 ↔ Algebra.trace (ZMod 2) (ZMod 2) (a • 1) = 0 := by
  have hβ : LinearIndependent (ZMod 2)
      (fun i : Fin 1 => (1 : ZMod 2) ^ (Fintype.card (ZMod 2) ^ (i : ℕ))) := by
    rw [linearIndependent_unique_iff]
    simp
  simpa only [Fin.sum_univ_one, Fin.val_zero, pow_zero, pow_one] using
    normalBasisMap_sum_eq_zero_iff_trace (ZMod 2) (ZMod 2) 1
      (Module.finrank_self (ZMod 2)) 1 hβ (fun _ ↦ a)

-- In characteristic two, the all-ones tuple in degree two has zero sum,
-- but the first basis vector alone still has nonzero trace.
example {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K]
    (hn : Module.finrank (ZMod 2) K = 2) (β : K)
    (hβ : LinearIndependent (ZMod 2) (fun i : Fin 2 => β ^ (Fintype.card (ZMod 2) ^ (i : ℕ)))) :
    Algebra.trace (ZMod 2) K (β + β ^ Fintype.card (ZMod 2)) = 0 ∧
      Algebra.trace (ZMod 2) K β ≠ 0 := by
  have h := normalBasisMap_sum_eq_zero_iff_trace (ZMod 2) K 2 hn β hβ
  constructor
  · have hsum : (![(1 : ZMod 2), 1] : Fin 2 → ZMod 2) 0 + ![(1 : ZMod 2), 1] 1 = 0 := by
      decide
    simpa [Fin.sum_univ_two] using (h ![1, 1]).mp (by simpa [Fin.sum_univ_two] using hsum)
  · simpa [Fin.sum_univ_two] using (h ![1, 0]).not.mp (by simp [Fin.sum_univ_two])
