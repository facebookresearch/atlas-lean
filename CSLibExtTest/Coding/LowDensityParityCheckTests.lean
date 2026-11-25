/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.LowDensityParityCheck

@[expose] public section

/-!
# Tests for low-density parity-check codes

Gallager's Figure 2.1 has `n = 20`, `j = 3`, `k = 4`, so `m = 5` rows per block: it is an instance
of `gallagerMatrix 5 3 4 σ`, regular with `15` rows, and every such code has rate at least
`1 - 3/4 = 1/4`. A small `2 × 2` matrix shows that regularity is a real constraint.
-/

namespace CSLibExtTest.Coding.LowDensityParityCheck

open Cslib.CodingTheory Cslib.CodingTheory.LDPC LinearCode Module

/-- Gallager's matrices with the parameters of his Figure 2.1 are `(20, 3, 4)`-regular. -/
example (σ : Fin 3 → Equiv.Perm (Fin (5 * 4))) : IsRegular (gallagerMatrix 5 3 4 σ) 3 4 :=
  isRegular_gallagerMatrix 5 3 4 σ

/-- Double counting: `15 · 4 = 20 · 3`. -/
example (σ : Fin 3 → Equiv.Perm (Fin (5 * 4))) :
    Fintype.card (Fin 3 × Fin 5) * 4 = Fintype.card (Fin (5 * 4)) * 3 :=
  card_rows_mul_eq (isRegular_gallagerMatrix 5 3 4 σ)

/-- Every code of the `(20, 3, 4)` ensemble has rate at least `1/4`. -/
example (σ : Fin 3 → Equiv.Perm (Fin (5 * 4))) :
    1 - (3 : ℝ) / 4 ≤ finrank (ZMod 2) (ofParityCheck (gallagerMatrix 5 3 4 σ)) / (5 * 4 : ℕ) :=
  one_sub_div_le_rate_gallagerMatrix (by norm_num) (by norm_num) σ

/-- In block `0` (no permutation), row `r` has its ones on columns `4r, …, 4r + 3`. -/
example (σ : Fin 3 → Equiv.Perm (Fin (5 * 4))) :
    gallagerMatrix 5 3 4 σ (0, 1) 5 = 1 ∧ gallagerMatrix 5 3 4 σ (0, 1) 8 = 0 := by
  simp [gallagerMatrix, blockPerm]

/-- The `2 × 2` identity matrix over `ZMod 2` is `(1, 1)`-regular. -/
example : IsRegular (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 1 := by
  unfold LDPC.IsRegular colWeight rowWeight
  decide

/-- The all-ones `2 × 2` matrix is `(2, 2)`-regular but not `(1, 1)`-regular. -/
example : IsRegular (Matrix.of fun _ _ => (1 : ZMod 2) : Matrix (Fin 2) (Fin 2) (ZMod 2)) 2 2 ∧
    ¬IsRegular (Matrix.of fun _ _ => (1 : ZMod 2) : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 1 := by
  unfold LDPC.IsRegular colWeight rowWeight
  decide

end CSLibExtTest.Coding.LowDensityParityCheck
