/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.NumericalLinearAlgebra.CommunicationLowerBound

@[expose] public section

open Finset MathlibExt.Combinatorics.LoomisWhitney
  Cslib.Algorithms.NumericalLinearAlgebra.CommunicationLowerBound

namespace CSLibExtTest.Algorithms.NumericalLinearAlgebra.CommunicationLowerBound

/-- The hypotheses are jointly satisfiable: `2 × 2` times `2 × 2` matrix multiplication done in
a single segment with a fast memory of `M = 1` word (each projection has `4 ≤ 4M` elements),
moving `W = 0` words; the bound reads `8 / 8 - 1 = 0 ≤ 0`. -/
example : ((2 * 2 * 2 : ℕ) : ℝ) / (8 * √((1 : ℕ) : ℝ)) - (1 : ℕ) ≤ (0 : ℕ) :=
  matmul_card_div_sub_le_words (n := 2) (m := 2) (r := 2) (s := 1) (fun _ => univ) 1 0
    (fun p => ⟨0, mem_univ p⟩) (fun _ => by decide) (fun _ => by decide) (fun _ => by decide)
    (by norm_num)

/-- A segment using at most `4M` operands of each kind performs at most `8 M √M` evaluations:
the cube `{0,1}³` with `M = 1` attains `8 = 8 · 1 · √1`. -/
example : ((univ : Finset (Fin 2 × Fin 2 × Fin 2)).card : ℝ) ≤ 8 * (1 : ℕ) * √((1 : ℕ) : ℝ) :=
  card_le_of_card_image_le _ 1 (by decide) (by decide) (by decide)

/-- With `M = 0` no operand fits, so a segment evaluates nothing. -/
example (E : Finset (ℕ × ℕ × ℕ)) (hA : (E.image projXZ).card ≤ 4 * 0)
    (hB : (E.image projYZ).card ≤ 4 * 0) (hC : (E.image projXY).card ≤ 4 * 0) : E.card = 0 := by
  have := card_le_of_card_image_le E 0 hA hB hC
  simpa using this

/-- The `2 × 2 × 2` block of index triples numbered `t`, for `4 × 4` matrices. -/
def block (t : Fin 8) : Finset (Fin 4 × Fin 4 × Fin 4) :=
  univ.filter fun p =>
    p.1.val / 2 = t.val / 4 ∧ p.2.1.val / 2 = t.val / 2 % 2 ∧ p.2.2.val / 2 = t.val % 2

/-- A nondegenerate instance: `4 × 4` times `4 × 4` matrix multiplication with `M = 4` cut into
`8` segments, each a `2 × 2 × 2` block of index triples (`4 ≤ 16` operands of each kind),
moving `W = 4 · 7 = 28` words; the bound gives `64 / 16 - 4 = 0 ≤ 28`. -/
example : ((4 * 4 * 4 : ℕ) : ℝ) / (8 * √((4 : ℕ) : ℝ)) - (4 : ℕ) ≤ (28 : ℕ) :=
  matmul_card_div_sub_le_words block 4 28 (by decide) (by decide) (by decide) (by decide)
    (by norm_num)

/-- The triples of `2 × 2` matrix multiplication with inner index `k = q`. -/
def half (q : Fin 2) : Finset (Fin 2 × Fin 2 × Fin 2) := univ.filter fun p => p.2.2 = q

/-- The parallel hypotheses are satisfiable: two processors split `2 × 2` matrix multiplication by
the inner index, each in one segment with `M = 1`; some processor moves at least
`8 / (2 · 8) - 1 < 0` words. -/
example : ∃ q : Fin 2, ((univ : Finset (Fin 2 × Fin 2 × Fin 2)).card : ℝ) /
    ((2 : ℕ) * (8 * √((1 : ℕ) : ℝ))) - (1 : ℕ) ≤ (fun _ : Fin 2 => (0 : ℕ)) q :=
  exists_card_div_sub_le_words_of_parallel univ (P := 2) (by norm_num) half (by decide)
    (fun _ => 1) (fun q _ => half q) 1 (fun _ => 0) (fun q => by decide +revert)
    (fun q _ => by decide +revert) (fun q _ => by decide +revert) (fun q _ => by decide +revert)
    (fun _ => by norm_num)

/-- The singleton segment `{t}` of `3 × 3` matrix multiplication, for `t < 27`. -/
def singleton (t : Fin 27) : Finset (Fin 3 × Fin 3 × Fin 3) :=
  {(⟨t / 9, by omega⟩, ⟨t / 3 % 3, by omega⟩, ⟨t % 3, by omega⟩)}

/-- A strictly positive bound: `3 × 3` matrix multiplication with `M = 1`, one evaluation per
segment (27 segments), so at least `M (27 - 1) = 26` words move; the bound gives
`27 / 8 - 1 = 19/8 > 0`. -/
example : ((3 * 3 * 3 : ℕ) : ℝ) / (8 * √((1 : ℕ) : ℝ)) - (1 : ℕ) ≤ (26 : ℕ) ∧
    (0 : ℝ) < ((3 * 3 * 3 : ℕ) : ℝ) / (8 * √((1 : ℕ) : ℝ)) - (1 : ℕ) := by
  refine ⟨matmul_card_div_sub_le_words singleton 1 26 (by decide) (fun t => ?_) (fun t => ?_)
    (fun t => ?_) (by norm_num), by norm_num⟩ <;>
  · refine card_image_le.trans ?_
    simp [singleton]

end CSLibExtTest.Algorithms.NumericalLinearAlgebra.CommunicationLowerBound
