/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.Algebraic.BilinearRecursion

/-!
# Gate counts for recursive bilinear matrix-multiplication circuits

Exact sizes of the block encoder and decoder, the one-step size recurrence
for `recursiveCircuit`, its closed form, and an upper-bound invariant. The
charged primitive is the gate (`add`/`mul` nodes); constants and input
references are free, and a linear combination is charged per
(output, source) pair even at zero coefficients, so the counts are exact
for the construction as written.
-/

set_option autoImplicit false

universe u

namespace Cslib.Complexity.Algebraic

@[expose] public section

/-- **Size of the block encoder.** One linear combination over all terms and both
input blocks, charged per (output, source) pair. -/
theorem blockEncoder_size {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ) :
    (blockEncoder terms k).size = 4 * terms.length * q ^ (2 * (k + 1)) := by
  have hpow : q ^ (2 * (k + 1)) = (q ^ k * q ^ k) * q ^ 2 := by
    rw [show 2 * (k + 1) = (k + k) + 2 by ring, pow_add, pow_add]
  simp only [blockEncoder, ArithmeticCircuit.size_linearCombination,
    MatrixMultiplicationExponent.MatrixCoordinate, Fintype.card_prod, Fintype.card_sum,
    Fintype.card_fin]
  rw [hpow]
  ring

/-- **Size of the block decoder.** One linear combination reassembling every output
block from the per-term results. -/
theorem blockDecoder_size {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ) :
    (blockDecoder terms k).size = 2 * terms.length * q ^ (2 * (k + 1)) := by
  have hpow : q ^ (2 * (k + 1)) = q ^ (k + 1) * q ^ (k + 1) := by
    rw [show 2 * (k + 1) = (k + 1) + (k + 1) by ring, pow_add]
  simp only [blockDecoder, ArithmeticCircuit.size_linearCombination,
    Fintype.card_prod, Fintype.card_fin]
  rw [hpow]
  ring

/-- **Base case of the size recurrence.** The level-zero circuit is the one-gate
outer-product circuit. -/
@[simp] theorem recursiveCircuit_size_zero {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) :
    (recursiveCircuit terms 0).size = 1 := by
  simp only [recursiveCircuit, outerMatrixCircuit_size, mul_one]

/-- **One-step size recurrence.** Each level adds one recursive copy per term plus
the encoder and decoder sizes. -/
theorem recursiveCircuit_size_succ {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ) :
    (recursiveCircuit terms (k + 1)).size =
      terms.length * (recursiveCircuit terms k).size +
        6 * terms.length * q ^ (2 * (k + 1)) := by
  simp only [recursiveCircuit, ArithmeticCircuit.size_subst, ArithmeticCircuit.size_parallel,
    blockEncoder_size, blockDecoder_size]
  ring

/-- **Closed form of the size recurrence.** Multiplying the recurrence solution
through by `terms.length - q ^ 2` clears the division. -/
theorem recursiveCircuit_size_closed {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q))) (k : ℕ) :
    ((terms.length : ℤ) - (q : ℤ) ^ 2) * (recursiveCircuit terms k).size +
        6 * terms.length * (q : ℤ) ^ 2 * (q : ℤ) ^ (2 * k) =
      ((terms.length : ℤ) - (q : ℤ) ^ 2 + 6 * terms.length * (q : ℤ) ^ 2) *
        (terms.length : ℤ) ^ k := by
  induction k with
  | zero =>
    simp [recursiveCircuit_size_zero]
  | succ k ih =>
    have hrecZ : ((recursiveCircuit terms (k + 1)).size : ℤ)
        = (terms.length : ℤ) * ((recursiveCircuit terms k).size : ℤ)
          + 6 * (terms.length : ℤ) * (q : ℤ) ^ (2 * (k + 1)) := by
      exact_mod_cast recursiveCircuit_size_succ terms k
    have hpow : (q : ℤ) ^ (2 * (k + 1)) = (q : ℤ) ^ (2 * k) * (q : ℤ) ^ 2 := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    rw [hrecZ, hpow, pow_succ]
    linear_combination (terms.length : ℤ) * ih

/-- **Upper-bound invariant for the size.** With at most `r` terms per level and
`q ^ 2 < r`, the size plus the scaled geometric term stays below the pure
exponential. -/
theorem recursiveCircuit_size_le {F : Type u} [Field F] {q : ℕ}
    (terms : List (MatrixMultiplicationExponent.RankOneTrilinearTerm F
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)
      (MatrixMultiplicationExponent.MatrixCoordinate q q)))
    {r : ℕ} (hlen : terms.length ≤ r) (hqr : q ^ 2 < r) (k : ℕ) :
    (recursiveCircuit terms k).size + 6 * r * q ^ 2 * q ^ (2 * k) ≤
      (1 + 6 * r * q ^ 2) * r ^ k := by
  induction k with
  | zero =>
    simp [recursiveCircuit_size_zero]
  | succ k ih =>
    have hQ1 : q ^ 2 + 1 ≤ r := hqr
    have hpow : q ^ (2 * (k + 1)) = q ^ (2 * k) * q ^ 2 := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    have hLr2 : terms.length + r * q ^ 2 ≤ r * r := by
      calc terms.length + r * q ^ 2 ≤ r + r * q ^ 2 := add_le_add_left hlen _
        _ = r * (q ^ 2 + 1) := by ring
        _ ≤ r * r := mul_le_mul_right hQ1 _
    have hrec := recursiveCircuit_size_succ terms k
    have hrpow : r ^ (k + 1) = r ^ k * r := by rw [pow_succ]
    rw [hrec, hpow, hrpow]
    nlinarith [mul_le_mul_right ih r, mul_le_mul_right hlen ((recursiveCircuit terms k).size),
      mul_le_mul_right hLr2 (6 * q ^ (2 * k) * q ^ 2)]

end

end Cslib.Complexity.Algebraic
