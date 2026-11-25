/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Fourier.FFT.Cost
public import CSLibExt.Algorithms.Lean.DivideAndConquer.Karatsuba
public import CSLibExt.Algorithms.Lean.Matrix.Strassen.Correctness
public import CSLibExt.Algorithms.Lean.Matrix.Strassen.Costs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Algebraic divide-and-conquer cost audit

Value and cost results for Karatsuba multiplication, the radix-two FFT and Strassen's matrix
accumulator, each in its provider's charged model. Every cost here is a total charge, summed over
all recursive calls.

Karatsuba's results are cited from the imported `Karatsuba` module, not restated:
`karatsuba_ret` gives the value `x * y`, and `karatsuba_time_le_rpow` bounds the declared total
charge by `9 * n ^ logb 2 3` for `n ≥ 1`. That charge, `karatsubaCost n`, adds `1` for each call
with `n ≤ 1` and `n` for each call with `n ≥ 2`; it is an accounting convention, not a count of
digit operations.

Not supplied here: a bound on Karatsuba's digit operations, and an FFT count of ring operations
alone (the FFT charge also counts array reads and writes).
-/

universe u

namespace Cslib.Algorithms.Lean.AlgebraicCostAudit

open Cslib.Algorithms.Lean.TimeM Cslib.Algorithms.Lean.Matrix

/-- **Charge bound for the radix-two FFT.** Let $R$ be a commutative ring. For every natural
number $d$, every $\omega \in R$ and every vector $x \in R^{2^d}$, the total charge of the
radix-two FFT of $x$ with root $\omega$, summed over all its recursive calls, is at most
$(7d + 1) \cdot 2^d$.

The charge counts scalar ring operations and array element reads and writes. -/
theorem fft_charge_le {R : Type*} [CommRing R] (d : ℕ) (ω : R)
    (xs : Vector R (2 ^ d)) :
    (fft d ω xs).time ≤ (7 * d + 1) * 2 ^ d := by
  have h := fft_time_add_one d ω xs; rw [← h]; exact Nat.le_succ _

/-- **Multiplication count of Strassen's accumulator.** Let $R$ be a type with a zero, an
addition, a subtraction and a multiplication. For every $k \ge 0$ and all $n \times n$ matrices
$A$, $B$, $C$ over $R$ with $n = 2^k$, Strassen's accumulator on $A$, $B$, $C$ performs exactly
$n^{\log_2 7}$ scalar multiplications, summed over all its recursive calls. -/
theorem strassen_mul_count {R : Type u} [Zero R] [Add R] [Sub R] [Mul R]
    (k : ℕ) (A B C : Vector (Vector R (2 ^ k)) (2 ^ k)) :
    ((strassenMatrixAccumulate k A B C).time.1 : ℝ) =
      ((2 ^ k : ℕ) : ℝ) ^ Real.logb 2 7 := by
  have ht := strassenMatrixAccumulate_time k A B C
  have h1 : (strassenMatrixAccumulate k A B C).time.1 = 7 ^ k := congrArg Prod.fst ht
  rw [h1, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat]
  have e1 : ((2 : ℝ) ^ k) = (2 : ℝ) ^ ((k : ℕ) : ℝ) := (Real.rpow_natCast 2 k).symm
  have h7 : (7 : ℝ) = (2 : ℝ) ^ Real.logb 2 7 :=
    (Real.rpow_logb (b := 2) (x := 7) (by norm_num) (by norm_num) (by norm_num)).symm
  rw [e1]
  conv_lhs => rw [h7]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (x := 2) (by norm_num),
    ← Real.rpow_mul (x := 2) (by norm_num), mul_comm (Real.logb 2 7) ((k : ℕ) : ℝ)]

/-- **Bound on the scalar operations of Strassen's accumulator.** Let $R$ be a type with a zero,
an addition, a subtraction and a multiplication. For every $k \ge 0$ and all $n \times n$
matrices $A$, $B$, $C$ over $R$ with $n = 2^k$, the total number of scalar multiplications,
additions and subtractions that Strassen's accumulator performs on $A$, $B$, $C$, summed over all
its recursive calls, is at most $\frac{28}{3}\, n^{\log_2 7}$. -/
theorem strassen_ops_le {R : Type u} [Zero R] [Add R] [Sub R] [Mul R]
    (k : ℕ) (A B C : Vector (Vector R (2 ^ k)) (2 ^ k)) :
    ((((strassenMatrixAccumulate k A B C).time.1 +
      (strassenMatrixAccumulate k A B C).time.2 : ℕ)) : ℝ) ≤
      (28 / 3) * ((2 ^ k : ℕ) : ℝ) ^ Real.logb 2 7 := by
  have hS1 := strassen_mul_count k A B C
  have ht := strassenMatrixAccumulate_time k A B C
  have h1 : (strassenMatrixAccumulate k A B C).time.1 = 7 ^ k := congrArg Prod.fst ht
  have h2 : (strassenMatrixAccumulate k A B C).time.2 =
      (25 * 7 ^ k - 22 * 4 ^ k) / 3 :=
    congrArg Prod.snd ht
  have hcast : ((7 ^ k : ℕ) : ℝ) = ((2 ^ k : ℕ) : ℝ) ^ Real.logb 2 7 := by
    rw [← h1]; exact hS1
  have hdiv : ((((25 * 7 ^ k - 22 * 4 ^ k) / 3 : ℕ)) : ℝ) ≤
      ((((25 * 7 ^ k - 22 * 4 ^ k : ℕ))) : ℝ) / 3 :=
    Nat.cast_div_le
  have hsub : ((((25 * 7 ^ k - 22 * 4 ^ k : ℕ))) : ℝ) ≤ ((25 * 7 ^ k : ℕ) : ℝ) :=
    by exact_mod_cast Nat.sub_le _ _
  have hmul : ((25 * 7 ^ k : ℕ) : ℝ) = 25 * ((7 ^ k : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
  rw [h1, h2, Nat.cast_add, hcast]
  rw [hmul, hcast] at hsub
  have h3 : ((((25 * 7 ^ k - 22 * 4 ^ k) / 3 : ℕ)) : ℝ) ≤
      25 / 3 * (((2 ^ k : ℕ) : ℝ) ^ Real.logb 2 7) := by
    linarith [hdiv, hsub]
  linarith [h3]

theorem strassen_value {R : Type u} [NonUnitalNonAssocRing R]
    (k : ℕ) (A B : Vector (Vector R (2 ^ k)) (2 ^ k)) :
    (Matrix.of fun i j =>
      (((strassenMatrixAccumulate k A B 0).ret.get i).get j)) =
      (Matrix.of fun i j => (A.get i).get j) *
        (Matrix.of fun i j => (B.get i).get j) := by
  have h := strassenMatrixAccumulate_ret k A B 0
  have hz : (Matrix.of fun i j =>
      (((0 : Vector (Vector R (2 ^ k)) (2 ^ k)).get i).get j)) = 0 := by
    ext i j
    change (((0 : Vector (Vector R (2 ^ k)) (2 ^ k))[i.1]'(i.2))[j.1]'(j.2) = (0 : R))
    rw [Vector.getElem_zero, Vector.getElem_zero]
  simpa [hz] using h

end Cslib.Algorithms.Lean.AlgebraicCostAudit
