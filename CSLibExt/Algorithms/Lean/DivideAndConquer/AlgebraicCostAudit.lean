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
Adapter audit restating FFT, Karatsuba, Strassen cost theorems.
Gates: Karatsuba digit-operation bound and ring-only FFT count
are not supplied here.
-/

universe u

namespace Cslib.Algorithms.Lean.AlgebraicCostAudit

open Cslib.Algorithms.Lean.TimeM Cslib.Algorithms.Lean.Matrix

theorem karatsuba_value (B n x y : ℕ) :
    (karatsuba B n x y).ret = x * y :=
  karatsuba_ret B n x y

/-- Bounded quantity is the module's declared per-call charge,
not a count of digit operations. -/
theorem karatsuba_declaredCharge_le (B : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (x y : ℕ) :
    ((karatsuba B n x y).time : ℝ) ≤ 9 * (n : ℝ) ^ Real.logb 2 3 :=
  karatsuba_time_le_rpow B hn x y

/-- Charge counts scalar ring operations and array element reads/writes. -/
theorem fft_charge_le {R : Type*} [CommRing R] (d : ℕ) (ω : R)
    (xs : Vector R (2 ^ d)) :
    (fft d ω xs).time ≤ (7 * d + 1) * 2 ^ d := by
  have h := fft_time_add_one d ω xs; rw [← h]; exact Nat.le_succ _

/-- Bounded first component counts scalar multiplications. -/
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

/-- Bounded sum counts scalar multiplications and scalar additions/subtractions. -/
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
