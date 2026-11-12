/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.QuasilinearDemand
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Tests for quasilinear demand

Interior case: prices `(1, 1)`, wealth `3`, demand `(1, 2)` with utility `4`. Corner case: prices
`(1, 2)`, wealth `1`, demand `(1, 0)`. Both are instances of the main theorem.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Consumer.QuasilinearDemand

open Matrix MathlibExt.Economics.Consumer

example : quasilinearSqrtDemand ![1, 1] 3 = ![1, 2] := by
  unfold quasilinearSqrtDemand
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs with hcond
  · funext i
    fin_cases i
    · norm_num
    · norm_num
  · norm_num at hcond

example : quasilinearSqrt ![1, 2] = 4 := by
  simp only [quasilinearSqrt, Matrix.cons_val_zero, Matrix.cons_val_one, Real.sqrt_one]
  norm_num

example : quasilinearSqrtDemand ![1, 2] 1 = ![1, 0] := by
  unfold quasilinearSqrtDemand
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs with hcond
  · norm_num at hcond
  · funext i
    fin_cases i
    · norm_num
    · norm_num

example : IsMarshallianDemand quasilinearSqrt twoGoodSet ![1, 1] 3 ![1, 2] := by
  have hp : ∀ i : Fin 2, 0 < (![1, 1] : Fin 2 → ℝ) i := by
    rw [Fin.forall_fin_two]
    constructor
    · simp only [Matrix.cons_val_zero]; norm_num
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; norm_num
  have h := isMarshallianDemand_quasilinearSqrt (p := ![1, 1]) (w := 3) hp (by norm_num)
  have heq : quasilinearSqrtDemand ![1, 1] 3 = ![1, 2] := by
    unfold quasilinearSqrtDemand
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    split_ifs with hcond
    · funext i
      fin_cases i
      · norm_num
      · norm_num
    · norm_num at hcond
  rwa [heq] at h

example : IsMarshallianDemand quasilinearSqrt twoGoodSet ![1, 2] 1 ![1, 0] := by
  have hp : ∀ i : Fin 2, 0 < (![1, 2] : Fin 2 → ℝ) i := by
    rw [Fin.forall_fin_two]
    constructor
    · simp only [Matrix.cons_val_zero]; norm_num
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; norm_num
  have h := isMarshallianDemand_quasilinearSqrt (p := ![1, 2]) (w := 1) hp (by norm_num)
  have heq : quasilinearSqrtDemand ![1, 2] 1 = ![1, 0] := by
    unfold quasilinearSqrtDemand
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    split_ifs with hcond
    · norm_num at hcond
    · funext i
      fin_cases i
      · norm_num
      · norm_num
  rwa [heq] at h

#print axioms isMarshallianDemand_quasilinearSqrt

end MathlibExtTest.Economics.Consumer.QuasilinearDemand
