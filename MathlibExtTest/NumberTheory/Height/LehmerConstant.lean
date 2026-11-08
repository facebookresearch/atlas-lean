/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.LehmerConstant

/-!
# Lehmer constant public-API and boundary checks

Exact-statement exercises for the integer Mahler measure, its values on
linear factors, multiplicativity, and the proved elementary bounds
`1 ≤ L ≤ 2` for Lehmer's constant together with the equivalence between
`L = 1` and Lehmer's question.
-/

@[expose] public section

namespace LehmerConstantTest

open Polynomial MathlibExt.NumberTheory.LehmerConstant

/-- Every nonzero integer polynomial has Mahler measure at least `1`. -/
example {f : Polynomial ℤ} (hf : f ≠ 0) : 1 ≤ intMahlerMeasure f :=
  one_le_intMahlerMeasure hf

/-- `M(X) = 1`. -/
example : intMahlerMeasure (X : Polynomial ℤ) = 1 :=
  intMahlerMeasure_X

/-- `M(X - 1) = 1`: the boundary value excluded from the infimum. -/
example : intMahlerMeasure (X - C (1 : ℤ)) = 1 :=
  intMahlerMeasure_X_sub_one

/-- `M(X - 2) = 2`. -/
example : intMahlerMeasure (X - C (2 : ℤ)) = 2 :=
  intMahlerMeasure_X_sub_two

/-- `M(C (-3)) = 3`. -/
example : intMahlerMeasure (C (-3 : ℤ)) = 3 := by
  rw [intMahlerMeasure_C]
  norm_num

/-- Multiplicativity on a concrete product: `M((X - 2)^2) = 4`. -/
example : intMahlerMeasure ((X - C (2 : ℤ)) * (X - C (2 : ℤ))) = 4 := by
  rw [intMahlerMeasure_mul, intMahlerMeasure_X_sub_two]
  norm_num

/-- The defining set is nonempty, with member `2`. -/
example : (2 : ℝ) ∈ mahlerMeasuresAboveOne :=
  ⟨X - C (2 : ℤ), by rw [intMahlerMeasure_X_sub_two]; norm_num,
    intMahlerMeasure_X_sub_two.symm⟩

/-- Proved elementary bounds `1 ≤ L ≤ 2`. -/
example : 1 ≤ lehmerConstant ∧ lehmerConstant ≤ 2 :=
  ⟨one_le_lehmerConstant, lehmerConstant_le_two⟩

/-- Any integer polynomial with Mahler measure in `(1, 3/2)` would bound
Lehmer's constant by `3/2`. -/
example {f : Polynomial ℤ} (h1 : 1 < intMahlerMeasure f)
    (h2 : intMahlerMeasure f < 3 / 2) : lehmerConstant < 3 / 2 :=
  lt_of_le_of_lt (lehmerConstant_le_intMahlerMeasure h1) h2

/-- Lehmer's constant equals `1` iff Lehmer's question has a positive
answer. -/
example : lehmerConstant = 1 ↔ LehmerQuestion :=
  lehmerConstant_eq_one_iff

/-- The constant polynomial `1` is reciprocal. -/
example : IsReciprocal (1 : Polynomial ℤ) :=
  isReciprocal_one

end LehmerConstantTest
