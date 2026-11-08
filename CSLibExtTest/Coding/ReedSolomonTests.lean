/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.ReedSolomon
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # Tests for Reed-Solomon codes and Berlekamp-Welch decoding

The running example is `RS(6, 2)` over `F₇` with evaluation points `1, …, 6`: minimum distance
`6 - 2 + 1 = 5`, so Berlekamp-Welch corrects `⌊(6 - 2)/2⌋ = 2` errors.
-/

namespace Cslib.CodingTheory.ReedSolomonTests

open Polynomial Cslib.CodingTheory ReedSolomon

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The evaluation points `1, …, 6` in `F₇`. -/
def α : Fin 6 → ZMod 7 := ![1, 2, 3, 4, 5, 6]

theorem α_injective : Function.Injective α := by decide

/-- `RS(6, 2)` has dimension 2 and minimum distance 5: it is MDS. -/
example : Module.finrank (ZMod 7) (code α 2) = 2 := finrank_code α_injective (by norm_num)

example : (code α 2).minDist = 5 := minDist_code α_injective (by norm_num) (by norm_num)

example : (code α 2).minDist = (6 - Module.finrank (ZMod 7) (code α 2) + 1 : ℕ) :=
  minDist_code_eq_singleton α_injective (by norm_num) (by norm_num)

/-- The bound is attained by `X - 1`, which vanishes at the first point only. -/
theorem encode_X_sub_one : encode α (X - C 1) = ![0, 1, 2, 3, 4, 5] := by
  funext i
  fin_cases i <;> simp [encode, α] <;> decide

example : hammingNorm (encode α (X - C 1)) = 5 := by
  rw [encode_X_sub_one]
  decide

/-- The message `X + 3` encodes to `(4, 5, 6, 0, 1, 2)`. -/
theorem encode_X_add_three : encode α (X + C 3) = ![4, 5, 6, 0, 1, 2] := by
  funext i
  fin_cases i <;> simp [encode, α] <;> decide

/-- Two errors, at the first two points: the received word is `(5, 6, 6, 0, 1, 2)`. -/
def y : Fin 6 → ZMod 7 := ![5, 6, 6, 0, 1, 2]

theorem y_eq : y = encode α (X + C 3) + ![1, 1, 0, 0, 0, 0] := by
  rw [encode_X_add_three]
  decide

/-- The error locator `(X - 1)(X - 2)` and `Q = (X + 3)(X - 1)(X - 2)` solve the key equations
for `y` with error budget 2. -/
example : IsKeySolution α 2 2 y ((X + C 3) * ((X - C 1) * (X - C 2))) ((X - C 1) * (X - C 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (monic_X_sub_C 1).mul (monic_X_sub_C 2)
  · rw [((monic_X_sub_C 1)).natDegree_mul (monic_X_sub_C 2), natDegree_X_sub_C,
      natDegree_X_sub_C]
  · rw [degree_mul, degree_mul, degree_X_add_C, degree_X_sub_C, degree_X_sub_C]
    decide
  · intro i
    fin_cases i <;> simp [α, y] <;> decide

/-- **Berlekamp-Welch recovers `X + 3`** from `y`, with any key-equation solver (here the
classical one). -/
example : decode (KeySolver.ofChoice α 2 ((6 - 2) / 2)) y = some (X + C 3) := by
  rw [y_eq]
  refine decode_encode_add α_injective (by norm_num) _ ?_ ?_
  · rw [degree_X_add_C]
    decide
  · decide

theorem hammingDist_y : hammingDist y (encode α (X + C 3)) ≤ 2 := by
  rw [y_eq, hammingDist_eq_hammingNorm_sub, add_sub_cancel_left]
  decide

/-- Every solution of the key equations divides out to the message. -/
example (Q E : (ZMod 7)[X]) (h : IsKeySolution α 2 2 y Q E) : Q /ₘ E = X + C 3 := by
  have hdeg : (X + C (3 : ZMod 7)).degree < ((2 : ℕ) : WithBot ℕ) := by
    rw [degree_X_add_C]
    decide
  exact divByMonic_eq_of_isKeySolution α_injective (by norm_num) hdeg hammingDist_y h

/-- Padding: with one error (at the first point) and budget 2, the error locator `X - 1` is padded
by `X` to degree 2. -/
example : IsKeySolution α 2 2 (encode α (X + C 3) + ![1, 0, 0, 0, 0, 0])
    ((X + C 3) * ((X - C 1) * X)) ((X - C 1) * X) := by
  rw [encode_X_add_three]
  refine ⟨(monic_X_sub_C 1).mul monic_X, ?_, ?_, ?_⟩
  · rw [(monic_X_sub_C 1).natDegree_mul monic_X, natDegree_X_sub_C, natDegree_X]
  · rw [degree_mul, degree_mul, degree_X_add_C, degree_X_sub_C, degree_X]
    decide
  · intro i
    fin_cases i <;> simp [α] <;> decide

/-- Beyond the radius: the weight-3 error `(0, 6, 5, 4, 0, 0)` turns the encoding of `X + 3` into
`(4, 4, 4, 4, 1, 2)`, which is within distance 2 of the encoding of the constant `4`. Every
solver then decodes to the wrong message. -/
theorem encode_C_four : encode α (C 4) = ![4, 4, 4, 4, 4, 4] := by
  funext i
  fin_cases i <;> simp [encode]

example (S : KeySolver α 2 ((6 - 2) / 2)) :
    decode S (encode α (X + C 3) + ![0, 6, 5, 4, 0, 0]) = some (C 4) := by
  refine (decode_eq_some_iff α_injective (by norm_num) S).mpr ⟨?_, ?_⟩
  · rw [degree_C (by decide)]
    decide
  · rw [encode_X_add_three, encode_C_four]
    decide

/-- Failure: no polynomial of degree less than 2 has its encoding within distance 2 of
`(0, 0, 0, 1, 1, 1)`, so every solver reports `none`. -/
example (S : KeySolver α 2 2) : decode S ![0, 0, 0, 1, 1, 1] = none := by
  rw [decode_eq_none_iff α_injective (by norm_num) S]
  intro p hp
  have hlin : p = C (p.coeff 0) + C (p.coeff 1) * X := by
    have h1 : p.degree ≤ 1 := Order.le_of_lt_succ (by exact_mod_cast hp)
    rw [eq_X_add_C_of_degree_le_one h1, add_comm, mul_comm]
    simp [coeff_C, coeff_X]
  have henc : encode α p = fun i ↦ p.coeff 0 + p.coeff 1 * α i := by
    funext i
    rw [encode]
    conv_lhs => rw [hlin]
    simp
  rw [henc]
  have key : ∀ a b : ZMod 7,
      2 < hammingDist (![0, 0, 0, 1, 1, 1] : Fin 6 → ZMod 7) (fun i ↦ a + b * α i) := by
    decide
  exact key _ _

end Cslib.CodingTheory.ReedSolomonTests
