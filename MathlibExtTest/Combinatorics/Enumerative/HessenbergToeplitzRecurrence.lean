/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.HessenbergToeplitzRecurrence
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.FinCases

namespace MetaMathlibExt.det_hessenbergToeplitz_eq_recurrence.Test

-- With two coefficients equal to one, the determinant is a Fibonacci number.
example : (!![1, 1, 0; -1, 1, 1; 0, -1, 1] : Matrix (Fin 3) (Fin 3) ℤ).det = 3 := by
  let β (m : ℕ) : ℤ := Nat.fib (m - 1)
  have hrec (m : ℕ) (hm : 2 < m) : β m = ∑ j ∈ Finset.Icc 1 2, (1 : ℤ) * β (m - j) := by
    obtain ⟨r, rfl⟩ : ∃ r, m = r + 3 := ⟨m - 3, by omega⟩
    simp [β, show Finset.Icc 1 2 = {1, 2} by decide, Nat.fib_add_two, add_comm]
  have h := det_hessenbergToeplitz_eq_recurrence 2 (by decide) (fun _ => 1) β
    (fun i hi hi' => by rw [show i = 1 by omega]; rfl) (by rfl) hrec 3
  convert h using 2
  · ext i j
    fin_cases i <;> fin_cases j <;> decide
  · decide

-- A zero last coefficient is allowed, including when the bandwidth exceeds the size.
private theorem zeroCoefficients (n : ℕ) :
    (Matrix.of fun a b : Fin n =>
      if (a : ℕ) = b + 1 then (-1 : ℤ) else 0).det = if n = 0 then 1 else 0 := by
  let β (m : ℕ) : ℤ := if m = 3 then 1 else 0
  have h := det_hessenbergToeplitz_eq_recurrence 3 (by decide) (fun _ => 0) β
    (fun i _ hi => by simp [β, hi.ne]) (by rfl) (fun m hm => by simp [β, hm.ne']) n
  convert h using 2
  · ext i j
    simp only [Matrix.of_apply]
    split_ifs <;> first | rfl | omega
  · omega

example : (Matrix.of fun a b : Fin 0 =>
    if (a : ℕ) = b + 1 then (-1 : ℤ) else 0).det = 1 := zeroCoefficients 0

example : (Matrix.of fun a b : Fin 1 =>
    if (a : ℕ) = b + 1 then (-1 : ℤ) else 0).det = 0 := zeroCoefficients 1

end MetaMathlibExt.det_hessenbergToeplitz_eq_recurrence.Test
