/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ValuationOnePoints
import Mathlib.Tactic.NormNum

/-!
# Tests for lifts of a singular point

At the origin modulo three, `x² + y² + 3` has nine lifts with valuation one, and `xy` has none.
-/

namespace MetaMathlibExt

open MvPolynomial

example :
    ((Finset.range 3 ×ˢ Finset.range 3).filter fun kl : ℕ × ℕ =>
      let z : ℤ := (kl.1 * 3 : ℤ) ^ 2 + (kl.2 * 3 : ℤ) ^ 2 + 3
      3 ∣ z ∧ ¬ 9 ∣ z).card = 9 := by
  let f : MvPolynomial (Fin 2) ℤ := X 0 ^ 2 + X 1 ^ 2 + C 3
  have grad (i : Fin 2) : (3 : ℤ) ∣ eval ![0, 0] (pderiv i f) := by
    simp only [f, map_add, pderiv_C]
    simp
  have h := card_lift_padicVal_eq_one_of_singular Nat.prime_three f
    (r := 0) (s := 0) (by decide) (by decide) (by norm_num [f]) (grad 0) (grad 1)
  simpa [f] using h

example :
    ((Finset.range 3 ×ˢ Finset.range 3).filter fun kl : ℕ × ℕ =>
      let z : ℤ := (kl.1 * 3 : ℤ) * (kl.2 * 3 : ℤ)
      3 ∣ z ∧ ¬ 9 ∣ z).card = 0 := by
  let f : MvPolynomial (Fin 2) ℤ := X 0 * X 1
  have h := card_lift_padicVal_eq_one_of_singular Nat.prime_three f
    (r := 0) (s := 0) (by decide) (by decide) (by simp [f]) (by simp [f]) (by simp [f])
  simpa [f] using h

end MetaMathlibExt
