/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.MultiplicativeAdditiveOnSquares
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.ZMod.Defs

namespace MetaMathlibExt.multiplicative_additive_on_squares.Test

-- The identity function realizes the branch that fixes all squares.
example (m : ℕ) (hm : 0 < m) :
    (ArithmeticFunction.id : ArithmeticFunction ℂ) (m ^ 2) = (m : ℂ) ^ 2 := by
  apply (multiplicative_additive_on_squares _ ArithmeticFunction.isMultiplicative_id.natCast
    (fun _ _ _ _ => Nat.cast_add ..)).2.2 _ m hm
  change ((4 : ℕ) : ℂ) = 4
  norm_num

open scoped Fin.CommRing

-- The other branch is realized by a function periodic modulo four, with values 0, 1, 2, 1.
private def weight (r : Fin 4) : ℕ := if r = 3 then 1 else r.val

private def residueFunction : ArithmeticFunction ℂ :=
  ⟨fun n => (weight (n : Fin 4) : ℂ), Nat.cast_zero⟩

private theorem residue_apply (n : ℕ) : residueFunction n = (weight (n : Fin 4) : ℂ) := rfl

private theorem residue_mult : residueFunction.IsMultiplicative := by
  have table : ∀ a b : Fin 4, a.val % 2 = 1 ∨ b.val % 2 = 1 →
      weight (a * b) = weight a * weight b := by decide
  refine ⟨Nat.cast_one, fun {m n} hcop => ?_⟩
  have h : ¬ (2 ∣ m ∧ 2 ∣ n) := by
    rintro ⟨hm, hn⟩
    have := Nat.dvd_gcd hm hn
    rw [hcop.gcd_eq_one] at this
    omega
  simp only [residue_apply, Nat.cast_mul]
  rw [table, Nat.cast_mul]
  change m % 4 % 2 = 1 ∨ n % 4 % 2 = 1
  omega

private theorem residue_add (m n : ℕ) :
    residueFunction (m ^ 2 + n ^ 2) = residueFunction (m ^ 2) + residueFunction (n ^ 2) := by
  have table : ∀ a b : Fin 4, weight (a ^ 2 + b ^ 2) = weight (a ^ 2) + weight (b ^ 2) := by
    decide
  simp only [residue_apply, Nat.cast_add, Nat.cast_pow, table]

example (k : ℕ) (hk : 0 < k) : residueFunction (2 ^ (2 * k)) = 0 := by
  have h := (multiplicative_additive_on_squares residueFunction residue_mult
    (fun m n _ _ => residue_add m n)).2.1 2 k (by decide) hk
  have h4 : residueFunction (2 ^ 2) = 0 := Nat.cast_zero
  rw [h, h4, zero_pow hk.ne']

end MetaMathlibExt.multiplicative_additive_on_squares.Test
