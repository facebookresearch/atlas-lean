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

-- The minimal arity fixes prime powers, not just positive squares.
example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x : Fin 2 → ℕ, (∀ i, ∃ m n : ℕ, n < m ∧ x i = ∑ j ∈ Finset.Ioc n m, j ^ 2) →
      f (∑ i, x i) = ∑ i, f (x i)) :
    f (47 ^ 2) = ((47 ^ 2 : ℕ) : ℂ) ∧ f (2 ^ 5) = ((2 ^ 5 : ℕ) : ℂ) := by
  have h := consecutiveSquareSums_kAdditiveUniqueness (k := 2) (hk := le_rfl) (f := f)
    (hf := hf) (hadd := hadd)
  exact ⟨h (47 ^ 2), h (2 ^ 5)⟩

-- At larger arity the hypothesis still quantifies over positive blocks, but the conclusion
-- includes arguments too small to be a sum of that many blocks (as well as zero).
example (f : ArithmeticFunction ℂ) (hf : f.IsMultiplicative)
    (hadd : ∀ x : Fin 5 → ℕ, (∀ i, ∃ m n : ℕ, n < m ∧ x i = ∑ j ∈ Finset.Ioc n m, j ^ 2) →
      f (∑ i, x i) = ∑ i, f (x i)) : f 0 = 0 ∧ f 3 = 3 := by
  have h := consecutiveSquareSums_kAdditiveUniqueness 5 (by decide) f hf hadd
  exact ⟨by simpa only [Nat.cast_zero] using h 0, by simpa only [Nat.cast_ofNat] using h 3⟩

-- Zero is not eligible for padding: the last index in any allowed interval contributes positively.
example : ¬ ∃ m n : ℕ, n < m ∧ 0 = ∑ j ∈ Finset.Ioc n m, j ^ 2 := by
  rintro ⟨m, n, hnm, hsum⟩
  have hm : m ^ 2 ≤ ∑ j ∈ Finset.Ioc n m, j ^ 2 :=
    Finset.single_le_sum (f := fun j : ℕ => j ^ 2) (fun j _ => Nat.zero_le (j ^ 2))
      (Finset.mem_Ioc.mpr ⟨hnm, le_rfl⟩)
  rw [← hsum] at hm
  exact (Nat.pow_pos (by omega : 0 < m)).not_ge hm

-- The old counterexample on individual squares is not additive on consecutive-square blocks.
example : ¬ (∀ x : Fin 2 → ℕ,
    (∀ i, ∃ m n : ℕ, n < m ∧ x i = ∑ j ∈ Finset.Ioc n m, j ^ 2) →
    residueFunction (∑ i, x i) = ∑ i, residueFunction (x i)) := by
  intro h
  have he := h (fun _ => 14) (fun _ => ⟨3, 0, by decide, by decide⟩)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  change residueFunction 28 = 2 * residueFunction 14 at he
  have h28 : residueFunction 28 = 0 := Nat.cast_zero
  have h14 : residueFunction 14 = 2 := Nat.cast_ofNat
  rw [h28, h14] at he
  norm_num at he

end MetaMathlibExt.multiplicative_additive_on_squares.Test
