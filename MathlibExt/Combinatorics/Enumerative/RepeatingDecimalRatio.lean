/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ZMod.LocalRing
import Mathlib.Tactic.FieldSimp

/-!
# Counting repeating-decimal ratios

`MetaMathlibExt.ncard_repeating_decimal_ratio_eq_two_pow_omega` counts the solutions by
writing each denominator as `10 ^ n + t`. The offsets are precisely the representatives of
the roots of `t * (t + 1) = 0` modulo `10 ^ n - 1`. Each prime-power factor contributes two roots.
-/

namespace MetaMathlibExt
namespace RepeatingDecimalRatio

private theorem exists_numerator_iff {x m t : ℕ} (hx : 0 < x) (hm : 0 < m) :
    (∃ k : ℕ, x ≤ k ∧ k < 2 * x ∧ (k : ℚ) / x = 1 + (t : ℚ) / m) ↔
      t < m ∧ m ∣ x * t := by
  have cross (k : ℕ) : (k : ℚ) / x = 1 + (t : ℚ) / m ↔ k * m = x * m + x * t := by
    have hx' : (x : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [← Nat.cast_inj (R := ℚ)]
    push_cast
    field_simp
  constructor
  · rintro ⟨k, hxk, hk, h⟩
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hxk
    have hq : x * t = q * m := by simpa [Nat.add_mul] using ((cross _).mp h).symm
    refine ⟨Nat.lt_of_mul_lt_mul_left (a := x) ?_, q, hq.trans (Nat.mul_comm ..)⟩
    rw [hq]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hm
  · rintro ⟨ht, q, hq⟩
    have hlt : q * m < x * m := by
      rw [Nat.mul_comm q, ← hq]
      exact Nat.mul_lt_mul_of_pos_left ht hx
    have : q < x := Nat.lt_of_mul_lt_mul_right hlt
    refine ⟨x + q, by omega, by omega, (cross _).mpr ?_⟩
    simp [Nat.add_mul, hq, Nat.mul_comm q m]

private theorem local_root_count (R : Type*) [CommRing R] [IsLocalRing R] :
    {z : R | z * (z + 1) = 0}.ncard = 2 := by
  have roots : {z : R | z * (z + 1) = 0} = {0, -1} := by
    ext z
    change z * (z + 1) = 0 ↔ z = 0 ∨ z = -1
    constructor
    · intro hz
      rcases IsLocalRing.isUnit_or_isUnit_of_add_one (show -z + (z + 1) = 1 by simp) with h | h
      · have hu : IsUnit z := by simpa using h.neg
        exact Or.inr (eq_neg_of_add_eq_zero_left (hu.mul_right_eq_zero.mp hz))
      · exact Or.inl (h.mul_left_eq_zero.mp hz)
    · rintro (rfl | rfl) <;> simp
  rw [roots, Set.ncard_pair (by simp)]

private theorem residue_root_count (m : ℕ) (hm : m ≠ 0) :
    {z : ZMod m | z * (z + 1) = 0}.ncard = 2 ^ ArithmeticFunction.cardDistinctFactors m := by
  classical
  let e := ZMod.equivPi m hm
  let R (p : m.primeFactors) := ZMod ((p : ℕ) ^ m.factorization p)
  have count (p : m.primeFactors) : Nat.card {z : R p // z * (z + 1) = 0} = 2 := by
    have hp := Nat.prime_of_mem_primeFactors p.property
    let : Fact (p : ℕ).Prime := ⟨hp⟩
    let : NeZero (m.factorization p) :=
      ⟨(hp.factorization_pos_of_dvd hm (Nat.dvd_of_mem_primeFactors p.property)).ne'⟩
    exact local_root_count (R p)
  -- Restrict the Chinese remainder equivalence to the roots in each coordinate.
  have equiv : {z : ZMod m // z * (z + 1) = 0} ≃ ∀ p, {z : R p // z * (z + 1) = 0} :=
    (e.toEquiv.subtypeEquiv (q := fun f => ∀ p, f p * (f p + 1) = 0) fun z => by
      rw [← e.injective.eq_iff, map_mul, map_add, map_one, map_zero]
      exact funext_iff).trans (Equiv.subtypePiEquivPi (p := fun p (z : R p) => z * (z + 1) = 0))
  change Nat.card {z : ZMod m // z * (z + 1) = 0} = _
  rw [Nat.card_congr equiv, Nat.card_pi]
  simp only [count, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  rw [ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

private theorem solution_set_as_image (b m : ℕ) (hm : 0 < m) (hb : b = m + 1) :
    {x : ℕ | b ≤ x ∧ x < b * 10 ∧ ∃ k : ℕ, x ≤ k ∧ k < 2 * x ∧
        (k : ℚ) / x = 1 + ((x : ℚ) - b) / m} =
      (fun z : ZMod m => b + z.val) '' {z | z * (z + 1) = 0} := by
  let : NeZero m := ⟨hm.ne'⟩
  -- At the denominator `b + t`, divisibility by `m` only sees the product `(1 + t) * t`.
  have shifted (t : ℕ) :
      (∃ k : ℕ, b + t ≤ k ∧ k < 2 * (b + t) ∧
        (k : ℚ) / (b + t : ℕ) = 1 + (((b + t : ℕ) : ℚ) - b) / m) ↔
        t < m ∧ (t : ZMod m) * (t + 1) = 0 := by
    rw [show (((b + t : ℕ) : ℚ) - b) = t by simp, exists_numerator_iff (by omega) hm,
      ← ZMod.natCast_eq_zero_iff]
    simp [hb, add_comm, mul_comm]
  ext x
  constructor
  · rintro ⟨hbx, _, hk⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hbx
    obtain ⟨ht, hz⟩ := (shifted t).mp hk
    exact ⟨(t : ZMod m), hz, congrArg (b + ·) (ZMod.val_natCast_of_lt ht)⟩
  · rintro ⟨z, hz, rfl⟩
    dsimp only
    have ht := z.val_lt
    refine ⟨by omega, by omega, (shifted _).mpr ⟨ht, ?_⟩⟩
    rwa [ZMod.natCast_zmod_val]

end RepeatingDecimalRatio

open RepeatingDecimalRatio

/-- **Counting solutions of a repeating-decimal ratio equation.** For every natural number
$n \ge 1$, the number of natural numbers $x$ with $10^n \le x < 10^{n+1}$ for which there is a
natural number $k$ with $x \le k < 2x$ and $k / x = 1 + (x - 10^n) / (10^n - 1)$, computed in the
rationals, (OEIS A285273) equals $2^{\omega(10^n - 1)}$, where $\omega(m)$ is the number of
distinct prime factors of $m$.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 13 (`jis-2026-26.1.8-thm-13`). -/
public theorem ncard_repeating_decimal_ratio_eq_two_pow_omega (n : ℕ) (hn : 1 ≤ n) :
    {x : ℕ | 10 ^ n ≤ x ∧ x < 10 ^ (n + 1) ∧ ∃ k : ℕ, x ≤ k ∧ k < 2 * x ∧
        (k : ℚ) / x = 1 + ((x : ℚ) - 10 ^ n) / (10 ^ n - 1)}.ncard =
      2 ^ ArithmeticFunction.cardDistinctFactors (10 ^ n - 1) := by
  let m : ℕ := 10 ^ n - 1
  have hb : 1 < 10 ^ n := one_lt_pow₀ (by decide : 1 < (10 : ℕ)) (by omega)
  have hm : 0 < m := by dsimp [m]; omega
  let : NeZero m := ⟨hm.ne'⟩
  have hcast : (10 : ℚ) ^ n - 1 = m := by
    dsimp [m]
    rw [Nat.cast_sub hb.le]
    norm_num
  rw [pow_succ (10 : ℕ), hcast, ← Nat.cast_ofNat (R := ℚ) (n := 10), ← Nat.cast_pow,
    solution_set_as_image _ m hm (by dsimp [m]; omega)]
  rw [Set.ncard_image_of_injective _ (fun _ _ h => ZMod.val_injective m (Nat.add_left_cancel h))]
  exact residue_root_count m hm.ne'

end MetaMathlibExt
