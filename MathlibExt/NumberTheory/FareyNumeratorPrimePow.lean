/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Rat.Floor
public import MathlibExt.NumberTheory.FareyNumeratorFormula
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith

namespace MathlibExt.NumberTheory.FareyNumeratorWanted

open Finset

/-- **Corollary 1**: for a prime `p` and positive `m`
with `p ^ m ≤ n`,
`N_n(p^m) = ⌈(n - p^m)(1 - 1/p)⌉`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 1. -/
public theorem fareyNumeratorCount_prime_pow (p m n : ℕ)
    (hp : p.Prime) (hm : 0 < m) (hpn : p ^ m ≤ n) :
    (fareyNumeratorCount n (p ^ m) : ℤ) =
      ⌈((n : ℚ) - (p : ℚ) ^ m) * (1 - 1 / (p : ℚ))⌉ := by
  let d := n - p ^ m
  have hpd : p ∣ p ^ m := dvd_pow_self p hm.ne'
  have hdc : (d : ℚ) = (n : ℚ) - (p : ℚ) ^ m := by
    simp [d, Nat.cast_sub hpn]
  have hcop (b : ℕ) : (p ^ m).Coprime b ↔ ¬p ∣ b :=
    (Nat.coprime_pow_left_iff hm p b).trans hp.coprime_iff_not_dvd
  have hcount : fareyNumeratorCount n (p ^ m) =
      ((Ioc 0 d).filter (fun j => ¬p ∣ j)).card := by
    have hendpoint : ¬(p ^ m).Coprime (p ^ m) := fun h => (hcop _).mp h hpd
    rw [fareyNumeratorCount, ← insert_left_Ioc hpn, filter_insert, ite_eq_right hendpoint]
    simp only [hcop]
    refine card_nbij' (fun b => b - p ^ m) (fun j => p ^ m + j) ?_ ?_ ?_ ?_
    · intro b hb
      simp only [mem_coe, mem_filter, mem_Ioc] at hb ⊢
      refine ⟨⟨by omega, by dsimp [d]; omega⟩, ?_⟩
      intro h
      apply hb.2
      simpa only [Nat.add_sub_of_le hb.1.1.le] using dvd_add hpd h
    · intro j hj
      simp only [mem_coe, mem_filter, mem_Ioc] at hj ⊢
      refine ⟨⟨by omega, by dsimp [d] at hj; omega⟩, ?_⟩
      exact fun h => hj.2 ((Nat.dvd_add_iff_right hpd).mpr h)
    · intro b hb
      simp only [mem_coe, mem_filter, mem_Ioc] at hb
      change p ^ m + (b - p ^ m) = b
      omega
    · intro j _
      change p ^ m + j - p ^ m = j
      omega
  have hpartition := card_filter_add_card_filter_not (s := Ioc 0 d) (fun j => p ∣ j)
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.card_Ioc, Nat.sub_zero, ← hcount] at hpartition
  have hvalue : fareyNumeratorCount n (p ^ m) = d - d / p := by omega
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hdecomp : (d % p : ℚ) + (p : ℚ) * (d / p : ℕ) = d := by
    exact_mod_cast Nat.mod_add_div d p
  have hquot : (d : ℚ) / p = (d / p : ℕ) + (d % p : ℚ) / p := by
    apply (div_eq_iff hpq.ne').2
    rw [add_mul, div_mul_cancel₀ _ hpq.ne']
    linarith
  have hr0 : 0 ≤ (d % p : ℚ) / p := div_nonneg (Nat.cast_nonneg _) hpq.le
  have hr1 : (d % p : ℚ) / p < 1 :=
    (div_lt_one hpq).2 (by exact_mod_cast Nat.mod_lt d hp.pos)
  rw [hvalue, ← hdc, eq_comm, Int.ceil_eq_iff, Int.cast_natCast,
    Nat.cast_sub (Nat.div_le_self d p), mul_sub, mul_one, mul_one_div, hquot]
  constructor <;> linarith

end MathlibExt.NumberTheory.FareyNumeratorWanted
