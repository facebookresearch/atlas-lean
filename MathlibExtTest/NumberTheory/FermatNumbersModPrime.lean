/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FermatNumbersModPrime
import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.FermatResiduePeriod

/-!
# Tests for Fermat numbers modulo a prime

* `p = 7`: `ord_7(2) = 3`, so the residues `3, 5, 3, 5, …` of `F_n` have
  preperiod `0` and period `ord_3(2) = 2`. Lemmas 2, 4 and 6 give
  `F_1 ≡ F_7 (mod 7)` without computing `F_7`, and Proposition 18 shows that
  `7` divides no Fermat number.
* `p = 7`, `g = 3`: `3 ^ 2 = 2`, so `ind_3(2) = 2 = 2^1 · 1`; this checks
  Lemma 8, Propositions 11 and 13 (also at the exponent `8`, outside the
  paper's range, where both sides are false), Corollary 14 and Theorem 15.
* `p = 17`, `g = 6`: `6 ^ 2 = 2`, so `ind_6(2) = 2^1 · 1` and `16 = 2^4 · 1`.
  Theorem 15 gives preperiod `3` and period `ord_1(2) = 1`, and Lemma 17
  gives `ord_17(2) = 8` from `17 ∣ F_2`.
* Lemma 17 at Euler's factor `641 ∣ F_5`: `ord_641(2) = 64`.
* Theorem 22 at `p = 7, 11, 13`, whose orders `3, 10, 12` have `2`-parts
  `1, 2, 4`; Theorem 23 for small `v`.
* The helper lemmas on small inputs.
-/

@[expose] public section

namespace MetaMathlibExtTest.FermatNumbersModPrime

open MetaMathlibExt

/-! ### Concrete orders and primitive roots -/

theorem orderOf_two_seven : orderOf (2 : ZMod 7) = 3 :=
  orderOf_eq_prime_pow (p := 3) (n := 0) (by decide) (by decide)

theorem orderOf_two_three : orderOf (2 : ZMod 3) = 2 :=
  orderOf_eq_prime_pow (p := 2) (n := 0) (by decide) (by decide)

theorem orderOf_two_seventeen : orderOf (2 : ZMod 17) = 8 :=
  orderOf_eq_prime_pow (p := 2) (n := 2) (by decide) (by decide)

theorem isPrimitiveRoot_three_seven : IsPrimitiveRoot (3 : ZMod 7) (7 - 1) :=
  IsPrimitiveRoot.iff_orderOf.mpr
    ((orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩)

theorem isPrimitiveRoot_six_seventeen :
    IsPrimitiveRoot (6 : ZMod 17) (17 - 1) :=
  IsPrimitiveRoot.iff_orderOf.mpr
    (orderOf_eq_prime_pow (p := 2) (n := 3) (by decide) (by decide))

/-- The exact preperiod `0` and period `2` modulo `7`, from Aigner's theorem
with `ord_7(2) = 2^0 · 3`. -/
theorem seven_preperiod_period :
    Function.Periodic (fun n : ℕ => (Nat.fermatNumber (0 + n) : ZMod 7)) 2 ∧
      (∀ h < 0, ¬ ∃ kp : ℕ, 0 < kp ∧
        Function.Periodic
          (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod 7)) kp) ∧
      (∀ kp : ℕ, 0 < kp →
        Function.Periodic
          (fun n : ℕ => (Nat.fermatNumber (0 + n) : ZMod 7)) kp → 2 ∣ kp) := by
  have h := Nat.fermatNumber_mod_prime_exact_preperiod_period 7 0 3
    (by norm_num) (by norm_num) (by rw [orderOf_two_seven]; rfl) (by decide)
  simp only [orderOf_two_three] at h
  exact h

/-! ### Lemmas 2, 4 and 6 -/

example : ∃ i j, i < j ∧ j ≤ 7 ∧
    Nat.fermatNumber i ≡ Nat.fermatNumber j [MOD 7] :=
  fermatNumber_modEq_exists_repeat 7 (by norm_num)

/-- The repeat found by pigeonhole: `F_0 = 3 ≡ 17 = F_2 (mod 7)`. -/
theorem fermatNumber_zero_modEq_two :
    Nat.fermatNumber 0 ≡ Nat.fermatNumber 2 [MOD 7] := by
  decide

example : Nat.fermatNumber 3 ≡ Nat.fermatNumber 5 [MOD 7] :=
  fermatNumber_modEq_add 7 0 2 fermatNumber_zero_modEq_two 3

example (h : ∀ t, 0 < t →
    ¬ Nat.fermatNumber 4 ≡ Nat.fermatNumber (4 + t) [MOD 11]) :
    ∀ t, 0 < t → ¬ Nat.fermatNumber 1 ≡ Nat.fermatNumber (1 + t) [MOD 11] :=
  fermatNumber_not_modEq_add_of_le 11 1 4 (by norm_num) h

/-- Lemma 6 at `p = 7`, `h = 0`, `k = 2`: `F_1 ≡ F_7 (mod 7)` since
`1 ≡ 7 (mod 2)`. -/
example : Nat.fermatNumber 1 ≡ Nat.fermatNumber 7 [MOD 7] := by
  obtain ⟨hper, hpre, hmin⟩ := seven_preperiod_period
  exact (fermatNumber_modEq_iff_preperiod_period 7 (by norm_num) 0 2
    (by norm_num) hper hpre hmin 1 7 (by norm_num)).mpr
      ⟨Nat.zero_le 1, by decide⟩

/-- Lemma 6 at `p = 7`: `F_2 ≢ F_5 (mod 7)` since `2 ≢ 5 (mod 2)`. -/
example : ¬ Nat.fermatNumber 2 ≡ Nat.fermatNumber 5 [MOD 7] := by
  obtain ⟨hper, hpre, hmin⟩ := seven_preperiod_period
  rw [fermatNumber_modEq_iff_preperiod_period 7 (by norm_num) 0 2
    (by norm_num) hper hpre hmin 2 5 (by norm_num)]
  decide

/-! ### Indices: Lemma 8, Propositions 11 and 13, Corollary 14 -/

example : Nat.gcd (7 - 1) 2 = (7 - 1) / orderOf (2 : ZMod 7) :=
  gcd_card_sub_one_exponent_eq_div_orderOf 7 (by norm_num) 3 2
    isPrimitiveRoot_three_seven 2 (by decide)

/-- Lemma 8 at the exponent `0`: `gcd(p - 1, 0) = p - 1 = (p - 1) / ord(1)`. -/
example : Nat.gcd (7 - 1) 0 = (7 - 1) / orderOf (1 : ZMod 7) :=
  gcd_card_sub_one_exponent_eq_div_orderOf 7 (by norm_num) 3 1
    isPrimitiveRoot_three_seven 0 (pow_zero _)

example : ∃ c, 0 < c ∧ Nat.Coprime c 12 ∧ c ≡ 3 [MOD 4] :=
  exists_coprime_modEq_of_coprime 4 3 12 (by norm_num) (by norm_num)

/-- Lemma 10 with `α = 0`: then `β = 1` and `c = 1`. -/
example : ∃ c, 0 < c ∧ Nat.Coprime c 30 ∧ c ≡ 1 [MOD 0] :=
  exists_coprime_modEq_of_coprime 0 1 30 (by norm_num) (by norm_num)

example : ∃ g : ZMod 7, IsPrimitiveRoot g (7 - 1) ∧
    g ^ ((7 - 1) / orderOf (2 : ZMod 7)) = 2 :=
  exists_primitiveRoot_pow_card_sub_one_div_orderOf 7 (by norm_num) 2
    (by decide)

/-- The primitive root `3` modulo `7` realizes Proposition 11 for `a = 2`. -/
example : (3 : ZMod 7) ^ ((7 - 1) / orderOf (2 : ZMod 7)) = 2 := by
  rw [orderOf_two_seven]
  decide

example : 2 ∣ 7 - 1 ↔ 2 = (7 - 1) / orderOf (2 : ZMod 7) :=
  exponent_dvd_card_sub_one_iff 7 (by norm_num) 3 2
    isPrimitiveRoot_three_seven 2 (by decide)

/-- Proposition 13 outside the paper's range: `3 ^ 8 = 2` modulo `7`, and
`8 ∤ 6`, `8 ≠ 6 / 3`. -/
example : ¬ 8 ∣ 7 - 1 ∧ ¬ 8 = (7 - 1) / orderOf (2 : ZMod 7) := by
  have h := exponent_dvd_card_sub_one_iff 7 (by norm_num) 3 2
    isPrimitiveRoot_three_seven 8 (by decide)
  rw [orderOf_two_seven] at h ⊢
  exact ⟨by decide, by decide⟩

/-- Corollary 14 at `p = 7 = 2^1 · 3 + 1`: the unique pair is `(1, 1)`. -/
example (st : ℕ × ℕ) (h : st.1 ≤ 1 ∧ st.2 ∣ 3 ∧
    ∃ g : ZMod 7, IsPrimitiveRoot g (7 - 1) ∧ g ^ (2 ^ st.1 * st.2) = 2) :
    st = (1, 1) := by
  obtain ⟨st', _, huniq⟩ := existsUnique_twoAdic_index_of_two 7 (by norm_num)
    (by norm_num) 1 3 (by decide) (by norm_num)
  rw [huniq st h, ← huniq (1, 1)
    ⟨le_rfl, one_dvd 3, 3, isPrimitiveRoot_three_seven, by decide⟩]

/-! ### Theorem 15 -/

/-- Theorem 15 at `p = 7`, `g = 3`: preperiod `1 - 1 = 0`, period
`ord_3(2) = 2`. -/
example : Function.Periodic
    (fun n : ℕ => (Nat.fermatNumber (1 - 1 + n) : ZMod 7)) 2 := by
  have h := (fermatNumber_mod_prime_preperiod_period_of_index 7 (by norm_num)
    (by norm_num) 1 3 (by decide) (by norm_num) 1 1 le_rfl (one_dvd 3) 3
    isPrimitiveRoot_three_seven (by decide)).1
  rwa [show 3 / 1 = 3 from rfl, orderOf_two_three] at h

/-- Theorem 15 at `p = 17`, `g = 6`: preperiod `4 - 1 = 3`, period
`ord_1(2) = 1`, so `F_n ≡ F_3 (mod 17)` for `n ≥ 3`, and the tail from `2` has
no positive period. -/
example : (∀ n, (Nat.fermatNumber (3 + n) : ZMod 17) = Nat.fermatNumber 3) ∧
    ¬ ∃ kp : ℕ, 0 < kp ∧
      Function.Periodic (fun n : ℕ => (Nat.fermatNumber (2 + n) : ZMod 17))
        kp := by
  obtain ⟨hper, hpre, -⟩ := fermatNumber_mod_prime_preperiod_period_of_index
    17 (by norm_num) (by norm_num) 4 1 (by decide) (by norm_num) 1 1
    (by norm_num) (one_dvd 1) 6 isPrimitiveRoot_six_seventeen (by decide)
  have h1 : orderOf (2 : ZMod (1 / 1)) = 1 :=
    orderOf_two_zmod_eq_one_iff.mpr rfl
  rw [h1] at hper
  refine ⟨fun n => ?_, hpre 2 (by norm_num)⟩
  induction n with
  | zero => rfl
  | succ n ih => exact (hper n).trans ih

/-! ### Lemma 17 and Proposition 18 -/

example : orderOf (2 : ZMod 17) = 2 ^ (2 + 1) :=
  (prime_dvd_fermatNumber_iff_orderOf_two 2 17 (by norm_num)
    (by norm_num)).mp (by decide)

/-- Euler's factor of `F_5 = 2^32 + 1`: `ord_641(2) = 64`. -/
example : orderOf (2 : ZMod 641) = 64 :=
  (prime_dvd_fermatNumber_iff_orderOf_two 5 641 (by norm_num)
    (by norm_num)).mp (by norm_num [Nat.fermatNumber])

/-- `7` divides no Fermat number, as its primitive period is `2`. -/
example : ¬ ∃ n : ℕ, 7 ∣ Nat.fermatNumber n := by
  obtain ⟨hper, -, hmin⟩ := seven_preperiod_period
  rw [exists_prime_dvd_fermatNumber_iff_period_eq_one 7 (by norm_num)
    (by norm_num) 0 2 (by norm_num) hper hmin]
  decide

/-- `17 ∣ F_2`, so every primitive period of a tail modulo `17` is `1`. -/
example (h k : ℕ) (hk : 0 < k)
    (hper : Function.Periodic
      (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod 17)) k)
    (hmin : ∀ kp : ℕ, 0 < kp →
      Function.Periodic
        (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod 17)) kp → k ∣ kp) :
    k = 1 :=
  (exists_prime_dvd_fermatNumber_iff_period_eq_one 17 (by norm_num)
    (by norm_num) h k hk hper hmin).mp ⟨2, by decide⟩

/-! ### Theorems 22 and 23 -/

/-- `7 ≡ 7 (mod 8)` and `ord_7(2) = 3` is odd. -/
example : ¬ 2 ∣ orderOf (2 : ZMod 7) :=
  (orderOf_two_twoAdic_of_mod_eight 7 (by norm_num)).1 (by norm_num)

/-- `11 ≡ 3 (mod 8)` and `ord_11(2) = 10`. -/
example : 2 ∣ orderOf (2 : ZMod 11) ∧ ¬ 4 ∣ orderOf (2 : ZMod 11) :=
  (orderOf_two_twoAdic_of_mod_eight 11 (by norm_num)).2.1 (by norm_num)

/-- `13 ≡ 5 (mod 8)` and `ord_13(2) = 12`. -/
example : 4 ∣ orderOf (2 : ZMod 13) ∧ ¬ 8 ∣ orderOf (2 : ZMod 13) :=
  (orderOf_two_twoAdic_of_mod_eight 13 (by norm_num)).2.2 (by norm_num)

example : orderOf (2 : ZMod 11) = 10 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩

example : orderOf (2 : ZMod 13) = 12 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩

example (v : ℕ) : ∃ p : ℕ, p.Prime ∧ p % 8 = 1 ∧
    (∃ k : ℕ, 0 < k ∧
      Function.Periodic (fun n : ℕ => (Nat.fermatNumber (v + n) : ZMod p)) k) ∧
    ∀ h < v, ¬ ∃ kp : ℕ, 0 < kp ∧
      Function.Periodic (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp :=
  exists_prime_one_mod_eight_fermat_preperiod v

/-! ### Helpers -/

example (n : ℕ) : (Nat.fermatNumber (n + 1) : ℤ) =
    ((Nat.fermatNumber n : ℤ) - 1) ^ 2 + 1 :=
  cast_fermatNumber_succ n

/-- The oddness hypotheses of `two_pow_mul_odd_inj` are needed. -/
example : 2 ^ 3 * 5 = 2 ^ 1 * 20 ∧ ¬ (3 = 1 ∧ 5 = 20) := by decide

example : 2 ^ 3 * 5 ≠ 2 ^ 2 * 7 := fun h =>
  absurd ((two_pow_mul_odd_inj (by decide) (by decide)).mp h).1 (by decide)

/-- `6 ∣ 2^2 · 3` and `4 ∤ 6` give `6 ∣ 2 · 3`. -/
example : 6 ∣ 2 ^ 1 * 3 :=
  dvd_pow_mul_of_dvd_pow_succ_mul Nat.prime_two (by decide) (by decide)

example : (2 : ZMod 13) ≠ 0 := two_ne_zero_zmod (by norm_num) (by norm_num)

example : orderOf (2 : ZMod 1) = 1 := orderOf_two_zmod_eq_one_iff.mpr rfl

example : orderOf (2 : ZMod 9) ≠ 1 := fun h =>
  absurd (orderOf_two_zmod_eq_one_iff.mp h) (by norm_num)

example : 0 < orderOf (2 : ZMod 9) := orderOf_two_zmod_pos (by decide)

/-- `n ↦ n % 2` has period `2` from `0`, so period `4` from `5`; that
period moves back down to the tail from `0`. -/
example : Function.Periodic (fun n => (fun m => m % 2) (0 + n)) 4 := by
  have h0 : Function.Periodic (fun n => (fun m => m % 2) (0 + n)) 2 :=
    fun n => by simp
  have h5 : Function.Periodic (fun n => (fun m => m % 2) (5 + n)) 4 :=
    periodic_tail_of_le (f := fun m => m % 2) (h := 0) (by norm_num)
      (by simpa using h0.nat_mul 2)
  exact periodic_tail_of_periodic_tail_of_le (f := fun m => m % 2)
    (Nat.zero_le 5) two_pos h0 h5

/-! ### Axioms -/

#print axioms periodic_tail_of_le
#print axioms periodic_tail_of_periodic_tail_of_le
#print axioms cast_fermatNumber_succ
#print axioms two_pow_mul_odd_inj
#print axioms dvd_pow_mul_of_dvd_pow_succ_mul
#print axioms two_ne_zero_zmod
#print axioms orderOf_two_zmod_eq_one_iff
#print axioms orderOf_two_zmod_pos
#print axioms fermatNumber_modEq_exists_repeat
#print axioms fermatNumber_modEq_add
#print axioms fermatNumber_not_modEq_add_of_le
#print axioms fermatNumber_modEq_iff_preperiod_period
#print axioms gcd_card_sub_one_exponent_eq_div_orderOf
#print axioms exists_coprime_modEq_of_coprime
#print axioms exists_primitiveRoot_pow_card_sub_one_div_orderOf
#print axioms exponent_dvd_card_sub_one_iff
#print axioms existsUnique_twoAdic_index_of_two
#print axioms fermatNumber_mod_prime_preperiod_period_of_index
#print axioms prime_dvd_fermatNumber_iff_orderOf_two
#print axioms exists_prime_dvd_fermatNumber_iff_period_eq_one
#print axioms orderOf_two_twoAdic_of_mod_eight
#print axioms exists_prime_one_mod_eight_fermat_preperiod

end MetaMathlibExtTest.FermatNumbersModPrime
