/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/NumberTheory/LucasLehmer.lean` (Mathlib):
Copyright (c) 2020 Kim Morrison. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Mario Carneiro, Alastair Irving, Kim Morrison, Ainsley Pahljina
-/

module

import Mathlib.RingTheory.Fintype

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LucasLehmer

/-!
# The Lucas-Lehmer test with a general seed

This file proves that the usual Lucas-Lehmer recurrence detects Mersenne primes when its
initial seed satisfies the two classical Jacobi-symbol conditions.
-/

@[expose] public section

namespace MetaMathlibExt

private def lucasLehmerSeed_D (s₁ : ℤ) (q : ℕ) : ZMod q := s₁ ^ 2 - 4

private def lucasLehmerSeed_X (_s₁ : ℤ) (q : ℕ) : Type := ZMod q × ZMod q

private instance lucasLehmerSeed_inhabited (s₁ : ℤ) (q : ℕ) :
    Inhabited (lucasLehmerSeed_X s₁ q) := inferInstanceAs (Inhabited (ZMod q × ZMod q))

private instance lucasLehmerSeed_decidableEq (s₁ : ℤ) (q : ℕ) :
    DecidableEq (lucasLehmerSeed_X s₁ q) := inferInstanceAs (DecidableEq (ZMod q × ZMod q))

private instance lucasLehmerSeed_addCommGroup (s₁ : ℤ) (q : ℕ) :
    AddCommGroup (lucasLehmerSeed_X s₁ q) :=
  inferInstanceAs (AddCommGroup (ZMod q × ZMod q))

@[simp] private theorem lucasLehmerSeed_zero_fst {s₁ : ℤ} {q : ℕ} :
    (0 : lucasLehmerSeed_X s₁ q).1 = 0 := rfl

@[simp] private theorem lucasLehmerSeed_zero_snd {s₁ : ℤ} {q : ℕ} :
    (0 : lucasLehmerSeed_X s₁ q).2 = 0 := rfl

@[simp] private theorem lucasLehmerSeed_add_fst {s₁ : ℤ} {q : ℕ}
    (x y : lucasLehmerSeed_X s₁ q) : (x + y).1 = x.1 + y.1 := rfl

@[simp] private theorem lucasLehmerSeed_add_snd {s₁ : ℤ} {q : ℕ}
    (x y : lucasLehmerSeed_X s₁ q) : (x + y).2 = x.2 + y.2 := rfl

@[simp] private theorem lucasLehmerSeed_neg_fst {s₁ : ℤ} {q : ℕ}
    (x : lucasLehmerSeed_X s₁ q) : (-x).1 = -x.1 := rfl

@[simp] private theorem lucasLehmerSeed_neg_snd {s₁ : ℤ} {q : ℕ}
    (x : lucasLehmerSeed_X s₁ q) : (-x).2 = -x.2 := rfl

private theorem lucasLehmerSeed_X_ext {s₁ : ℤ} {q : ℕ}
    {x y : lucasLehmerSeed_X s₁ q} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y := by
  cases x
  cases y
  congr

private instance lucasLehmerSeed_mul (s₁ : ℤ) (q : ℕ) : Mul (lucasLehmerSeed_X s₁ q) where
  mul x y :=
    (x.1 * y.1 + lucasLehmerSeed_D s₁ q * x.2 * y.2, x.1 * y.2 + x.2 * y.1)

@[simp] private theorem lucasLehmerSeed_mul_fst {s₁ : ℤ} {q : ℕ}
    (x y : lucasLehmerSeed_X s₁ q) :
    (x * y).1 = x.1 * y.1 + lucasLehmerSeed_D s₁ q * x.2 * y.2 := rfl

@[simp] private theorem lucasLehmerSeed_mul_snd {s₁ : ℤ} {q : ℕ}
    (x y : lucasLehmerSeed_X s₁ q) : (x * y).2 = x.1 * y.2 + x.2 * y.1 := rfl

private instance lucasLehmerSeed_one (s₁ : ℤ) (q : ℕ) : One (lucasLehmerSeed_X s₁ q) where
  one := (1, 0)

@[simp] private theorem lucasLehmerSeed_one_fst {s₁ : ℤ} {q : ℕ} :
    (1 : lucasLehmerSeed_X s₁ q).1 = 1 := rfl

@[simp] private theorem lucasLehmerSeed_one_snd {s₁ : ℤ} {q : ℕ} :
    (1 : lucasLehmerSeed_X s₁ q).2 = 0 := rfl

private instance lucasLehmerSeed_monoid (s₁ : ℤ) (q : ℕ) :
    Monoid (lucasLehmerSeed_X s₁ q) :=
  { lucasLehmerSeed_mul s₁ q, lucasLehmerSeed_one s₁ q with
    mul_assoc := fun x y z => by
      apply lucasLehmerSeed_X_ext <;> simp [lucasLehmerSeed_D] <;> ring
    one_mul := fun x => by
      apply lucasLehmerSeed_X_ext <;> simp
    mul_one := fun x => by
      apply lucasLehmerSeed_X_ext <;> simp }

private instance lucasLehmerSeed_natCast (s₁ : ℤ) (q : ℕ) :
    NatCast (lucasLehmerSeed_X s₁ q) where
  natCast n := (n, 0)

@[simp] private theorem lucasLehmerSeed_natCast_fst {s₁ : ℤ} {q : ℕ} (n : ℕ) :
    (n : lucasLehmerSeed_X s₁ q).1 = (n : ZMod q) := rfl

@[simp] private theorem lucasLehmerSeed_natCast_snd {s₁ : ℤ} {q : ℕ} (n : ℕ) :
    (n : lucasLehmerSeed_X s₁ q).2 = 0 := rfl

private instance lucasLehmerSeed_addGroupWithOne (s₁ : ℤ) (q : ℕ) :
    AddGroupWithOne (lucasLehmerSeed_X s₁ q) :=
  { lucasLehmerSeed_monoid s₁ q, lucasLehmerSeed_addCommGroup s₁ q,
      lucasLehmerSeed_natCast s₁ q with
    natCast_zero := by
      apply lucasLehmerSeed_X_ext <;> simp
    natCast_succ := fun _ => by
      apply lucasLehmerSeed_X_ext <;> simp
    intCast n := (n, 0)
    intCast_ofNat := fun _ => by
      apply lucasLehmerSeed_X_ext <;> simp
    intCast_negSucc := fun _ => by
      apply lucasLehmerSeed_X_ext <;> simp }

@[simp] private theorem lucasLehmerSeed_intCast_fst {s₁ : ℤ} {q : ℕ} (z : ℤ) :
    (z : lucasLehmerSeed_X s₁ q).1 = (z : ZMod q) := rfl

@[simp] private theorem lucasLehmerSeed_intCast_snd {s₁ : ℤ} {q : ℕ} (z : ℤ) :
    (z : lucasLehmerSeed_X s₁ q).2 = 0 := rfl

private instance lucasLehmerSeed_ring (s₁ : ℤ) (q : ℕ) : Ring (lucasLehmerSeed_X s₁ q) :=
  { lucasLehmerSeed_addGroupWithOne s₁ q, lucasLehmerSeed_addCommGroup s₁ q,
      lucasLehmerSeed_monoid s₁ q with
    left_distrib := fun x y z => by
      apply lucasLehmerSeed_X_ext <;> simp <;> ring
    right_distrib := fun x y z => by
      apply lucasLehmerSeed_X_ext <;> simp <;> ring
    mul_zero := fun x => by
      apply lucasLehmerSeed_X_ext <;> simp
    zero_mul := fun x => by
      apply lucasLehmerSeed_X_ext <;> simp }

private instance lucasLehmerSeed_commRing (s₁ : ℤ) (q : ℕ) :
    CommRing (lucasLehmerSeed_X s₁ q) :=
  { lucasLehmerSeed_ring s₁ q with
    mul_comm := fun x y => by
      apply lucasLehmerSeed_X_ext <;> simp <;> ring }

private instance lucasLehmerSeed_charP (s₁ : ℤ) (q : ℕ) :
    CharP (lucasLehmerSeed_X s₁ q) q where
  cast_eq_zero_iff x := by
    convert! ZMod.natCast_eq_zero_iff x q
    exact ⟨congr_arg Prod.fst, fun hx => lucasLehmerSeed_X_ext hx (by simp)⟩

private instance lucasLehmerSeed_coeZMod (s₁ : ℤ) (q : ℕ) :
    Coe (ZMod q) (lucasLehmerSeed_X s₁ q) where
  coe := ZMod.castHom dvd_rfl (lucasLehmerSeed_X s₁ q)

@[simp] private theorem lucasLehmerSeed_coeZMod_fst {s₁ : ℤ} {q : ℕ} (z : ZMod q) :
    (z : lucasLehmerSeed_X s₁ q).1 = z := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast]
  rfl

@[simp] private theorem lucasLehmerSeed_coeZMod_snd {s₁ : ℤ} {q : ℕ} (z : ZMod q) :
    (z : lucasLehmerSeed_X s₁ q).2 = 0 := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast]
  rfl

private instance lucasLehmerSeed_nontrivial (s₁ : ℤ) (q : ℕ) [Fact (1 < q)] :
    Nontrivial (lucasLehmerSeed_X s₁ q) :=
  ⟨⟨0, 1, ne_of_apply_ne Prod.fst zero_ne_one⟩⟩

private instance lucasLehmerSeed_fintype (s₁ : ℤ) (q : ℕ) [NeZero q] :
    Fintype (lucasLehmerSeed_X s₁ q) :=
  inferInstanceAs (Fintype (ZMod q × ZMod q))

private theorem lucasLehmerSeed_card_X (s₁ : ℤ) (q : ℕ) [NeZero q] :
    Fintype.card (lucasLehmerSeed_X s₁ q) = q ^ 2 := by
  change Fintype.card (ZMod q × ZMod q) = q ^ 2
  rw [Fintype.card_prod, ZMod.card, sq]

private theorem lucasLehmerSeed_card_units_lt (s₁ : ℤ) (q : ℕ) [NeZero q]
    (hq : 1 < q) : Fintype.card (lucasLehmerSeed_X s₁ q)ˣ < q ^ 2 := by
  have : Fact (1 < q) := ⟨hq⟩
  convert! card_units_lt (lucasLehmerSeed_X s₁ q)
  rw [lucasLehmerSeed_card_X]

private def lucasLehmerSeed_alpha (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    lucasLehmerSeed_X s₁ q :=
  ((s₁ : ZMod q) / 2, 1 / 2)

private def lucasLehmerSeed_beta (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    lucasLehmerSeed_X s₁ q :=
  ((s₁ : ZMod q) / 2, -(1 / 2))

@[simp] private theorem lucasLehmerSeed_alpha_fst (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    (lucasLehmerSeed_alpha s₁ q).1 = (s₁ : ZMod q) / 2 := rfl

@[simp] private theorem lucasLehmerSeed_alpha_snd (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    (lucasLehmerSeed_alpha s₁ q).2 = 1 / 2 := rfl

@[simp] private theorem lucasLehmerSeed_beta_fst (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    (lucasLehmerSeed_beta s₁ q).1 = (s₁ : ZMod q) / 2 := rfl

@[simp] private theorem lucasLehmerSeed_beta_snd (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    (lucasLehmerSeed_beta s₁ q).2 = -(1 / 2) := rfl

private theorem lucasLehmerSeed_two_ne_zero {q : ℕ} [Fact q.Prime] (hq_odd : Odd q) :
    (2 : ZMod q) ≠ 0 := by
  obtain ⟨k, hk⟩ := hq_odd
  intro h
  have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h
  have hq_le : q ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  have hq_eq : q = 2 := le_antisymm hq_le (Fact.out : q.Prime).two_le
  subst q
  omega

private theorem lucasLehmerSeed_alpha_add_beta (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) :
    lucasLehmerSeed_alpha s₁ q + lucasLehmerSeed_beta s₁ q =
      (s₁ : lucasLehmerSeed_X s₁ q) := by
  apply lucasLehmerSeed_X_ext
  · simp only [lucasLehmerSeed_add_fst, lucasLehmerSeed_alpha_fst,
      lucasLehmerSeed_beta_fst, lucasLehmerSeed_intCast_fst]
    field_simp [lucasLehmerSeed_two_ne_zero hq_odd]
    ring
  · simp

private theorem lucasLehmerSeed_alpha_mul_beta (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) :
    lucasLehmerSeed_alpha s₁ q * lucasLehmerSeed_beta s₁ q = 1 := by
  apply lucasLehmerSeed_X_ext
  · simp only [lucasLehmerSeed_mul_fst, lucasLehmerSeed_alpha_fst,
      lucasLehmerSeed_beta_fst, lucasLehmerSeed_alpha_snd,
      lucasLehmerSeed_beta_snd, lucasLehmerSeed_one_fst]
    rw [lucasLehmerSeed_D]
    field_simp [lucasLehmerSeed_two_ne_zero hq_odd]
    ring
  · simp
    ring

private theorem lucasLehmerSeed_beta_mul_alpha (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) :
    lucasLehmerSeed_beta s₁ q * lucasLehmerSeed_alpha s₁ q = 1 := by
  rw [mul_comm, lucasLehmerSeed_alpha_mul_beta s₁ q hq_odd]

private def lucasLehmerSeed_alphaUnit (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) : (lucasLehmerSeed_X s₁ q)ˣ where
  val := lucasLehmerSeed_alpha s₁ q
  inv := lucasLehmerSeed_beta s₁ q
  val_inv := lucasLehmerSeed_alpha_mul_beta s₁ q hq_odd
  inv_val := lucasLehmerSeed_beta_mul_alpha s₁ q hq_odd

@[simp] private theorem lucasLehmerSeed_alphaUnit_coe (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) :
    (lucasLehmerSeed_alphaUnit s₁ q hq_odd : lucasLehmerSeed_X s₁ q) =
      lucasLehmerSeed_alpha s₁ q := rfl

private theorem lucasLehmerSeed_closedForm (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) (j : ℕ) :
    ((Nat.iterate (fun x : ℤ => x ^ 2 - 2) j s₁ : ℤ) : lucasLehmerSeed_X s₁ q) =
      lucasLehmerSeed_alpha s₁ q ^ 2 ^ j + lucasLehmerSeed_beta s₁ q ^ 2 ^ j := by
  induction j with
  | zero =>
      simpa using (lucasLehmerSeed_alpha_add_beta s₁ q hq_odd).symm
  | succ j ih =>
      calc
        ((Nat.iterate (fun x : ℤ => x ^ 2 - 2) (j + 1) s₁ : ℤ) :
              lucasLehmerSeed_X s₁ q) =
            ((Nat.iterate (fun x : ℤ => x ^ 2 - 2) j s₁) ^ 2 - 2 : ℤ) := by
              rw [Function.iterate_succ_apply']
        _ = ((Nat.iterate (fun x : ℤ => x ^ 2 - 2) j s₁ : ℤ) :
              lucasLehmerSeed_X s₁ q) ^ 2 - 2 := by
              push_cast
              rfl
        _ = (lucasLehmerSeed_alpha s₁ q ^ 2 ^ j +
              lucasLehmerSeed_beta s₁ q ^ 2 ^ j) ^ 2 - 2 := by rw [ih]
        _ = (lucasLehmerSeed_alpha s₁ q ^ 2 ^ j) ^ 2 +
              (lucasLehmerSeed_beta s₁ q ^ 2 ^ j) ^ 2 +
              2 * (lucasLehmerSeed_beta s₁ q ^ 2 ^ j *
                lucasLehmerSeed_alpha s₁ q ^ 2 ^ j) - 2 := by ring
        _ = (lucasLehmerSeed_alpha s₁ q ^ 2 ^ j) ^ 2 +
              (lucasLehmerSeed_beta s₁ q ^ 2 ^ j) ^ 2 := by
              rw [← mul_pow, lucasLehmerSeed_beta_mul_alpha s₁ q hq_odd, one_pow]
              ring
        _ = lucasLehmerSeed_alpha s₁ q ^ 2 ^ (j + 1) +
              lucasLehmerSeed_beta s₁ q ^ 2 ^ (j + 1) := by
              rw [← pow_mul, ← pow_mul, _root_.pow_succ]

private theorem lucasLehmerSeed_two_lt_minFac (p' : ℕ) :
    2 < Nat.minFac (mersenne (p' + 2)) := by
  refine (Nat.minFac_prime (one_lt_mersenne.2 ?_).ne').two_le.lt_of_ne' ?_
  · omega
  · rw [Ne, Nat.minFac_eq_two_iff, mersenne, Nat.pow_succ']
    exact Nat.two_not_dvd_two_mul_sub_one (Nat.one_le_two_pow)

private theorem lucasLehmerSeed_mersenne_coe_X (s₁ : ℤ) (p : ℕ) :
    (mersenne p : lucasLehmerSeed_X s₁ (Nat.minFac (mersenne p))) = 0 := by
  apply lucasLehmerSeed_X_ext
  · simp only [lucasLehmerSeed_natCast_fst, lucasLehmerSeed_zero_fst]
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.minFac_dvd _
  · simp

private theorem lucasLehmerSeed_alpha_pow_neg_one (p' : ℕ) (s₁ : ℤ) (q : ℕ)
    [Fact q.Prime] (hq_odd : Odd q)
    (hM : (mersenne (p' + 2) : lucasLehmerSeed_X s₁ q) = 0)
    (hdiv : (mersenne (p' + 2) : ℤ) ∣
      Nat.iterate (fun x : ℤ => x ^ 2 - 2) p' s₁) :
    lucasLehmerSeed_alpha s₁ q ^ 2 ^ (p' + 1) = -1 := by
  obtain ⟨k, hk⟩ := hdiv
  replace hk := congr_arg (fun z : ℤ => (z : lucasLehmerSeed_X s₁ q)) hk
  rw [lucasLehmerSeed_closedForm s₁ q hq_odd] at hk
  push_cast at hk
  rw [hM] at hk
  simp only [zero_mul] at hk
  have h := congr_arg
    (fun x : lucasLehmerSeed_X s₁ q => lucasLehmerSeed_alpha s₁ q ^ 2 ^ p' * x) hk
  have hexp : 2 ^ p' + 2 ^ p' = 2 ^ (p' + 1) := by ring
  rw [mul_add, ← pow_add, hexp, ← mul_pow, lucasLehmerSeed_alpha_mul_beta s₁ q hq_odd,
    one_pow, mul_zero] at h
  linear_combination h

private theorem lucasLehmerSeed_alpha_pow_one (p' : ℕ) (s₁ : ℤ) (q : ℕ)
    [Fact q.Prime] (hq_odd : Odd q)
    (hM : (mersenne (p' + 2) : lucasLehmerSeed_X s₁ q) = 0)
    (hdiv : (mersenne (p' + 2) : ℤ) ∣
      Nat.iterate (fun x : ℤ => x ^ 2 - 2) p' s₁) :
    lucasLehmerSeed_alpha s₁ q ^ 2 ^ (p' + 2) = 1 := by
  calc
    lucasLehmerSeed_alpha s₁ q ^ 2 ^ (p' + 2) =
        (lucasLehmerSeed_alpha s₁ q ^ 2 ^ (p' + 1)) ^ 2 := by
      rw [← pow_mul, ← Nat.pow_succ]
    _ = (-1) ^ 2 := by
      rw [lucasLehmerSeed_alpha_pow_neg_one p' s₁ q hq_odd hM hdiv]
    _ = 1 := by norm_num

private theorem lucasLehmerSeed_order_alpha (p' : ℕ) (s₁ : ℤ) (q : ℕ)
    [Fact q.Prime] (hq_odd : Odd q)
    (hM : (mersenne (p' + 2) : lucasLehmerSeed_X s₁ q) = 0)
    (hdiv : (mersenne (p' + 2) : ℤ) ∣
      Nat.iterate (fun x : ℤ => x ^ 2 - 2) p' s₁) :
    orderOf (lucasLehmerSeed_alphaUnit s₁ q hq_odd) = 2 ^ (p' + 2) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow
  · exact Nat.prime_two
  · intro o
    have halpha := congr_arg
      (Units.coeHom (lucasLehmerSeed_X s₁ q) :
        (lucasLehmerSeed_X s₁ q)ˣ → lucasLehmerSeed_X s₁ q)
      (orderOf_dvd_iff_pow_eq_one.1 o)
    have hbad : (1 : ZMod q) = -1 := congr_arg Prod.fst <|
      halpha.symm.trans (lucasLehmerSeed_alpha_pow_neg_one p' s₁ q hq_odd hM hdiv)
    obtain ⟨k, hk⟩ := hq_odd
    have hq_gt : 2 < q := by
      have := (Fact.out : q.Prime).two_le
      omega
    have : Fact (2 < q) := ⟨hq_gt⟩
    exact ZMod.neg_one_ne_one hbad.symm
  · apply orderOf_dvd_iff_pow_eq_one.2
    apply Units.ext
    push_cast
    exact lucasLehmerSeed_alpha_pow_one p' s₁ q hq_odd hM hdiv

private theorem lucasLehmerSeed_order_ineq (p' : ℕ) (s₁ : ℤ)
    (hdiv : (mersenne (p' + 2) : ℤ) ∣
      Nat.iterate (fun x : ℤ => x ^ 2 - 2) p' s₁) :
    2 ^ (p' + 2) < Nat.minFac (mersenne (p' + 2)) ^ 2 := by
  let q := Nat.minFac (mersenne (p' + 2))
  have hq_prime : q.Prime := by
    dsimp [q]
    exact Nat.minFac_prime (ne_of_gt (one_lt_mersenne.2 (by omega)))
  have : Fact q.Prime := ⟨hq_prime⟩
  have hq_gt : 2 < q := by simpa [q] using lucasLehmerSeed_two_lt_minFac p'
  have hq_odd : Odd q := hq_prime.odd_of_ne_two (by omega)
  have hM : (mersenne (p' + 2) : lucasLehmerSeed_X s₁ q) = 0 := by
    simpa [q] using lucasLehmerSeed_mersenne_coe_X s₁ (p' + 2)
  calc
    2 ^ (p' + 2) = orderOf (lucasLehmerSeed_alphaUnit s₁ q hq_odd) :=
      (lucasLehmerSeed_order_alpha p' s₁ q hq_odd hM hdiv).symm
    _ ≤ Fintype.card (lucasLehmerSeed_X s₁ q)ˣ := orderOf_le_card_univ
    _ < q ^ 2 := lucasLehmerSeed_card_units_lt s₁ q (by omega)

private theorem lucasLehmerSeed_sufficiency (n : ℕ) (hn_ge : 3 ≤ n) (s₁ : ℤ) :
    (mersenne n : ℤ) ∣ Nat.iterate (fun x : ℤ => x ^ 2 - 2) (n - 2) s₁ →
      (mersenne n).Prime := by
  set p' := n - 2 with hp'
  clear_value p'
  obtain rfl : n = p' + 2 := by omega
  contrapose
  intro hnot_prime hdiv
  have horder := lucasLehmerSeed_order_ineq p' s₁ hdiv
  have hfactor := Nat.minFac_sq_le_self
    (mersenne_pos.2 (by omega : 0 < p' + 2)) hnot_prime
  have hcontra := lt_of_lt_of_le horder hfactor
  exact not_lt_of_ge (Nat.sub_le _ _) hcontra

private theorem lucasLehmerSeed_legendre_add_two (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hjac : jacobiSym (s₁ + 2) q = -1) : legendreSym q (s₁ + 2) = -1 := by
  calc
    legendreSym q (s₁ + 2) = jacobiSym (s₁ + 2) q :=
      jacobiSym.legendreSym.to_jacobiSym q (s₁ + 2)
    _ = -1 := hjac

private theorem lucasLehmerSeed_legendre_sub_two (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hjac : jacobiSym (s₁ - 2) q = 1) : legendreSym q (s₁ - 2) = 1 := by
  calc
    legendreSym q (s₁ - 2) = jacobiSym (s₁ - 2) q :=
      jacobiSym.legendreSym.to_jacobiSym q (s₁ - 2)
    _ = 1 := hjac

private theorem lucasLehmerSeed_legendre_D (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hplus : legendreSym q (s₁ + 2) = -1)
    (hminus : legendreSym q (s₁ - 2) = 1) :
    legendreSym q (s₁ ^ 2 - 4) = -1 := by
  rw [show s₁ ^ 2 - 4 = (s₁ + 2) * (s₁ - 2) by ring, legendreSym.mul, hplus, hminus]
  norm_num

private def lucasLehmerSeed_delta (s₁ : ℤ) (q : ℕ) : lucasLehmerSeed_X s₁ q := (0, 1)

@[simp] private theorem lucasLehmerSeed_delta_fst (s₁ : ℤ) (q : ℕ) :
    (lucasLehmerSeed_delta s₁ q).1 = 0 := rfl

@[simp] private theorem lucasLehmerSeed_delta_snd (s₁ : ℤ) (q : ℕ) :
    (lucasLehmerSeed_delta s₁ q).2 = 1 := rfl

@[simp] private theorem lucasLehmerSeed_delta_sq (s₁ : ℤ) (q : ℕ) :
    lucasLehmerSeed_delta s₁ q ^ 2 =
      (lucasLehmerSeed_D s₁ q : lucasLehmerSeed_X s₁ q) := by
  apply lucasLehmerSeed_X_ext
  · simp only [pow_two, lucasLehmerSeed_mul_fst, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd, lucasLehmerSeed_coeZMod_fst]
    ring
  · simp only [pow_two, lucasLehmerSeed_mul_snd, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd, lucasLehmerSeed_coeZMod_snd]
    ring

private theorem lucasLehmerSeed_delta_pow (s₁ : ℤ) (q i : ℕ) :
    lucasLehmerSeed_delta s₁ q ^ (2 * i + 1) =
      (lucasLehmerSeed_D s₁ q : lucasLehmerSeed_X s₁ q) ^ i *
        lucasLehmerSeed_delta s₁ q := by
  rw [pow_succ, pow_mul, lucasLehmerSeed_delta_sq]

private theorem lucasLehmerSeed_delta_pow_q (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) (hD : legendreSym q (s₁ ^ 2 - 4) = -1) :
    lucasLehmerSeed_delta s₁ q ^ q = -lucasLehmerSeed_delta s₁ q := by
  obtain ⟨k, rfl⟩ := hq_odd
  have hDpow : (lucasLehmerSeed_D s₁ (2 * k + 1)) ^ k = -1 := by
    have h := legendreSym.eq_pow (2 * k + 1) (s₁ ^ 2 - 4)
    rw [hD] at h
    have hhalf : (2 * k + 1) / 2 = k := by omega
    rw [hhalf] at h
    simpa [lucasLehmerSeed_D] using h.symm
  rw [lucasLehmerSeed_delta_pow]
  rw [← map_pow, hDpow, map_neg]
  simp

private theorem lucasLehmerSeed_alpha_eq (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    lucasLehmerSeed_alpha s₁ q =
      ((((s₁ : ZMod q) / (2 : ZMod q)) : ZMod q) : lucasLehmerSeed_X s₁ q) +
        (1 / 2 : ZMod q) * lucasLehmerSeed_delta s₁ q := by
  apply lucasLehmerSeed_X_ext
  · simp only [lucasLehmerSeed_alpha_fst, lucasLehmerSeed_add_fst,
      lucasLehmerSeed_coeZMod_fst, lucasLehmerSeed_mul_fst,
      lucasLehmerSeed_coeZMod_snd, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd]
    ring
  · simp only [lucasLehmerSeed_alpha_snd, lucasLehmerSeed_add_snd,
      lucasLehmerSeed_coeZMod_snd, lucasLehmerSeed_mul_snd,
      lucasLehmerSeed_coeZMod_fst, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd]
    ring

private theorem lucasLehmerSeed_beta_eq (s₁ : ℤ) (q : ℕ) [Fact q.Prime] :
    lucasLehmerSeed_beta s₁ q =
      ((((s₁ : ZMod q) / (2 : ZMod q)) : ZMod q) : lucasLehmerSeed_X s₁ q) +
        (((-(1 / 2 : ZMod q)) : ZMod q) : lucasLehmerSeed_X s₁ q) *
          lucasLehmerSeed_delta s₁ q := by
  apply lucasLehmerSeed_X_ext
  · simp only [lucasLehmerSeed_beta_fst, lucasLehmerSeed_add_fst,
      lucasLehmerSeed_coeZMod_fst, lucasLehmerSeed_mul_fst,
      lucasLehmerSeed_coeZMod_snd, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd]
    ring
  · simp only [lucasLehmerSeed_beta_snd, lucasLehmerSeed_add_snd,
      lucasLehmerSeed_coeZMod_snd, lucasLehmerSeed_mul_snd,
      lucasLehmerSeed_coeZMod_fst, lucasLehmerSeed_delta_fst,
      lucasLehmerSeed_delta_snd]
    ring

private theorem lucasLehmerSeed_coeZMod_pow_q (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (z : ZMod q) :
    (z : lucasLehmerSeed_X s₁ q) ^ q = (z : lucasLehmerSeed_X s₁ q) := by
  rw [← map_pow, ZMod.pow_card]

private theorem lucasLehmerSeed_alpha_pow_q (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) (hD : legendreSym q (s₁ ^ 2 - 4) = -1) :
    lucasLehmerSeed_alpha s₁ q ^ q = lucasLehmerSeed_beta s₁ q := by
  rw [lucasLehmerSeed_alpha_eq, add_pow_expChar, mul_pow,
    lucasLehmerSeed_coeZMod_pow_q s₁ q ((s₁ : ZMod q) / 2),
    lucasLehmerSeed_coeZMod_pow_q s₁ q (1 / 2),
    lucasLehmerSeed_delta_pow_q s₁ q hq_odd hD, lucasLehmerSeed_beta_eq]
  rw [map_neg]
  ring

private theorem lucasLehmerSeed_one_add_alpha_pow_q_succ
    (s₁ : ℤ) (q : ℕ) [Fact q.Prime] (hq_odd : Odd q)
    (hD : legendreSym q (s₁ ^ 2 - 4) = -1) :
    (1 + lucasLehmerSeed_alpha s₁ q) ^ (q + 1) =
      (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
  rw [pow_succ, add_pow_expChar, one_pow,
    lucasLehmerSeed_alpha_pow_q s₁ q hq_odd hD]
  rw [show (1 + lucasLehmerSeed_beta s₁ q) *
      (1 + lucasLehmerSeed_alpha s₁ q) =
      2 + (lucasLehmerSeed_alpha s₁ q + lucasLehmerSeed_beta s₁ q) by
        calc
          (1 + lucasLehmerSeed_beta s₁ q) *
              (1 + lucasLehmerSeed_alpha s₁ q) =
              1 + lucasLehmerSeed_alpha s₁ q + lucasLehmerSeed_beta s₁ q +
                lucasLehmerSeed_beta s₁ q * lucasLehmerSeed_alpha s₁ q := by ring
          _ = 2 + (lucasLehmerSeed_alpha s₁ q + lucasLehmerSeed_beta s₁ q) := by
            rw [lucasLehmerSeed_beta_mul_alpha s₁ q hq_odd]
            ring]
  rw [lucasLehmerSeed_alpha_add_beta s₁ q hq_odd]
  ring

private theorem lucasLehmerSeed_one_add_alpha_sq (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) :
    (1 + lucasLehmerSeed_alpha s₁ q) ^ 2 =
      lucasLehmerSeed_alpha s₁ q *
        (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
  calc
    (1 + lucasLehmerSeed_alpha s₁ q) ^ 2 =
        lucasLehmerSeed_alpha s₁ q ^ 2 + 2 * lucasLehmerSeed_alpha s₁ q + 1 := by
      ring
    _ = lucasLehmerSeed_alpha s₁ q ^ 2 + 2 * lucasLehmerSeed_alpha s₁ q +
        lucasLehmerSeed_alpha s₁ q * lucasLehmerSeed_beta s₁ q := by
      rw [lucasLehmerSeed_alpha_mul_beta s₁ q hq_odd]
    _ = lucasLehmerSeed_alpha s₁ q *
        (lucasLehmerSeed_alpha s₁ q + lucasLehmerSeed_beta s₁ q + 2) := by ring
    _ = lucasLehmerSeed_alpha s₁ q *
        (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
      rw [lucasLehmerSeed_alpha_add_beta s₁ q hq_odd]

private theorem lucasLehmerSeed_alpha_pow_half (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) (hD : legendreSym q (s₁ ^ 2 - 4) = -1)
    (hplus : legendreSym q (s₁ + 2) = -1) :
    lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) = -1 := by
  have htwo : 2 * ((q + 1) / 2) = q + 1 := Nat.two_mul_div_two_of_even hq_odd.add_one
  have htrace :
      lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) *
          (s₁ + 2 : lucasLehmerSeed_X s₁ q) ^ ((q + 1) / 2) =
        (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
    calc
      lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) *
          (s₁ + 2 : lucasLehmerSeed_X s₁ q) ^ ((q + 1) / 2) =
          (lucasLehmerSeed_alpha s₁ q *
            (s₁ + 2 : lucasLehmerSeed_X s₁ q)) ^ ((q + 1) / 2) :=
        (mul_pow _ _ _).symm
      _ = ((1 + lucasLehmerSeed_alpha s₁ q) ^ 2) ^ ((q + 1) / 2) := by
        rw [lucasLehmerSeed_one_add_alpha_sq s₁ q hq_odd]
      _ = (1 + lucasLehmerSeed_alpha s₁ q) ^ (q + 1) := by
        rw [← pow_mul, htwo]
      _ = (s₁ + 2 : lucasLehmerSeed_X s₁ q) :=
        lucasLehmerSeed_one_add_alpha_pow_q_succ s₁ q hq_odd hD
  have hplus_pow : ((s₁ + 2 : ℤ) : ZMod q) ^ (q / 2) = -1 := by
    have h := legendreSym.eq_pow q (s₁ + 2)
    rw [hplus] at h
    simpa using h.symm
  obtain ⟨k, hk⟩ := hq_odd
  have hhalf : (q + 1) / 2 = q / 2 + 1 := by omega
  have hcast :
      (((s₁ + 2 : ℤ) : ZMod q) : lucasLehmerSeed_X s₁ q) =
        (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
    rw [map_intCast]
    push_cast
    rfl
  have hbase_pow :
      (s₁ + 2 : lucasLehmerSeed_X s₁ q) ^ ((q + 1) / 2) =
        -(s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
    rw [← hcast, hhalf, pow_succ, ← map_pow, hplus_pow, map_neg]
    simp
  rw [hbase_pow] at htrace
  have hbase_ne : ((s₁ + 2 : ℤ) : ZMod q) ≠ 0 := by
    intro hz
    have := (legendreSym.eq_zero_iff q (s₁ + 2)).2 hz
    rw [hplus] at this
    norm_num at this
  have hunit_z : IsUnit (((s₁ + 2 : ℤ) : ZMod q)) := isUnit_iff_ne_zero.mpr hbase_ne
  have hunit : IsUnit (s₁ + 2 : lucasLehmerSeed_X s₁ q) := by
    rw [← hcast]
    exact hunit_z.map (ZMod.castHom dvd_rfl (lucasLehmerSeed_X s₁ q))
  have hcancel := hunit.mul_right_cancel <| show
    (lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) * -1) *
        (s₁ + 2 : lucasLehmerSeed_X s₁ q) =
      1 * (s₁ + 2 : lucasLehmerSeed_X s₁ q) by
        calc
          _ = lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) *
              -(s₁ + 2 : lucasLehmerSeed_X s₁ q) := by ring
          _ = (s₁ + 2 : lucasLehmerSeed_X s₁ q) := htrace
          _ = _ := by ring
  calc
    lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) =
        -(lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) * -1) := by ring
    _ = -1 := by rw [hcancel]

private theorem lucasLehmerSeed_trace_zero (s₁ : ℤ) (q : ℕ) [Fact q.Prime]
    (hq_odd : Odd q) (hD : legendreSym q (s₁ ^ 2 - 4) = -1)
    (hplus : legendreSym q (s₁ + 2) = -1) (hq4 : 4 ∣ q + 1) :
    lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 4) +
      lucasLehmerSeed_beta s₁ q ^ ((q + 1) / 4) = 0 := by
  have hmul : lucasLehmerSeed_alpha s₁ q ^ ((q + 1) / 2) *
      lucasLehmerSeed_beta s₁ q ^ ((q + 1) / 4) =
      -lucasLehmerSeed_beta s₁ q ^ ((q + 1) / 4) := by
    rw [lucasLehmerSeed_alpha_pow_half s₁ q hq_odd hD hplus]
    ring
  have hsplit : (q + 1) / 2 = (q + 1) / 4 + (q + 1) / 4 := by
    obtain ⟨k, hk⟩ := hq4
    omega
  rw [hsplit, pow_add, mul_assoc, ← mul_pow,
    lucasLehmerSeed_alpha_mul_beta s₁ q hq_odd, one_pow, mul_one] at hmul
  rw [hmul]
  ring

private theorem lucasLehmerSeed_necessity (n : ℕ) (hn_odd : Odd n) (hn_ge : 3 ≤ n)
    (s₁ : ℤ)
    (hjac : jacobiSym (s₁ + 2) (mersenne n) = -1 ∧
      jacobiSym (s₁ - 2) (mersenne n) = 1)
    (hprime : (mersenne n).Prime) :
    (mersenne n : ℤ) ∣ Nat.iterate (fun x : ℤ => x ^ 2 - 2) (n - 2) s₁ := by
  set p' := n - 2 with hp'
  clear_value p'
  obtain rfl : n = p' + 2 := by omega
  have : Fact (mersenne (p' + 2)).Prime := ⟨hprime⟩
  have hq_odd : Odd (mersenne (p' + 2)) := mersenne_odd.2 (by omega)
  have hplus := lucasLehmerSeed_legendre_add_two s₁ (mersenne (p' + 2)) hjac.1
  have hminus := lucasLehmerSeed_legendre_sub_two s₁ (mersenne (p' + 2)) hjac.2
  have hD := lucasLehmerSeed_legendre_D s₁ (mersenne (p' + 2)) hplus hminus
  have htrace := lucasLehmerSeed_trace_zero s₁ (mersenne (p' + 2)) hq_odd hD hplus
    (by simp [succ_mersenne, pow_add])
  rw [succ_mersenne, pow_add, show 2 ^ 2 = 4 by norm_num,
    mul_div_cancel_right₀ _ (by norm_num)] at htrace
  have hclosed := lucasLehmerSeed_closedForm s₁ (mersenne (p' + 2)) hq_odd p'
  have hzero :
      ((Nat.iterate (fun x : ℤ => x ^ 2 - 2) p' s₁ : ℤ) :
        ZMod (mersenne (p' + 2))) = 0 := by
    rw [← lucasLehmerSeed_intCast_fst
      (s₁ := s₁) (q := mersenne (p' + 2))]
    rw [hclosed, htrace]
    simp
  simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using hzero

/--
**Lucas–Lehmer test with a general seed.** Let $n \ge 3$ be an odd natural number, let
$M_n = 2^n - 1$, and let $s_1$ be an integer. Define $s_{k+1} = s_k^2 - 2$ for $k \ge 1$. If the
Jacobi symbols satisfy $\left(\frac{s_1 + 2}{M_n}\right) = -1$ and
$\left(\frac{s_1 - 2}{M_n}\right) = 1$, then $M_n$ is prime if and only if $M_n$ divides
$s_{n-1}$.

In the terminology of Roettger and Williams, such a seed $s_1$ is acceptable: the Lucas–Lehmer
test started at $s_1$ decides the primality of $M_n$ (their Assertion A).

Proof: Following Mathlib's Lucas-Lehmer order argument, sufficiency uses a quadratic extension
and the least prime factor; necessity uses the Jacobi conditions and Frobenius conjugation as in
Lehmer (1930) and Roettger-Williams (2025).

Proves `Wanted` entry `acceptableSeed_of_jacobi`.

Source: E. L. Roettger and H. C. Williams, "Some Remarks Concerning the
Lucas-Lehmer Primality Test," Journal of Integer Sequences 28 (2025),
Article 25.2.5, Theorem (label acceptableseed), lines 814–819; Assertion A
(label assertionA) at lines 187–190,
https://cs.uwaterloo.ca/journals/JIS/VOL28/Roettger/roettger15.tex
-/
public theorem acceptableSeed_of_jacobi
    (n : ℕ) (hn_odd : Odd n) (hn_ge : 3 ≤ n) (s₁ : ℤ) :
    jacobiSym (s₁ + 2) (mersenne n) = -1 ∧
      jacobiSym (s₁ - 2) (mersenne n) = 1 →
        (Nat.Prime (mersenne n) ↔
          (mersenne n : ℤ) ∣ Nat.iterate (fun x : ℤ => x ^ 2 - 2) (n - 2) s₁) := by
  intro hjac
  constructor
  · exact lucasLehmerSeed_necessity n hn_odd hn_ge s₁ hjac
  · exact lucasLehmerSeed_sufficiency n hn_ge s₁

end MetaMathlibExt
