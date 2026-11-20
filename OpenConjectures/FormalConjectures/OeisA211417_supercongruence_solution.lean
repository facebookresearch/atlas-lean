/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/OEIS/211417.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

import Mathlib
















import FormalConjecturesUtil












namespace OeisA211417






def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

open Nat Int Finset

private lemma factorial_ratio_floor_ineq (n d : ℕ) :
    15 * n / d + 10 * n / d + 6 * n / d ≤ 30 * n / d + n / d := by
  by_cases hd0 : d = 0
  · simp [hd0]
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  have decomp (c : ℕ) : c * n / d = c * (n / d) + c * (n % d) / d := by
    rw [show c * n = c * (n % d) + d * (c * (n / d)) by
      nth_rewrite 1 [← Nat.mod_add_div n d]
      ring]
    rw [Nat.add_mul_div_left _ _ hd]
    omega
  have hr : n % d < d := Nat.mod_lt n hd
  have residual :
      15 * (n % d) / d + 10 * (n % d) / d + 6 * (n % d) / d ≤
        30 * (n % d) / d := by
    let j := 30 * (n % d) / d
    have hj : j < 30 := by
      dsimp [j]
      rw [Nat.div_lt_iff_lt_mul hd]
      omega
    have hbase : j * d ≤ 30 * (n % d) ∧ 30 * (n % d) < (j + 1) * d := by
      constructor
      · dsimp [j]
        simpa [Nat.mul_comm] using Nat.mul_div_le (30 * (n % d)) d
      · have h :=
          (Nat.div_lt_iff_lt_mul hd).1
            (Nat.lt_succ_self (30 * (n % d) / d))
        simpa [j] using h
    have h15 : 15 * (n % d) / d ≤ j / 2 := by
      apply (Nat.lt_add_one_iff).1
      rw [Nat.div_lt_iff_lt_mul hd]
      interval_cases j <;> omega
    have h10 : 10 * (n % d) / d ≤ j / 3 := by
      apply (Nat.lt_add_one_iff).1
      rw [Nat.div_lt_iff_lt_mul hd]
      interval_cases j <;> omega
    have h6 : 6 * (n % d) / d ≤ j / 5 := by
      apply (Nat.lt_add_one_iff).1
      rw [Nat.div_lt_iff_lt_mul hd]
      interval_cases j <;> omega
    have hjineq : j / 2 + j / 3 + j / 5 ≤ j := by
      interval_cases j <;> decide
    omega
  rw [decomp 15, decomp 10, decomp 6, decomp 30]
  omega

private lemma factorial_ratio_integral (n : ℕ) :
    Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n) ∣
      Nat.factorial (30 * n) * Nat.factorial n := by
  apply (Nat.factorization_le_iff_dvd (by positivity) (by positivity)).mp
  intro q
  by_cases hq : q.Prime
  · let b := Nat.log q (30 * n) + 1
    have hlog : Nat.log q (30 * n) < b := Nat.lt_succ_self _
    have h15 : Nat.log q (15 * n) < b :=
      lt_of_le_of_lt (Nat.log_mono_right (by omega)) hlog
    have h10 : Nat.log q (10 * n) < b :=
      lt_of_le_of_lt (Nat.log_mono_right (by omega)) hlog
    have h6 : Nat.log q (6 * n) < b :=
      lt_of_le_of_lt (Nat.log_mono_right (by omega)) hlog
    have hn : Nat.log q n < b :=
      lt_of_le_of_lt (Nat.log_mono_right (by omega)) hlog
    rw [Nat.factorization_mul
          (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
          (Nat.factorial_ne_zero _),
      Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
      Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
    simp only [Nat.factorization_factorial hq h15,
      Nat.factorization_factorial hq h10, Nat.factorization_factorial hq h6,
      Nat.factorization_factorial hq hlog, Nat.factorization_factorial hq hn,
      Pi.add_apply, Finsupp.coe_add]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    exact factorial_ratio_floor_ineq n (q ^ i)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

private lemma factorial_ratio_mul_a (n : ℕ) :
    (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n)) * a n =
      Nat.factorial (30 * n) * Nat.factorial n := by
  rw [a, Nat.mul_div_cancel' (factorial_ratio_integral n)]

private lemma a_mul_choose (n : ℕ) :
    a n * Nat.choose (6 * n) n =
      Nat.choose (30 * n) (15 * n) * Nat.choose (15 * n) (10 * n) := by
  apply Nat.cast_injective (R := ℚ)
  have eA : (a n : ℚ) =
      ((Nat.factorial (30 * n) * Nat.factorial n : ℕ) : ℚ) /
        ((Nat.factorial (15 * n) * Nat.factorial (10 * n) *
          Nat.factorial (6 * n) : ℕ) : ℚ) := by
    apply (eq_div_iff (by positivity)).2
    norm_cast
    nlinarith [factorial_ratio_mul_a n]
  have e6 : (Nat.choose (6 * n) n : ℚ) = (Nat.factorial (6 * n) : ℚ) /
      ((Nat.factorial n : ℚ) * (Nat.factorial (5 * n) : ℚ)) := by
    apply (eq_div_iff (by positivity)).2
    norm_cast
    simpa [show 6 * n - n = 5 * n by omega, mul_assoc] using
      Nat.choose_mul_factorial_mul_factorial (show n ≤ 6 * n by omega)
  have e30 : (Nat.choose (30 * n) (15 * n) : ℚ) =
      (Nat.factorial (30 * n) : ℚ) /
        ((Nat.factorial (15 * n) : ℚ) * (Nat.factorial (15 * n) : ℚ)) := by
    apply (eq_div_iff (by positivity)).2
    norm_cast
    simpa [show 30 * n - 15 * n = 15 * n by omega, mul_assoc] using
      Nat.choose_mul_factorial_mul_factorial (show 15 * n ≤ 30 * n by omega)
  have e15 : (Nat.choose (15 * n) (10 * n) : ℚ) =
      (Nat.factorial (15 * n) : ℚ) /
        ((Nat.factorial (10 * n) : ℚ) * (Nat.factorial (5 * n) : ℚ)) := by
    apply (eq_div_iff (by positivity)).2
    norm_cast
    simpa [show 15 * n - 10 * n = 5 * n by omega, mul_assoc] using
      Nat.choose_mul_factorial_mul_factorial (show 10 * n ≤ 15 * n by omega)
  push_cast
  rw [eA, e6, e30, e15]
  field_simp
  push_cast
  ring

private def unitProd (p n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, if p ∣ i + 1 then 1 else i + 1

private lemma prod_dvd_part (p n : ℕ) (hp0 : 0 < p) :
    (∏ i ∈ Finset.range n, if p ∣ i + 1 then i + 1 else 1) =
      p ^ (n / p) * Nat.factorial (n / p) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      by_cases h : p ∣ n + 1
      · have hs := Nat.succ_div_of_dvd h
        have hn : n + 1 = p * (n / p + 1) := by
          rw [← hs]
          exact (Nat.mul_div_cancel' h).symm
        simp only [h, if_pos]
        rw [hs, hn, pow_succ, Nat.factorial_succ]
        ring
      · rw [Nat.succ_div_of_not_dvd h]
        simp [h]

private lemma factorial_eq_dvd_part_mul_unitProd (p n : ℕ) (hp0 : 0 < p) :
    Nat.factorial n = p ^ (n / p) * Nat.factorial (n / p) * unitProd p n := by
  rw [Nat.factorial_eq_prod_range_add_one]
  calc
    (∏ i ∈ Finset.range n, (i + 1)) =
        ∏ i ∈ Finset.range n,
          (if p ∣ i + 1 then i + 1 else 1) *
            (if p ∣ i + 1 then 1 else i + 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases h : p ∣ i + 1 <;> simp [h]
    _ = (∏ i ∈ Finset.range n, if p ∣ i + 1 then i + 1 else 1) *
          unitProd p n := by rw [unitProd, Finset.prod_mul_distrib]
    _ = p ^ (n / p) * Nat.factorial (n / p) * unitProd p n := by
      rw [prod_dvd_part p n hp0]

private lemma choose_mul_unitProd_relation
    (p r c d : ℕ) (hp0 : 0 < p) (hdc : d ≤ c) :
    Nat.choose (c * (p * r)) (d * (p * r)) *
        unitProd p (d * (p * r)) * unitProd p ((c - d) * (p * r)) =
      Nat.choose (c * r) (d * r) * unitProd p (c * (p * r)) := by
  have hbig := Nat.choose_mul_factorial_mul_factorial
    (show d * (p * r) ≤ c * (p * r) by gcongr)
  have hsmall := Nat.choose_mul_factorial_mul_factorial
    (show d * r ≤ c * r by gcongr)
  have hN := factorial_eq_dvd_part_mul_unitProd p (c * (p * r)) hp0
  have hD := factorial_eq_dvd_part_mul_unitProd p (d * (p * r)) hp0
  have hE := factorial_eq_dvd_part_mul_unitProd p ((c - d) * (p * r)) hp0
  have hdivN : c * (p * r) / p = c * r := by
    rw [show c * (p * r) = (c * r) * p by ring, Nat.mul_div_left _ hp0]
  have hdivD : d * (p * r) / p = d * r := by
    rw [show d * (p * r) = (d * r) * p by ring, Nat.mul_div_left _ hp0]
  have hdivE : (c - d) * (p * r) / p = (c - d) * r := by
    rw [show (c - d) * (p * r) = ((c - d) * r) * p by ring,
      Nat.mul_div_left _ hp0]
  have hsub : c * (p * r) - d * (p * r) = (c - d) * (p * r) := by
    rw [Nat.sub_mul]
  have hsub' : c * r - d * r = (c - d) * r := by rw [Nat.sub_mul]
  rw [hsub] at hbig
  rw [hsub'] at hsmall
  rw [hN, hD, hE, hdivN, hdivD, hdivE] at hbig
  have hexp : c * r = d * r + (c - d) * r := by
    have hc : d + (c - d) = c := Nat.add_sub_of_le hdc
    calc
      c * r = (d + (c - d)) * r := congrArg (fun x => x * r) hc.symm
      _ = d * r + (c - d) * r := Nat.add_mul _ _ _
  rw [hexp, pow_add] at hbig
  have hfac : Nat.factorial (c * r) =
      Nat.choose (c * r) (d * r) * Nat.factorial (d * r) *
        Nat.factorial ((c - d) * r) := hsmall.symm
  rw [← hexp, hfac] at hbig
  let F := p ^ (d * r) * Nat.factorial (d * r) *
    (p ^ ((c - d) * r) * Nat.factorial ((c - d) * r))
  have hbig' :
      F * (Nat.choose (c * (p * r)) (d * (p * r)) *
        unitProd p (d * (p * r)) * unitProd p ((c - d) * (p * r))) =
      F * (Nat.choose (c * r) (d * r) * unitProd p (c * (p * r))) := by
    dsimp [F]
    calc
      _ = Nat.choose (c * (p * r)) (d * (p * r)) *
          (p ^ (d * r) * Nat.factorial (d * r) * unitProd p (d * (p * r))) *
          (p ^ ((c - d) * r) * Nat.factorial ((c - d) * r) *
            unitProd p ((c - d) * (p * r))) := by ring
      _ = p ^ (d * r) * p ^ ((c - d) * r) *
          (Nat.choose (c * r) (d * r) * Nat.factorial (d * r) *
            Nat.factorial ((c - d) * r)) * unitProd p (c * (p * r)) := hbig
      _ = _ := by ring
  have hpos : 0 < F := by dsimp [F]; positivity
  exact Nat.eq_of_mul_eq_mul_left hpos hbig'

private lemma sum_units_sq_zmod (q : ℕ) [NeZero q]
    (h2 : Nat.Coprime 2 q) (h3 : Nat.Coprime 3 q) :
    (∑ u : (ZMod q)ˣ, (u : ZMod q) ^ 2) = 0 := by
  let u2 : (ZMod q)ˣ := ZMod.unitOfCoprime 2 h2
  let S : ZMod q := ∑ u : (ZMod q)ˣ, (u : ZMod q) ^ 2
  have hp := Equiv.sum_comp (Equiv.mulLeft u2)
    (fun u : (ZMod q)ˣ => (u : ZMod q) ^ 2)
  have heq : (4 : ZMod q) * S = S := by
    dsimp [S, u2] at hp ⊢
    rw [show (4 : ZMod q) = (2 : ZMod q) ^ 2 by norm_num]
    simpa [mul_pow, ← Finset.mul_sum] using hp
  have hzero : (3 : ZMod q) * S = 0 := by
    calc
      3 * S = 4 * S - S := by ring
      _ = 0 := by rw [heq]; ring
  let u3 : (ZMod q)ˣ := ZMod.unitOfCoprime 3 h3
  calc
    S = (↑u3⁻¹ : ZMod q) * ((u3 : ZMod q) * S) := by simp
    _ = 0 := by rw [show (u3 : ZMod q) = 3 by rfl, hzero, mul_zero]

private def unitIndex (p k : ℕ) := {i : Fin (p ^ k) // ¬p ∣ i.val}

private noncomputable instance unitIndexFintype (p k : ℕ) : Fintype (unitIndex p k) := by
  unfold unitIndex
  infer_instance

private def unitIndexEquiv (p k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    unitIndex p k ≃ (ZMod (p ^ k))ˣ := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine
    { toFun := fun i =>
        ZMod.unitOfCoprime i.val (hp.coprime_pow_of_not_dvd i.prop)
      invFun := fun u => ⟨⟨(u : ZMod (p ^ k)).val, ZMod.val_lt _⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro hdiv
    have hc := ZMod.val_coe_unit_coprime u
    apply hp.not_dvd_one
    rw [← hc.gcd_eq_one]
    exact Nat.dvd_gcd hdiv (dvd_pow_self p hk.ne')
  · intro i
    apply Subtype.ext
    apply Fin.ext
    dsimp
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.val.isLt]
  · intro u
    apply Units.ext
    dsimp
    exact ZMod.natCast_zmod_val (u : ZMod (p ^ k))

private lemma sum_unitIndex_inv_sq (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 0 < k) :
    (∑ i : unitIndex p k, ((i.val : ZMod (p ^ k))⁻¹) ^ 2) = 0 := by
  letI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have h2p : Nat.Coprime 2 p := ((hp.coprime_iff_not_dvd).2 (by
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega)).symm
  have h3p : Nat.Coprime 3 p := ((hp.coprime_iff_not_dvd).2 (by
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega)).symm
  have hs := sum_units_sq_zmod (p ^ k) (h2p.pow_right k) (h3p.pow_right k)
  rw [← Equiv.sum_comp (Equiv.inv ((ZMod (p ^ k))ˣ))
    (fun u : (ZMod (p ^ k))ˣ => (u : ZMod (p ^ k)) ^ 2)] at hs
  change (∑ u : (ZMod (p ^ k))ˣ,
    (((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) ^ 2)) = 0 at hs
  let e := unitIndexEquiv p k hp hk
  rw [← Equiv.sum_comp e
    (fun u : (ZMod (p ^ k))ˣ => ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) ^ 2)] at hs
  dsimp [e, unitIndexEquiv] at hs
  rw [show (∑ i : unitIndex p k, ((i.val : ZMod (p ^ k))⁻¹) ^ 2) =
      ∑ i : unitIndex p k,
        (((ZMod.unitOfCoprime i.val
          (hp.coprime_pow_of_not_dvd i.prop))⁻¹ : (ZMod (p ^ k))ˣ) :
            ZMod (p ^ k)) ^ 2 by
    apply Finset.sum_congr rfl
    intro i hi
    apply congrArg (fun x : ZMod (p ^ k) => x⁻¹ ^ 2)
    exact (ZMod.coe_unitOfCoprime i.val
      (hp.coprime_pow_of_not_dvd i.prop)).symm]
  exact hs

private lemma prime_not_dvd_unitProd (p n : ℕ) (hp : p.Prime) :
    ¬p ∣ unitProd p n := by
  rw [unitProd]
  apply (hp.prime : _root_.Prime p).not_dvd_finsetProd
  intro i hi
  by_cases h : p ∣ i + 1
  · simp [h, hp.not_dvd_one]
  · simpa [h]

private noncomputable instance unitIndexDecidableEq (p k : ℕ) :
    DecidableEq (unitIndex p k) := Classical.decEq _

private lemma block_cofactor_dvd (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 0 < k) :
    p ^ k ∣ ∑ i : unitIndex p k,
      ∏ j ∈ (Finset.univ.erase i), j.val * (p ^ k - j.val) := by
  classical
  let q := p ^ k
  let A : unitIndex p k → ℕ := fun i => i.val * (q - i.val)
  let P : ℕ := ∏ i : unitIndex p k, A i
  change q ∣ ∑ i : unitIndex p k, ∏ j ∈ (Finset.univ.erase i), A j
  rw [← ZMod.natCast_eq_zero_iff]
  have hA (i : unitIndex p k) :
      (A i : ZMod q) = -(i.val : ZMod q) ^ 2 := by
    dsimp only [A]
    push_cast
    rw [Nat.cast_sub (by dsimp [q]; omega), ZMod.natCast_self]
    ring
  have hxi (i : unitIndex p k) : IsUnit (i.val : ZMod q) :=
    (ZMod.isUnit_iff_coprime i.val q).2
      (hp.coprime_pow_of_not_dvd i.prop)
  have hunit (i : unitIndex p k) : IsUnit (A i : ZMod q) := by
    rw [hA]
    exact ((hxi i).pow 2).neg
  have hterm (i : unitIndex p k) :
      (∏ j ∈ Finset.univ.erase i, (A j : ZMod q)) =
        (P : ZMod q) * (A i : ZMod q)⁻¹ := by
    have he := Finset.prod_erase_mul
      (Finset.univ : Finset (unitIndex p k))
      (fun j => (A j : ZMod q)) (Finset.mem_univ i)
    dsimp only [P]
    push_cast
    rw [← he, mul_assoc, ZMod.mul_inv_of_unit _ (hunit i), mul_one]
  change
    ((↑(∑ i : unitIndex p k, ∏ j ∈ (Finset.univ.erase i), A j) : ZMod q)) = 0
  push_cast
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hinv (i : unitIndex p k) :
      (A i : ZMod q)⁻¹ = -((i.val : ZMod q)⁻¹) ^ 2 := by
    rw [hA]
    apply ZMod.inv_eq_of_mul_eq_one
    calc
      (-((i.val : ZMod q) ^ 2)) * (-((i.val : ZMod q)⁻¹) ^ 2) =
          ((i.val : ZMod q) * (i.val : ZMod q)⁻¹) ^ 2 := by ring
      _ = 1 := by rw [ZMod.mul_inv_of_unit _ (hxi i)]; simp
  simp_rw [hinv]
  rw [Finset.sum_neg_distrib]
  have hs := sum_unitIndex_inv_sq p k hp hp5 hk
  change (∑ i : unitIndex p k, ((i.val : ZMod q)⁻¹) ^ 2) = 0 at hs
  rw [hs]
  simp

private noncomputable def blockProd (p k t : ℕ) : ℕ :=
  ∏ i : unitIndex p k, (t * p ^ k + i.val)

private lemma prod_add_squareZero {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (A : ι → R) (C E : R) (hE : E * E = 0) :
    (∏ i ∈ s, (A i + C * E)) =
      (∏ i ∈ s, A i) + C * E * (∑ i ∈ s, ∏ j ∈ s.erase i, A j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ih]
    have hs : (∑ i ∈ insert a s, ∏ j ∈ (insert a s).erase i, A j) =
        (∏ j ∈ s, A j) + A a * (∑ i ∈ s, ∏ j ∈ s.erase i, A j) := by
      rw [Finset.sum_insert ha]
      congr 1
      · simp [Finset.erase_insert, ha]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.erase_insert_of_ne (by rintro rfl; exact ha hi),
          Finset.prod_insert]
        exact fun h => ha (Finset.mem_of_mem_erase h)
    rw [Finset.prod_insert ha, hs]
    ring_nf
    rw [show E ^ 2 = 0 by simpa [pow_two] using hE]
    simp

private def unitIndexNeg (p k : ℕ) (hp0 : 0 < p) (hk : 0 < k) :
    unitIndex p k ≃ unitIndex p k := by
  let q := p ^ k
  have hq : 0 < q := pow_pos hp0 k
  have hpq : p ∣ q := dvd_pow_self p hk.ne'
  refine
    { toFun := fun i => ⟨⟨q - i.1.1, by
          have hi0 : 0 < i.1.1 := by
            by_contra h
            apply i.prop
            have hz : i.1.1 = 0 := by omega
            simpa [hz]
          omega⟩, ?_⟩
      invFun := fun i => ⟨⟨q - i.1.1, by
          have hi0 : 0 < i.1.1 := by
            by_contra h
            apply i.prop
            have hz : i.1.1 = 0 := by omega
            simpa [hz]
          omega⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro hdiv
    apply i.prop
    have hsub := Nat.dvd_sub hpq hdiv
    change p ∣ q - (q - i.1.1) at hsub
    rw [Nat.sub_sub_self (by omega)] at hsub
    exact hsub
  · intro hdiv
    apply i.prop
    have hsub := Nat.dvd_sub hpq hdiv
    change p ∣ q - (q - i.1.1) at hsub
    rw [Nat.sub_sub_self (by omega)] at hsub
    exact hsub
  · intro i
    apply Subtype.ext
    apply Fin.ext
    change q - (q - i.1.1) = i.1.1
    exact Nat.sub_sub_self (by omega)
  · intro i
    apply Subtype.ext
    apply Fin.ext
    change q - (q - i.1.1) = i.1.1
    exact Nat.sub_sub_self (by omega)

private lemma blockProd_sq_eq_prod_pair
    (p k t : ℕ) (hp0 : 0 < p) (hk : 0 < k) :
    blockProd p k t ^ 2 =
      ∏ i : unitIndex p k,
        (t * p ^ k + i.val) * (t * p ^ k + (p ^ k - i.val)) := by
  classical
  let e := unitIndexNeg p k hp0 hk
  let f : unitIndex p k → ℕ := fun i => t * p ^ k + i.val
  calc
    blockProd p k t ^ 2 = (∏ i : unitIndex p k, f i) * ∏ i : unitIndex p k, f i := by
      simp [blockProd, f, pow_two]
    _ = (∏ i : unitIndex p k, f i) * ∏ i : unitIndex p k, f (e i) := by
      rw [Equiv.prod_comp e f]
    _ = ∏ i : unitIndex p k, f i * f (e i) := Finset.prod_mul_distrib.symm
    _ = ∏ i : unitIndex p k,
        (t * p ^ k + i.val) * (t * p ^ k + (p ^ k - i.val)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rfl

private lemma blockProd_sq_congr
    (p k t : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    (blockProd p k t : ZMod ((p ^ k) ^ 3)) ^ 2 =
      (blockProd p k 0 : ZMod ((p ^ k) ^ 3)) ^ 2 := by
  classical
  let q := p ^ k
  let N := q ^ 3
  let A : unitIndex p k → ZMod N := fun i =>
    (i.val * (q - i.val) : ℕ)
  let C : ZMod N := t * (t + 1)
  let E : ZMod N := (q ^ 2 : ℕ)
  have hE : E * E = 0 := by
    change ((q ^ 2 : ℕ) : ZMod N) * (q ^ 2 : ℕ) = 0
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    use q
    dsimp [N]
    ring
  have hpairNat (i : unitIndex p k) :
      (t * q + i.val) * (t * q + (q - i.val)) =
        i.val * (q - i.val) + t * (t + 1) * q ^ 2 := by
    have hi : i.val ≤ q := by dsimp [q]; omega
    have hsum : q - i.val + i.val = q := Nat.sub_add_cancel hi
    calc
      _ = (t * (q - i.val + i.val) + i.val) *
          (t * (q - i.val + i.val) + (q - i.val)) := by rw [hsum]
      _ = i.val * (q - i.val) +
          t * (t + 1) * (q - i.val + i.val) ^ 2 := by ring
      _ = _ := by rw [hsum]
  have hpair (i : unitIndex p k) :
      (((t * q + i.val) * (t * q + (q - i.val)) : ℕ) : ZMod N) =
        A i + C * E := by
    rw [hpairNat]
    simp only [A, C, E]
    push_cast
    rfl
  have hexpand := prod_add_squareZero
    (Finset.univ : Finset (unitIndex p k)) A C E hE
  have hcof := block_cofactor_dvd p k hp hp5 hk
  change q ∣ ∑ i : unitIndex p k,
      ∏ j ∈ (Finset.univ.erase i), j.val * (q - j.val) at hcof
  obtain ⟨m, hm⟩ := hcof
  have hcast :
      (((∑ i : unitIndex p k,
        ∏ j ∈ (Finset.univ.erase i), j.val * (q - j.val) : ℕ)) : ZMod N) =
        ∑ i : unitIndex p k, ∏ j ∈ (Finset.univ.erase i), A j := by
    simp only [A]
    push_cast
    rfl
  have hsum :
      (∑ i : unitIndex p k, ∏ j ∈ (Finset.univ.erase i), A j) =
        (q : ZMod N) * (m : ZMod N) := by
    rw [← hcast, hm]
    push_cast
    rfl
  have hcorr : C * E *
      (∑ i : unitIndex p k, ∏ j ∈ (Finset.univ.erase i), A j) = 0 := by
    rw [hsum]
    have hq3 : ((q ^ 3 : ℕ) : ZMod N) = 0 := by
      dsimp [N]
      exact ZMod.natCast_self _
    calc
      C * E * ((q : ZMod N) * (m : ZMod N)) =
          C * (m : ZMod N) * ((q : ZMod N) ^ 3) := by
        simp only [E]
        push_cast
        ring
      _ = 0 := by rw [← Nat.cast_pow, hq3, mul_zero]
  have ht := blockProd_sq_eq_prod_pair p k t hp.pos hk
  have h0 := blockProd_sq_eq_prod_pair p k 0 hp.pos hk
  change (blockProd p k t : ZMod N) ^ 2 =
    (blockProd p k 0 : ZMod N) ^ 2
  calc
    (blockProd p k t : ZMod N) ^ 2 =
        ∏ i : unitIndex p k,
          (((t * q + i.val) * (t * q + (q - i.val)) : ℕ) : ZMod N) := by
      rw [← Nat.cast_pow, ht]
      simp only [q]
      push_cast
      rfl
    _ = ∏ i : unitIndex p k, (A i + C * E) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hpair i
    _ = (∏ i : unitIndex p k, A i) + C * E *
          (∑ i : unitIndex p k, ∏ j ∈ (Finset.univ.erase i), A j) := by
      simpa using hexpand
    _ = ∏ i : unitIndex p k, A i := by rw [hcorr, add_zero]
    _ = (blockProd p k 0 : ZMod N) ^ 2 := by
      rw [← Nat.cast_pow, h0]
      simp only [q, A]
      push_cast
      simp

private lemma blockProd_congr
    (p k t : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    (blockProd p k t : ZMod ((p ^ k) ^ 3)) =
      (blockProd p k 0 : ZMod ((p ^ k) ^ 3)) := by
  classical
  let q := p ^ k
  let B := blockProd p k 0
  have hpq : p ∣ q := by dsimp [q]; exact dvd_pow_self p hk.ne'
  have hmod : blockProd p k t ≡ B [MOD p] := by
    dsimp [blockProd, B]
    apply Nat.ModEq.prod
    intro i hi
    apply Nat.ModEq.add
    · simpa [q] using
        (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right hpq t))
    · rfl
  have hB : ¬p ∣ B := by
    dsimp [B, blockProd]
    simp only [zero_mul, zero_add]
    apply (hp.prime : _root_.Prime p).not_dvd_finsetProd
    intro i hi
    exact i.prop
  have hp2 : ¬p ∣ 2 := by
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hsum : ¬p ∣ blockProd p k t + B := by
    intro h
    have hmodsum : blockProd p k t + B ≡ B + B [MOD p] := hmod.add rfl
    have hd : p ∣ B + B := (hmodsum.dvd_iff (dvd_refl p)).mp h
    rw [show B + B = 2 * B by omega] at hd
    exact (hp.not_dvd_mul hp2 hB) hd
  have hcop : (blockProd p k t + B).Coprime (q ^ 3) := by
    simpa [q, ← pow_mul] using hp.coprime_pow_of_not_dvd (m := k * 3) hsum
  have hunit : IsUnit
      ((blockProd p k t : ZMod (q ^ 3)) + (B : ZMod (q ^ 3))) := by
    rw [← Nat.cast_add, ZMod.isUnit_iff_coprime]
    exact hcop
  have hsq := blockProd_sq_congr p k t hp hp5 hk
  change (blockProd p k t : ZMod (q ^ 3)) = (B : ZMod (q ^ 3))
  change (blockProd p k t : ZMod (q ^ 3)) ^ 2 = (B : ZMod (q ^ 3)) ^ 2 at hsq
  have hfac :
      ((blockProd p k t : ZMod (q ^ 3)) - (B : ZMod (q ^ 3))) *
        ((blockProd p k t : ZMod (q ^ 3)) + (B : ZMod (q ^ 3))) = 0 := by
    calc
      _ = (blockProd p k t : ZMod (q ^ 3)) ^ 2 - (B : ZMod (q ^ 3)) ^ 2 := by ring
      _ = 0 := by rw [hsq]; ring
  exact sub_eq_zero.mp (hunit.mul_left_eq_zero.mp hfac)

private lemma blockProd_eq_range_block
    (p k t : ℕ) (hp0 : 0 < p) (hk : 0 < k) :
    blockProd p k t =
      ∏ i ∈ Finset.range (p ^ k),
        if p ∣ i + 1 then 1 else t * p ^ k + i + 1 := by
  classical
  let q := p ^ k
  have hq : 0 < q := pow_pos hp0 k
  have hpq : p ∣ q := by dsimp [q]; exact dvd_pow_self p hk.ne'
  let s : Finset ℕ := (Finset.range q).filter (fun i => ¬p ∣ i + 1)
  have hprod :
      (Finset.univ.prod (fun i : unitIndex p k => t * q + i.1.1)) =
        s.prod (fun i => t * q + i + 1) := by
    refine Finset.prod_bij
      (s := (Finset.univ : Finset (unitIndex p k))) (t := s)
      (f := fun i : unitIndex p k => t * q + i.1.1)
      (g := fun x : ℕ => t * q + x + 1)
      (fun i _ => i.1.1 - 1) ?_ ?_ ?_ ?_
    · intro i hi
      have hi0 : 0 < i.1.1 := Nat.pos_of_ne_zero (by
        intro hzero
        apply i.prop
        simp [hzero])
      simp only [s, Finset.mem_filter, Finset.mem_range]
      constructor
      · omega
      · simpa [Nat.sub_add_cancel hi0] using i.prop
    · intro i hi j hj hij
      apply Subtype.ext
      apply Fin.ext
      have hi0 : 0 < i.1.1 := Nat.pos_of_ne_zero (by
        intro hzero
        apply i.prop
        simp [hzero])
      have hj0 : 0 < j.1.1 := Nat.pos_of_ne_zero (by
        intro hzero
        apply j.prop
        simp [hzero])
      omega
    · intro x hx
      simp only [s, Finset.mem_filter, Finset.mem_range] at hx
      have hxlt : x + 1 < q := by
        have hle : x + 1 ≤ q := by omega
        by_contra hn
        have heq : x + 1 = q := by omega
        exact hx.2 (heq ▸ hpq)
      let i : unitIndex p k := ⟨⟨x + 1, by simpa [q] using hxlt⟩, hx.2⟩
      refine ⟨i, Finset.mem_univ _, ?_⟩
      dsimp [i]
    · intro i hi
      have hi0 : 0 < i.1.1 := by
        by_contra hz
        apply i.prop
        have : i.1.1 = 0 := by omega
        simp [this]
      omega
  rw [blockProd]
  change (Finset.univ.prod (fun i : unitIndex p k => t * q + i.1.1)) = _
  rw [hprod]
  change s.prod (fun i => t * q + i + 1) =
    (Finset.range q).prod
      (fun i => if p ∣ i + 1 then 1 else t * q + i + 1)
  dsimp only [s]
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : p ∣ i + 1 <;> simp [h]

private lemma unitProd_eq_prod_blocks
    (p k c : ℕ) (hp0 : 0 < p) (hk : 0 < k) :
    unitProd p (c * p ^ k) =
      ∏ t ∈ Finset.range c, blockProd p k t := by
  classical
  let q := p ^ k
  have hpq : p ∣ q := by dsimp [q]; exact dvd_pow_self p hk.ne'
  induction c with
  | zero => simp [unitProd]
  | succ c ih =>
      have htail :
          (∏ i ∈ Finset.range q,
            if p ∣ c * q + i + 1 then 1 else c * q + i + 1) =
            blockProd p k c := by
        rw [blockProd_eq_range_block p k c hp0 hk]
        change _ = ∏ i ∈ Finset.range q,
          if p ∣ i + 1 then 1 else c * q + i + 1
        apply Finset.prod_congr rfl
        intro i hi
        have hbase : p ∣ c * q := dvd_mul_of_dvd_right hpq c
        have hdiv : p ∣ c * q + i + 1 ↔ p ∣ i + 1 := by
          have h : p ∣ i + 1 ↔ p ∣ c * q + (i + 1) :=
            Nat.dvd_add_iff_right hbase
          simpa [add_assoc] using h.symm
        simp only [hdiv]
      rw [show (c + 1) * p ^ k = c * q + q by dsimp [q]; ring]
      rw [unitProd, Finset.prod_range_add]
      change unitProd p (c * p ^ k) *
          (∏ i ∈ Finset.range q,
            if p ∣ c * q + i + 1 then 1 else c * q + i + 1) = _
      rw [htail, ih, Finset.prod_range_succ]




private lemma unitProd_block_supercongruence
    (p k c d : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k)
    (hdc : d ≤ c) :
    (p : ℤ) ^ (3 * k) ∣
      (unitProd p (c * p ^ k) : ℤ) -
        (unitProd p (d * p ^ k) : ℤ) * unitProd p ((c - d) * p ^ k) := by
  classical
  let q := p ^ k
  let N := q ^ 3
  let B : ZMod N := blockProd p k 0
  have hU (e : ℕ) :
      (unitProd p (e * p ^ k) : ZMod N) = B ^ e := by
    rw [unitProd_eq_prod_blocks p k e hp.pos hk]
    push_cast
    simp_rw [show ∀ t : ℕ, (blockProd p k t : ZMod N) = B by
      intro t
      exact blockProd_congr p k t hp hp5 hk]
    simp
  have heq :
      (unitProd p (c * p ^ k) : ZMod N) =
        (unitProd p (d * p ^ k) : ZMod N) *
          (unitProd p ((c - d) * p ^ k) : ZMod N) := by
    rw [hU c, hU d, hU (c - d), ← pow_add, Nat.add_sub_of_le hdc]
  have hmod :
      unitProd p (c * p ^ k) ≡
        unitProd p (d * p ^ k) * unitProd p ((c - d) * p ^ k) [MOD N] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact heq
  have hdvd := hmod.dvd
  have hneg := dvd_neg.mpr hdvd
  simpa [N, q, ← pow_mul, Nat.mul_comm, Nat.cast_mul] using hneg

private lemma six_mul_sum_range_sq (n : ℕ) :
    6 * (∑ i ∈ Finset.range n, (i : ℤ) ^ 2) =
      (n : ℤ) * ((n : ℤ) - 1) * (2 * (n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

private lemma choose_prime_power_supercongruence
    (p k c d : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k)
    (hd : 0 < d) (hdc : d < c) :
    (p : ℤ) ^ (3 * k) ∣
      (Nat.choose (c * p ^ k) (d * p ^ k) : ℤ) -
        (Nat.choose (c * p ^ (k - 1)) (d * p ^ (k - 1)) : ℤ) := by
  let r := p ^ (k - 1)
  let M : ℤ := (p : ℤ) ^ (3 * k)
  have hpow : p ^ k = p * r := by
    calc
      p ^ k = p ^ ((k - 1) + 1) := by congr 1 <;> omega
      _ = p ^ (k - 1) * p := pow_succ _ _
      _ = p * r := by simp [r, Nat.mul_comm]
  have hrel := choose_mul_unitProd_relation p r c d hp.pos (Nat.le_of_lt hdc)
  rw [← hpow] at hrel
  have hcore := unitProd_block_supercongruence p k c d hp hp5 hk
    (Nat.le_of_lt hdc)
  let X := unitProd p (d * p ^ k) * unitProd p ((c - d) * p ^ k)
  let Y := unitProd p (c * p ^ k)
  have hXY : (X : ℤ) ≡ (Y : ℤ) [ZMOD M] := by
    rw [Int.modEq_iff_dvd]
    simpa [X, Y, M] using hcore
  have hrelZ :
      (Nat.choose (c * p ^ k) (d * p ^ k) : ℤ) * (X : ℤ) =
        (Nat.choose (c * r) (d * r) : ℤ) * (Y : ℤ) := by
    dsimp only [X, Y]
    have hn :
        Nat.choose (c * p ^ k) (d * p ^ k) *
            (unitProd p (d * p ^ k) * unitProd p ((c - d) * p ^ k)) =
          Nat.choose (c * r) (d * r) * unitProd p (c * p ^ k) := by
      simpa [mul_assoc] using hrel
    exact_mod_cast hn
  have hprod :
      (Nat.choose (c * p ^ k) (d * p ^ k) : ℤ) * (X : ℤ) ≡
        (Nat.choose (c * r) (d * r) : ℤ) * (X : ℤ) [ZMOD M] := by
    calc
      _ = (Nat.choose (c * r) (d * r) : ℤ) * (Y : ℤ) := hrelZ
      _ ≡ (Nat.choose (c * r) (d * r) : ℤ) * (X : ℤ) [ZMOD M] :=
        hXY.symm.mul_left _
  have hmul : M ∣ (X : ℤ) *
      ((Nat.choose (c * p ^ k) (d * p ^ k) : ℤ) -
        (Nat.choose (c * r) (d * r) : ℤ)) := by
    rw [show (X : ℤ) *
        ((Nat.choose (c * p ^ k) (d * p ^ k) : ℤ) -
          (Nat.choose (c * r) (d * r) : ℤ)) =
        -((Nat.choose (c * r) (d * r) : ℤ) * (X : ℤ) -
          (Nat.choose (c * p ^ k) (d * p ^ k) : ℤ) * (X : ℤ)) by ring]
    exact dvd_neg.mpr hprod.dvd
  have hpX : ¬p ∣ X := by
    dsimp [X]
    exact hp.not_dvd_mul (prime_not_dvd_unitProd p _ hp)
      (prime_not_dvd_unitProd p _ hp)
  have hcop : (p ^ (3 * k)).Coprime X :=
    ((hp.coprime_iff_not_dvd).2 hpX).pow_left _
  have hcopZ : IsCoprime M (X : ℤ) := by
    simpa [M] using (hcop.isCoprime :
      IsCoprime ((p ^ (3 * k) : ℕ) : ℤ) (X : ℤ))
  have hout := hcopZ.dvd_of_dvd_mul_left hmul
  simpa [r, M] using hout


private lemma prime_not_dvd_choose_six (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬p ∣ Nat.choose (6 * p ^ k) (p ^ k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hmod := Choose.choose_pow_mul_pow_mul_modEq_choose_nat
    (p := p) (k := k) (a := 6) (b := 1)
  rw [mul_one] at hmod
  have hmod' : Nat.choose (6 * p ^ k) (p ^ k) ≡ 6 [MOD p] := by
    simpa [Nat.mul_comm] using hmod
  intro hdvd
  have hzero : Nat.choose (6 * p ^ k) (p ^ k) % p = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd
  change Nat.choose (6 * p ^ k) (p ^ k) % p = 6 % p at hmod'
  have hsixzero : 6 % p = 0 := by omega
  have hpd6 : p ∣ 6 := Nat.dvd_of_mod_eq_zero hsixzero
  have ple6 := Nat.le_of_dvd (by omega) hpd6
  interval_cases p
  · norm_num at hpd6
  · norm_num at hp








@[category research open, AMS 11]
theorem supercongruence (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ)) := by
  let M : ℤ := (p : ℤ) ^ (3 * k)
  have h30 := choose_prime_power_supercongruence p k 30 15 hp hp5 hk (by omega) (by omega)
  have h15 := choose_prime_power_supercongruence p k 15 10 hp hp5 hk (by omega) (by omega)
  have h6 := choose_prime_power_supercongruence p k 6 1 hp hp5 hk (by omega) (by omega)
  have h30m :
      (Nat.choose (30 * p ^ k) (15 * p ^ k) : ℤ) ≡
        (Nat.choose (30 * p ^ (k - 1)) (15 * p ^ (k - 1)) : ℤ) [ZMOD M] := by
    rw [Int.modEq_iff_dvd]
    simpa [M] using dvd_neg.mpr h30
  have h15m :
      (Nat.choose (15 * p ^ k) (10 * p ^ k) : ℤ) ≡
        (Nat.choose (15 * p ^ (k - 1)) (10 * p ^ (k - 1)) : ℤ) [ZMOD M] := by
    rw [Int.modEq_iff_dvd]
    simpa [M] using dvd_neg.mpr h15
  have h6m :
      (Nat.choose (6 * p ^ k) (p ^ k) : ℤ) ≡
        (Nat.choose (6 * p ^ (k - 1)) (p ^ (k - 1)) : ℤ) [ZMOD M] := by
    rw [Int.modEq_iff_dvd]
    simpa using dvd_neg.mpr h6
  have hrel (n : ℕ) :
      (a n : ℤ) * (Nat.choose (6 * n) n : ℤ) =
        (Nat.choose (30 * n) (15 * n) : ℤ) *
          (Nat.choose (15 * n) (10 * n) : ℤ) := by
    exact_mod_cast a_mul_choose n
  have hprod :
      (a (p ^ k) : ℤ) * (Nat.choose (6 * p ^ k) (p ^ k) : ℤ) ≡
        (a (p ^ (k - 1)) : ℤ) * (Nat.choose (6 * p ^ k) (p ^ k) : ℤ) [ZMOD M] := by
    calc
      (a (p ^ k) : ℤ) * (Nat.choose (6 * p ^ k) (p ^ k) : ℤ) =
          (Nat.choose (30 * p ^ k) (15 * p ^ k) : ℤ) *
            (Nat.choose (15 * p ^ k) (10 * p ^ k) : ℤ) := hrel _
      _ ≡ (Nat.choose (30 * p ^ (k - 1)) (15 * p ^ (k - 1)) : ℤ) *
            (Nat.choose (15 * p ^ (k - 1)) (10 * p ^ (k - 1)) : ℤ) [ZMOD M] :=
          h30m.mul h15m
      _ = (a (p ^ (k - 1)) : ℤ) *
            (Nat.choose (6 * p ^ (k - 1)) (p ^ (k - 1)) : ℤ) := (hrel _).symm
      _ ≡ (a (p ^ (k - 1)) : ℤ) *
            (Nat.choose (6 * p ^ k) (p ^ k) : ℤ) [ZMOD M] :=
          h6m.symm.mul_left _
  have hmul : M ∣
      (Nat.choose (6 * p ^ k) (p ^ k) : ℤ) *
        ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ)) := by
    rw [show
      (Nat.choose (6 * p ^ k) (p ^ k) : ℤ) *
          ((a (p ^ k) : ℤ) - (a (p ^ (k - 1)) : ℤ)) =
        -((a (p ^ (k - 1)) : ℤ) * (Nat.choose (6 * p ^ k) (p ^ k) : ℤ) -
          (a (p ^ k) : ℤ) * (Nat.choose (6 * p ^ k) (p ^ k) : ℤ)) by ring]
    exact dvd_neg.mpr hprod.dvd
  have hpc : p.Coprime (Nat.choose (6 * p ^ k) (p ^ k)) :=
    (hp.coprime_iff_not_dvd).2 (prime_not_dvd_choose_six p k hp hp5)
  have hpcpow : (p ^ (3 * k)).Coprime (Nat.choose (6 * p ^ k) (p ^ k)) :=
    hpc.pow_left _
  have hpcZ : IsCoprime M (Nat.choose (6 * p ^ k) (p ^ k) : ℤ) := by
    simpa [M] using (hpcpow.isCoprime :
      IsCoprime ((p ^ (3 * k) : ℕ) : ℤ) (Nat.choose (6 * p ^ k) (p ^ k) : ℤ))
  exact hpcZ.dvd_of_dvd_mul_left hmul
end OeisA211417
