/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

namespace Nat

/-!
# Highly composite numbers

This file formalizes the strict divisor records and their first shape theorem from
*Prime-Exponent Transition Geometry and Divisor Barriers Between Consecutive Highly
Composite Numbers* (arXiv:2608.17045), `hcn_transition_geometry.tex`, source SHA-256
`f8de59657076caf6f78a5e97cbdde69afd23b0c6dafc3e790d098cb9ef58aa42`, lines 121–127
and 250–270.
-/

/-- A positive natural number is highly composite if it has strictly more divisors than every
smaller positive natural number. -/
def IsHighlyComposite (H : ℕ) : Prop :=
  0 < H ∧ ∀ m : ℕ, 0 < m → m < H → m.divisors.card < H.divisors.card

/-- **Exponents of highly composite numbers are non-increasing.** If $H$ is a highly composite
number and $p \le q$ are primes, then the exponent of $q$ in the prime factorization of $H$ is at
most the exponent of $p$. -/
theorem IsHighlyComposite.factorization_antitone {H p q : ℕ}
    (hH : H.IsHighlyComposite) (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    H.factorization q ≤ H.factorization p := by
  obtain rfl | hpq := hpq.eq_or_lt
  · exact le_rfl
  by_contra hlt
  push Not at hlt
  set a := H.factorization p with ha_def
  set b := H.factorization q with hb_def
  have hab : a < b := hlt
  have hHpos : 0 < H := hH.1
  have hHne0 : H ≠ 0 := Nat.ne_of_gt hHpos
  have hpq_ne : p ≠ q := Nat.ne_of_lt hpq
  have hqp_ne : q ≠ p := Ne.symm hpq_ne
  let Hp := ordCompl[p] H
  let c := ordCompl[q] Hp
  have hHp_pos : 0 < Hp := Nat.ordCompl_pos p hHne0
  have hHp_ne0 : Hp ≠ 0 := Nat.ne_of_gt hHp_pos
  have hc_pos : 0 < c := Nat.ordCompl_pos q hHp_ne0
  have hHp_fact : Hp.factorization = H.factorization.erase p :=
    Nat.factorization_ordCompl H p
  have hHp_q : Hp.factorization q = b := by
    rw [hHp_fact, Finsupp.erase_ne hqp_ne, hb_def]
  have hProj_p : ordProj[p] H = p ^ a := by
    simp only [ha_def]
  have hProj_q_Hp : ordProj[q] Hp = q ^ b := by
    simp only [hHp_q]
  have hH_eq : H = p ^ a * Hp := by
    rw [← hProj_p]
    exact (Nat.ordProj_mul_ordCompl_eq_self H p).symm
  have hHp_eq : Hp = q ^ b * c := by
    rw [← hProj_q_Hp]
    exact (Nat.ordProj_mul_ordCompl_eq_self Hp q).symm
  have hH_eq2 : H = p ^ a * (q ^ b * c) := by rw [hH_eq, hHp_eq]
  have hCop_p_Hp : Nat.Coprime (p ^ a) Hp :=
    (Nat.coprime_ordCompl hp hHne0).pow_left a
  have hCop_q_c : Nat.Coprime (q ^ b) c :=
    (Nat.coprime_ordCompl hq hHp_ne0).pow_left b
  have hpq_coprime : Nat.Coprime p q := by
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    rcases (Nat.dvd_prime hq).mp hdvd with h | h
    · exact hp.ne_one h
    · exact hpq_ne h
  have hc_dvd_Hp : c ∣ Hp := Nat.ordCompl_dvd Hp q
  have hCard_pa : (p ^ a).divisors.card = a + 1 := by
    simp [Nat.divisors_prime_pow hp]
  have hCard_qb : (q ^ b).divisors.card = b + 1 := by
    simp [Nat.divisors_prime_pow hq]
  have hCard_pb : (p ^ b).divisors.card = b + 1 := by
    simp [Nat.divisors_prime_pow hp]
  have hCard_qa : (q ^ a).divisors.card = a + 1 := by
    simp [Nat.divisors_prime_pow hq]
  have hCard_Hp : Hp.divisors.card = (b + 1) * c.divisors.card := by
    rw [hHp_eq, hCop_q_c.card_divisors_mul, hCard_qb]
  have hCard_H : H.divisors.card = (a + 1) * ((b + 1) * c.divisors.card) := by
    rw [hH_eq, hCop_p_Hp.card_divisors_mul, hCard_pa, hCard_Hp]
  set M := p ^ b * (q ^ a * c) with hM_def
  have hM_pos : 0 < M :=
    Nat.mul_pos (Nat.pow_pos hp.pos) (Nat.mul_pos (Nat.pow_pos hq.pos) hc_pos)
  have hCop_qa_c : Nat.Coprime (q ^ a) c :=
    (Nat.coprime_ordCompl hq hHp_ne0).pow_left a
  have hCop_pb_qa : Nat.Coprime (p ^ b) (q ^ a) := hpq_coprime.pow b a
  have hCop_pb_c : Nat.Coprime (p ^ b) c :=
    ((Nat.coprime_ordCompl hp hHne0).coprime_dvd_right hc_dvd_Hp).pow_left b
  have hCop_pb_qac : Nat.Coprime (p ^ b) (q ^ a * c) :=
    hCop_pb_qa.mul_right hCop_pb_c
  have hCard_qac : (q ^ a * c).divisors.card = (a + 1) * c.divisors.card := by
    rw [hCop_qa_c.card_divisors_mul, hCard_qa]
  have hCard_M : M.divisors.card = (b + 1) * ((a + 1) * c.divisors.card) := by
    rw [hM_def, hCop_pb_qac.card_divisors_mul, hCard_pb, hCard_qac]
  have hCard_eq : M.divisors.card = H.divisors.card := by
    rw [hCard_M, hCard_H]
    ac_rfl
  let k := b - a
  have hk_pos : 0 < k := Nat.sub_pos_of_lt hab
  have hak : a + k = b := Nat.add_sub_cancel' (Nat.le_of_lt hab)
  have hp_pow : p ^ b = p ^ a * p ^ k := by rw [← hak, pow_add]
  have hq_pow : q ^ b = q ^ a * q ^ k := by rw [← hak, pow_add]
  have hpow_lt : p ^ k < q ^ k := Nat.pow_lt_pow_left hpq (Nat.ne_of_gt hk_pos)
  have hH_eq3 : H = p ^ a * q ^ a * c * q ^ k := by
    rw [hH_eq2, hq_pow]
    ac_rfl
  have hM_eq3 : M = p ^ a * q ^ a * c * p ^ k := by
    rw [hM_def, hp_pow]
    ac_rfl
  have h_common_pos : 0 < p ^ a * q ^ a * c :=
    Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hp.pos) (Nat.pow_pos hq.pos)) hc_pos
  have hM_lt_H : M < H := by
    rw [hM_eq3, hH_eq3]
    exact Nat.mul_lt_mul_of_pos_left hpow_lt h_common_pos
  have hlt_card := hH.2 M hM_pos hM_lt_H
  rw [hCard_eq] at hlt_card
  exact Nat.lt_irrefl _ hlt_card

/-- **Prime divisors of highly composite numbers form an initial segment.** If $H$ is a highly
composite number and $p \le q$ are primes with $q \mid H$, then $p \mid H$. In other words, the
set of primes dividing $H$ is an initial segment of the primes. -/
theorem IsHighlyComposite.dvd_of_prime_le {H p q : ℕ}
    (hH : H.IsHighlyComposite) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≤ q) (hqH : q ∣ H) : p ∣ H := by
  have hHne0 : H ≠ 0 := Nat.ne_of_gt hH.1
  have hAnt := hH.factorization_antitone hp hq hpq
  have hq_le : 1 ≤ H.factorization q :=
    (Nat.Prime.dvd_iff_one_le_factorization hq hHne0).mp hqH
  have hp_le : 1 ≤ H.factorization p := hq_le.trans hAnt
  exact (Nat.Prime.dvd_iff_one_le_factorization hp hHne0).mpr hp_le

end Nat
