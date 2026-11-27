/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SpoofLehmerFactorization
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic

/-!
# Repeated unitary Lehmer factorizations

The repeated unitary factorization $x \cdots x$ is a spoof $k$-Lehmer factorization only when
$x = 2$ with at least two factors, or $x = 3$ with two or four factors.
-/

namespace MetaMathlibExt

namespace eq_two_or_eq_three_of_isSpoofLehmer_replicate

private theorem lt_pow_sub_one {s : ℕ} (hs : 3 ≤ s) : s < 2 ^ (s - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 3 := ⟨s - 3, by omega⟩
  have key : ∀ n : ℕ, n + 3 < 2 ^ (n + 2) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hpow : (2 : ℕ) ^ (n + 3) = 2 * 2 ^ (n + 2) := by
        rw [show n + 3 = (n + 2) + 1 by omega, pow_succ, mul_comm]
      have hgoal : (n + 1) + 3 = n + 4 := rfl
      have hexp : (n + 1) + 2 = n + 3 := rfl
      rw [hgoal, hexp, hpow]
      omega
  simpa using key n

private theorem lt_pow_sub_two {s : ℕ} (hs : 6 ≤ s) : s < 2 ^ (s - 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 6 := ⟨s - 6, by omega⟩
  have key : ∀ n : ℕ, n + 6 < 2 ^ (n + 4) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hpow : (2 : ℕ) ^ (n + 5) = 2 * 2 ^ (n + 4) := by
        rw [show n + 5 = (n + 4) + 1 by omega, pow_succ, mul_comm]
      have hgoal : (n + 1) + 6 = n + 7 := rfl
      have hexp : (n + 1) + 4 = n + 5 := rfl
      rw [hgoal, hexp, hpow]
      omega
  simpa using key n

/-- Lifting the exponent at an odd prime divisor of `x - 1` rules out `s ≥ 3`. -/
private theorem absurd_of_odd_prime {p x s : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hx : 2 ≤ x) (hpd : p ∣ x - 1) (hs : 3 ≤ s)
    (hdvd : (x - 1) ^ s ∣ x ^ s - 1) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hpx : ¬ p ∣ x := by
    intro h
    have h1 : p ∣ x - (x - 1) := Nat.dvd_sub h hpd
    rw [show x - (x - 1) = 1 by omega] at h1
    exact hp.not_dvd_one h1
  have hM := Nat.multiplicity_pow_sub_pow hodd (by omega : 1 < x) hpd hpx (by omega : s ≠ 0)
  simp only [one_pow] at hM
  have hfin : FiniteMultiplicity p (x ^ s - 1) :=
    Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, by
      have : 1 < x ^ s := one_lt_pow₀ hx (by omega)
      omega⟩
  have hv : 1 ≤ multiplicity p (x - 1) := by
    have hfin' : FiniteMultiplicity p (x - 1) :=
      Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, by omega⟩
    have := hfin'.le_multiplicity_of_pow_dvd (k := 1) (by simpa using hpd)
    simpa using this
  have hle : s * multiplicity p (x - 1) ≤ multiplicity p (x ^ s - 1) := by
    apply hfin.le_multiplicity_of_pow_dvd
    have h1 : p ^ multiplicity p (x - 1) ∣ x - 1 := pow_dvd_of_le_multiplicity le_rfl
    have h2 := pow_dvd_pow_of_dvd h1 s
    rw [← pow_mul, Nat.mul_comm (multiplicity p (x - 1)) s] at h2
    exact dvd_trans h2 hdvd
  have hw : p ^ multiplicity p s ≤ s :=
    Nat.le_of_dvd (by omega) (pow_dvd_of_le_multiplicity le_rfl)
  have hs' : s = (s - 1) + 1 := by omega
  have hsplit : s * multiplicity p (x - 1) =
      (s - 1) * multiplicity p (x - 1) + multiplicity p (x - 1) := by
    conv_lhs => rw [hs']
    rw [add_mul, one_mul]
  rw [hsplit] at hle
  have hle' := hle
  have hmult : (s - 1) * multiplicity p (x - 1) ≤ multiplicity p s := by omega
  have hpow : (2 : ℕ) ^ (s - 1) ≤ s := by
    calc (2 : ℕ) ^ (s - 1) ≤ p ^ (s - 1) := Nat.pow_le_pow_left hp.two_le _
      _ ≤ p ^ ((s - 1) * multiplicity p (x - 1)) :=
        Nat.pow_le_pow_right hp.pos (Nat.le_mul_of_pos_right _ hv)
      _ ≤ p ^ multiplicity p s := Nat.pow_le_pow_right hp.pos hmult
      _ ≤ s := hw
  exact absurd hpow (not_le_of_gt (lt_pow_sub_one hs))

private theorem exists_eq_two_pow {d : ℕ} (hd : 1 ≤ d)
    (h : ∀ p : ℕ, p.Prime → p ∣ d → p = 2) : ∃ t, d = 2 ^ t := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases eq_or_ne d 1 with rfl | hd1
    · exact ⟨0, by simp⟩
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := d) hd1
      have hp2 := h p hp hpd
      subst hp2
      obtain ⟨m, rfl⟩ := hpd
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · simp [h0] at hd
        · exact hpos
      have hmd : m < 2 * m := by omega
      obtain ⟨t, ht⟩ := ih m hmd hm1 (fun q hq hqd => by
        obtain ⟨c, hc⟩ := hqd
        exact h q hq ⟨2 * c, by rw [hc]; ring⟩)
      exact ⟨t + 1, by rw [ht]; exact (pow_succ' 2 t).symm⟩

end eq_two_or_eq_three_of_isSpoofLehmer_replicate

namespace eq_two_or_eq_three_of_isSpoofLehmer_replicate

private theorem geom_sum_mul_sub {x s : ℕ} (hx : 1 ≤ x) :
    (∑ i ∈ Finset.range s, x ^ i) * (x - 1) = x ^ s - 1 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, Nat.add_mul, ih, pow_succ, Nat.mul_sub]
    have h1 : 1 ≤ x ^ s := Nat.one_le_pow s x hx
    have h2 : x ^ s ≤ x ^ s * x := Nat.le_mul_of_pos_right _ hx
    omega

end eq_two_or_eq_three_of_isSpoofLehmer_replicate

/-- **Repeated unitary Lehmer factorizations.** Let $k$ be an integer and let $x \ge 2$ and $s$ be
natural numbers. If the spoof factorization $x \cdots x$ with $s$ factors, each with base $x$ and
exponent $1$, is a spoof $k$-Lehmer factorization (a unitary $k$-Lehmer factorization), then
either $x = 2$ and $s \ge 2$, or $x = 3$ and $s \in \{2, 4\}$.

The paper assumes $k \ge 2$ instead of $x \ge 2$; as printed the statement fails for $x = 1$:
for every $s \ge 2$ the factorization $1 \cdots 1$ with $s$ factors has spoof totient $0$ and
spoof evaluation $1$, so it is a spoof $k$-Lehmer factorization for every $k$. The paper's proof
treats only $x = 2$, $x = 3$ and $x \ge 4$. When $x \ge 2$, the hypothesis forces $k \ge 2$.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Theorem 2 (`integers-2026-A100-thm-2`). -/
public theorem eq_two_or_eq_three_of_isSpoofLehmer_replicate (k : ℤ) (x s : ℕ)
    (hx : 2 ≤ x) (h : IsSpoofLehmer k (spoofOfBases (Multiset.replicate s x))) :
    (x = 2 ∧ 2 ≤ s) ∨ (x = 3 ∧ (s = 2 ∨ s = 4)) := by
  obtain ⟨-, heq, hcard⟩ := h
  have hEval : spoofEval (spoofOfBases (Multiset.replicate s x)) = (x : ℤ) ^ s := by
    simp [spoofEval, spoofOfBases]
  have hTot : spoofTotient (spoofOfBases (Multiset.replicate s x)) = ((x : ℤ) - 1) ^ s := by
    simp [spoofTotient, spoofOfBases]
  rw [hEval, hTot] at heq
  have hs2 : 2 ≤ s := by
    rcases hcard with hcard | hex
    · simpa [spoofOfBases] using hcard
    · obtain ⟨p, hp, hp2⟩ := hex
      simp only [spoofOfBases, Multiset.mem_map, Multiset.mem_replicate] at hp
      obtain ⟨a, -, rfl⟩ := hp
      simp at hp2
  have hcast : ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ x), Nat.cast_one]
  have hkpos : 0 < k := by
    have h1 : (0 : ℤ) < ((x : ℤ) - 1) ^ s := by
      have hcast1 : (1 : ℤ) ≤ ((x - 1 : ℕ) : ℤ) := by
        exact_mod_cast (by omega : 1 ≤ x - 1)
      rw [hcast] at hcast1
      exact pow_pos (by linarith) s
    have h2 : (0 : ℤ) < (x : ℤ) ^ s - 1 := by
      have hcast : (2 : ℤ) ≤ x := by exact_mod_cast hx
      have := one_lt_pow₀ (by linarith : (1 : ℤ) < x) (by omega : s ≠ 0)
      linarith
    by_contra hk
    have hk : k ≤ 0 := le_of_not_gt hk
    have := mul_nonpos_of_nonpos_of_nonneg hk h1.le
    linarith
  have hNatEq : k.toNat * (x - 1) ^ s = x ^ s - 1 := by
    have hcastEq : ((k.toNat * (x - 1) ^ s : ℕ) : ℤ) = ((x ^ s - 1 : ℕ) : ℤ) := by
      push_cast [Int.toNat_of_nonneg hkpos.le, hcast]
      rw [Nat.cast_sub (show (1 : ℕ) ≤ x ^ s from one_le_pow₀ (by omega : 1 ≤ x)),
        Nat.cast_one, Nat.cast_pow]
      exact heq
    exact_mod_cast hcastEq
  have hdvd : (x - 1) ^ s ∣ x ^ s - 1 := ⟨k.toNat, by rw [mul_comm]; exact hNatEq.symm⟩
  by_cases hx2 : x = 2
  · exact Or.inl ⟨hx2, hs2⟩
  have hx3 : 3 ≤ x := by omega
  by_cases hs_eq2 : s = 2
  · subst hs_eq2
    have hsq2 : (x - 1) * (x + 1) = x ^ 2 - 1 := by
      rw [pow_two, Nat.sub_mul, one_mul, Nat.mul_add, mul_one]
      omega
    have hsq : x ^ 2 - 1 = (x + 1) * (x - 1) := by rw [mul_comm, hsq2]
    have h3 : (k.toNat * (x - 1)) * (x - 1) = (x + 1) * (x - 1) := by
      calc (k.toNat * (x - 1)) * (x - 1) = k.toNat * (x - 1) ^ 2 := by
            rw [pow_two, mul_assoc]
        _ = x ^ 2 - 1 := hNatEq
        _ = (x + 1) * (x - 1) := hsq
    have h4 : k.toNat * (x - 1) = x + 1 :=
      Nat.eq_of_mul_eq_mul_right (by omega : 0 < x - 1) h3
    have hdvd2 : (x - 1) ∣ 2 := by
      have h5 : (x - 1) ∣ x + 1 := ⟨k.toNat, by rw [mul_comm]; exact h4.symm⟩
      have h6 : (x - 1) ∣ (x + 1) - (x - 1) := Nat.dvd_sub h5 (dvd_refl _)
      rwa [show (x + 1) - (x - 1) = 2 by omega] at h6
    have hle : x - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    have : x = 3 := by omega
    exact Or.inr ⟨this, Or.inl rfl⟩
  have hs3 : 3 ≤ s := by omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := x - 1) (by omega : x - 1 ≠ 1)
  by_cases hodd : Odd p
  · exact (eq_two_or_eq_three_of_isSpoofLehmer_replicate.absurd_of_odd_prime hp hodd hx hpd
      hs3 hdvd).elim
  have hp2 : p = 2 := by
    rcases hp.eq_two_or_odd with h2 | hodd2
    · exact h2
    · exact absurd (Nat.odd_iff.mpr hodd2) hodd
  subst hp2
  by_cases hoddprime : ∃ q : ℕ, q.Prime ∧ Odd q ∧ q ∣ x - 1
  · obtain ⟨q, hq, hqodd, hqd⟩ := hoddprime
    exact (eq_two_or_eq_three_of_isSpoofLehmer_replicate.absurd_of_odd_prime hq hqodd hx hqd
      hs3 hdvd).elim
  have hclass : ∀ q : ℕ, q.Prime → q ∣ x - 1 → q = 2 := by
    intro q hq hqd
    rcases hq.eq_two_or_odd with h2 | hodd2
    · exact h2
    · exact absurd ⟨q, hq, Nat.odd_iff.mpr hodd2, hqd⟩ hoddprime
  obtain ⟨t, ht⟩ := eq_two_or_eq_three_of_isSpoofLehmer_replicate.exists_eq_two_pow
    (d := x - 1) (by omega) hclass
  have htpos : 1 ≤ t := by
    rcases t with _ | t
    · simp at ht
      omega
    · omega
  have hxeq : x = 2 ^ t + 1 := by omega
  have hxodd : ¬ 2 ∣ x := by
    intro hd
    have h2t : 2 ∣ 2 ^ t := dvd_pow_self 2 (by omega : t ≠ 0)
    have h1 : 2 ∣ x - 2 ^ t := Nat.dvd_sub hd h2t
    rw [hxeq] at h1
    simp at h1
  have hfin : FiniteMultiplicity 2 (x ^ s - 1) :=
    Nat.finiteMultiplicity_iff.mpr ⟨by norm_num, by
      have : 1 < x ^ s := one_lt_pow₀ hx (by omega)
      omega⟩
  have hmult_d : multiplicity 2 (x - 1) = t := by
    rw [ht]
    exact Nat.multiplicity_prime_pow t
  have hle2 : t * s ≤ multiplicity 2 (x ^ s - 1) := by
    apply hfin.le_multiplicity_of_pow_dvd
    have h1 : (2 : ℕ) ^ (t * s) ∣ x ^ s - 1 := by
      have e : (2 : ℕ) ^ (t * s) = (x - 1) ^ s := by rw [pow_mul, ht]
      rw [e]
      exact hdvd
    exact h1
  rcases Nat.even_or_odd s with hsEven | hsOdd
  · have hM2 := Nat.multiplicity_pow_two_sub_one (x := x) (n := s) (by omega : 1 < x)
      hxodd (by omega) hsEven
    by_cases ht1 : t = 1
    · have hx3eq : x = 3 := by rw [hxeq, ht1]; norm_num
      subst hx3eq
      have hmult4 : multiplicity 2 (3 + 1) ≤ 2 := by
        by_contra hgt
        have hgt' : 3 ≤ multiplicity 2 (3 + 1) := by omega
        have h8 : (2 : ℕ) ^ 3 ∣ 3 + 1 := pow_dvd_of_le_multiplicity hgt'
        norm_num at h8
      have hsle : s ≤ 2 + multiplicity 2 s := by
        rw [ht1] at hle2 hmult_d
        simp only [one_mul] at hle2
        omega
      have hpowle : (2 : ℕ) ^ (s - 2) ≤ s := by
        calc (2 : ℕ) ^ (s - 2) ≤ 2 ^ multiplicity 2 s :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ s := Nat.le_of_dvd (by omega) (pow_dvd_of_le_multiplicity le_rfl)
      have hs5 : s ≤ 5 := by
        by_contra hgt
        have h6 : 6 ≤ s := by omega
        have := eq_two_or_eq_three_of_isSpoofLehmer_replicate.lt_pow_sub_two h6
        omega
      interval_cases s
      · exact absurd hdvd (by decide)
      · exact Or.inr ⟨rfl, Or.inr rfl⟩
      · exact absurd hdvd (by decide)
    · have ht2 : 2 ≤ t := by omega
      have hnot4 : ¬ (4 : ℕ) ∣ x + 1 := by
        intro h4
        have h4d : (4 : ℕ) ∣ 2 ^ t := by
          have : (2 : ℕ) ^ 2 ∣ 2 ^ t := pow_dvd_pow 2 ht2
          simpa using this
        have h2d : (4 : ℕ) ∣ 2 := by
          have h5 : (4 : ℕ) ∣ (x + 1) - 2 ^ t := Nat.dvd_sub h4 h4d
          rwa [show (x + 1) - 2 ^ t = 2 by omega] at h5
        norm_num at h2d
      have hmult1 : multiplicity 2 (x + 1) ≤ 1 := by
        by_contra hgt
        have hgt' : 2 ≤ multiplicity 2 (x + 1) := by omega
        have h4 : (2 : ℕ) ^ 2 ∣ x + 1 := pow_dvd_of_le_multiplicity hgt'
        exact hnot4 (by simpa using h4)
      have hle3 : t * (s - 1) ≤ multiplicity 2 s := by
        have hts : t * s = t * (s - 1) + t := by
          conv_lhs => rw [show s = (s - 1) + 1 by omega]
          rw [mul_add, mul_one]
        omega
      have hpowle : (2 : ℕ) ^ (t * (s - 1)) ≤ s := by
        calc (2 : ℕ) ^ (t * (s - 1)) ≤ 2 ^ multiplicity 2 s :=
            Nat.pow_le_pow_right (by norm_num) hle3
          _ ≤ s := Nat.le_of_dvd (by omega) (pow_dvd_of_le_multiplicity le_rfl)
      have hge : s ≤ t * (s - 1) := by
        calc s ≤ 2 * (s - 1) := by omega
          _ ≤ t * (s - 1) := Nat.mul_le_mul_right _ ht2
      have : (2 : ℕ) ^ s ≤ s := by
        calc (2 : ℕ) ^ s ≤ 2 ^ (t * (s - 1)) := Nat.pow_le_pow_right (by norm_num) hge
          _ ≤ s := hpowle
      exact absurd this (not_le_of_gt Nat.lt_two_pow_self)
  · have hgeom := eq_two_or_eq_three_of_isSpoofLehmer_replicate.geom_sum_mul_sub
      (x := x) (s := s) (by omega)
    have hxOdd : Odd x := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact hxodd
    have hGodd : ¬ 2 ∣ ∑ i ∈ Finset.range s, x ^ i := by
      intro hdvdG
      have hmod : (∑ i ∈ Finset.range s, x ^ i) % 2 = 1 := by
        rw [Finset.sum_nat_mod]
        have hxi : ∀ i ∈ Finset.range s, x ^ i % 2 = 1 := by
          intro i _
          exact Nat.odd_iff.mp (hxOdd.pow)
        rw [Finset.sum_congr rfl hxi]
        simp [Nat.odd_iff.mp hsOdd]
      have h0 : (∑ i ∈ Finset.range s, x ^ i) % 2 = 0 := by omega
      omega
    have hmultG : multiplicity 2 (∑ i ∈ Finset.range s, x ^ i) = 0 := by
      by_contra hne
      have h1 : 1 ≤ multiplicity 2 (∑ i ∈ Finset.range s, x ^ i) := Nat.pos_of_ne_zero hne
      have h2 : (2 : ℕ) ^ 1 ∣ ∑ i ∈ Finset.range s, x ^ i :=
        pow_dvd_of_le_multiplicity h1
      exact hGodd (by simpa using h2)
    have hGpos : 0 < ∑ i ∈ Finset.range s, x ^ i := by
      have hle1 := Finset.single_le_sum (f := fun i => x ^ i) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by omega : 0 < s))
      simp only [pow_zero] at hle1
      omega
    have hmultProd : multiplicity 2 (x ^ s - 1) = t := by
      rw [← hgeom, Nat.multiplicity_mul (by omega : (∑ i ∈ Finset.range s, x ^ i) ≠ 0)
        (by omega : x - 1 ≠ 0), hmultG, hmult_d, zero_add]
    exfalso
    have hs1 : s ≤ 1 := by
      rw [hmultProd] at hle2
      exact Nat.le_of_mul_le_mul_left (by simpa using hle2) htpos
    omega

end MetaMathlibExt
