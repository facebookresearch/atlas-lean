/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import MathlibExt.NumberTheory.Cyclotomic.CommonPrimeDivisorEvalPow
import MathlibExt.NumberTheory.Cyclotomic.ComposedFactorization
import MathlibExt.NumberTheory.Cyclotomic.PrimeDivisorCongruence
import MathlibExt.NumberTheory.Cyclotomic.PrimePowerDivisibility
import MathlibExt.NumberTheory.Cyclotomic.TwoPowRamifiedBound

/-!
# Hybrid bound for prime divisors of `x ^ p - 1`

For a prime `p` and `x > 1`, with `ω` the number of distinct prime factors of `x ^ p - 1`,
there is `k < ω` such that the first `k` primes not congruent to `1` modulo `p` and the
first `ω - k` primes congruent to `1` satisfy `1 + ∏ r_{i,0} ≤ x` and
`1 + (∏ r_{i,0}) * (∏ r_{j,1}) ≤ x ^ p`.

## References

* Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
  Article A95, Proposition 2 (`integers-2026-A95-prop-2`).
-/

namespace MetaMathlibExt

open Polynomial

private theorem mem_nth_of_card_lt
    {P : ℕ → Prop} (s : Finset ℕ) (hs : ∀ q ∈ s, P q)
    {i : ℕ} (hi : i < s.card) : P (Nat.nth P i) := by
  by_cases hfin : (Set.ofPred P).Finite
  · have hle : s.card ≤ hfin.toFinset.card := by
      apply Finset.card_le_card
      intro q hq
      rw [hfin.mem_toFinset]
      exact hs q hq
    exact Nat.nth_mem_of_lt_card hfin (lt_of_lt_of_le hi hle)
  · exact Nat.nth_mem_of_infinite (Set.not_finite.mp hfin) i

private theorem prod_nth_le_prod
    {P : ℕ → Prop} (s : Finset ℕ) (hs : ∀ q ∈ s, P q) :
    ∏ i ∈ Finset.range s.card, Nat.nth P i ≤ ∏ q ∈ s, q := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert p s hlt ih =>
    have hp : P p := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, P q := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hps : p ∉ s := fun h => (hlt p h).false
    have hcount : s.card ≤ Nat.count P p := by
      rw [Nat.count_eq_card_filter_range]
      apply Finset.card_le_card
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_range] at hq ⊢
      exact ⟨hlt q hq, hs' q hq⟩
    have hnth : Nat.nth P s.card ≤ p := by
      by_cases hfin : (Set.ofPred P).Finite
      · have hcard : (insert p s).card ≤ hfin.toFinset.card := by
          apply Finset.card_le_card
          intro q hq
          rw [hfin.mem_toFinset]
          simp only [Finset.mem_insert] at hq
          rcases hq with rfl | hq
          · exact hp
          · exact hs' q hq
        rw [Finset.card_insert_of_notMem hps] at hcard
        have hlt2 : Nat.count P p < hfin.toFinset.card := by
          rw [Nat.count_eq_card_filter_range]
          apply Finset.card_lt_card
          constructor
          · intro q hq
            simp only [Finset.mem_filter, Finset.mem_range] at hq
            rw [hfin.mem_toFinset]
            exact hq.2
          · intro hsub
            have hmem : p ∈ hfin.toFinset := by
              rw [hfin.mem_toFinset]
              exact hp
            have hmem2 : p ∈ {x ∈ Finset.range p | P x} := hsub hmem
            simp only [Finset.mem_filter, Finset.mem_range] at hmem2
            exact (lt_irrefl p hmem2.1).elim
        calc Nat.nth P s.card ≤ Nat.nth P (Nat.count P p) :=
              Nat.nth_le_nth_of_lt_card hfin hcount hlt2
          _ = p := Nat.nth_count hp
      · have hinf : (Set.ofPred P).Infinite := Set.not_finite.mp hfin
        calc Nat.nth P s.card ≤ Nat.nth P (Nat.count P p) :=
              Nat.nth_monotone hinf hcount
          _ = p := Nat.nth_count hp
    rw [Finset.card_insert_of_notMem hps, Finset.prod_range_succ,
      Finset.prod_insert hps, mul_comm p]
    exact Nat.mul_le_mul (ih hs') hnth

private theorem cyclo_mul_sub_one_eq {p : ℕ} (hp : p.Prime) (x : ℤ) :
    (cyclotomic p ℤ).eval x * (x - 1) = x ^ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h := congrArg (fun f : ℤ[X] => f.eval x) (cyclotomic_prime_mul_X_sub_one ℤ p)
  simpa using h

private theorem natPrime_prime_int {ρ : ℕ} (hρ : ρ.Prime) : Prime (ρ : ℤ) := by
  rw [Int.prime_iff_natAbs_prime]
  simpa using hρ

private theorem mem_s0_dvd_sub_one {p x ρ : ℕ} (hp : p.Prime) (hx : 1 < x)
    (hρprime : ρ.Prime) (hdvd : ρ ∣ x ^ p - 1) (hnmod : ¬ Nat.ModEq p ρ 1) :
    ρ ∣ x - 1 := by
  by_cases heq : ρ = p
  · have hdvd_p : p ∣ x ^ p - 1 := by simpa [heq] using hdvd
    have hgoal : (ρ ∣ x - 1) ↔ (p ∣ x - 1) := by rw [heq]
    rw [hgoal]
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hxpos : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hx0
    have hxp_gt1 : (1 : ℕ) < x ^ p := one_lt_pow₀ hx hp.pos.ne'
    have hxp1 : (1 : ℕ) ≤ x ^ p := le_of_lt hxp_gt1
    have hNcast : ((x ^ p - 1 : ℕ) : ℤ) = (x : ℤ) ^ p - 1 := by
      rw [Nat.cast_sub hxp1]
      simp
    have hx1cast : ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by
      rw [Nat.cast_sub (le_of_lt hx)]
      simp
    have hdvdZ : (p : ℤ) ∣ (x : ℤ) ^ p - 1 := by
      rw [← hNcast]
      exact Int.natCast_dvd_natCast.mpr hdvd_p
    have hiff := (prime_dvd_pow_self_sub_one_iff hp hxpos).mp hdvdZ
    have hsubZ : (p : ℤ) ∣ (x : ℤ) - 1 := hiff.1
    rw [← hx1cast] at hsubZ
    exact Int.natCast_dvd_natCast.mp hsubZ
  · by_contra hndvd
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hxpos : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hx0
    have hxp_gt1 : (1 : ℕ) < x ^ p := one_lt_pow₀ hx hp.pos.ne'
    have hxp1 : (1 : ℕ) ≤ x ^ p := le_of_lt hxp_gt1
    have hNcast : ((x ^ p - 1 : ℕ) : ℤ) = (x : ℤ) ^ p - 1 := by
      rw [Nat.cast_sub hxp1]
      simp
    have hx1cast : ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by
      rw [Nat.cast_sub (le_of_lt hx)]
      simp
    have hdvdZ : (ρ : ℤ) ∣ (x : ℤ) ^ p - 1 := by
      rw [← hNcast]
      exact Int.natCast_dvd_natCast.mpr hdvd
    have hndvdZ : ¬ (ρ : ℤ) ∣ (x : ℤ) - 1 := by
      intro h
      rw [← hx1cast] at h
      exact hndvd (Int.natCast_dvd_natCast.mp h)
    have hfact : (x : ℤ) ^ p - 1 = (cyclotomic p ℤ).eval (x : ℤ) * ((x : ℤ) - 1) :=
      (cyclo_mul_sub_one_eq hp (x : ℤ)).symm
    rw [hfact] at hdvdZ
    have hprime : Prime (ρ : ℤ) := natPrime_prime_int hρprime
    have hor := (hprime.dvd_mul.mp hdvdZ)
    rcases hor with hΦ | hsub
    · exact hnmod (prime_modEq_one_of_dvd_cyclotomic_eval hρprime hp heq hxpos hΦ)
    · exact hndvdZ hsub

private theorem main_of_s1_nonempty {p x : ℕ} (hp : p.Prime) (hx : 1 < x)
    (hs1 : ∃ ρ ∈ (x ^ p - 1).primeFactors, Nat.ModEq p ρ 1) :
    ∃ k < (x ^ p - 1).primeFactors.card,
      (∀ i < k, 0 < Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i) ∧
      1 + ∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i ≤ x ∧
        1 + (∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i) *
            ∏ j ∈ Finset.range ((x ^ p - 1).primeFactors.card - k),
              Nat.nth (fun ρ => ρ.Prime ∧ Nat.ModEq p ρ 1) j ≤ x ^ p := by
  set S := (x ^ p - 1).primeFactors with hSdef
  set S0 := S.filter (fun ρ => ¬ Nat.ModEq p ρ 1) with hS0def
  set S1 := S.filter (fun ρ => Nat.ModEq p ρ 1) with hS1def
  have hcard_add : S0.card + S1.card = S.card := by
    have h := Finset.card_filter_add_card_filter_not (s := S) (fun ρ => Nat.ModEq p ρ 1)
    simpa [hS0def, hS1def, add_comm] using h
  have hS1pos : 0 < S1.card := by
    obtain ⟨ρ, hmem, hmod⟩ := hs1
    have hmem1 : ρ ∈ S1 := Finset.mem_filter.mpr ⟨hmem, hmod⟩
    exact Finset.card_pos.mpr ⟨ρ, hmem1⟩
  have hk_lt : S0.card < S.card := by omega
  have hS0P : ∀ q ∈ S0, (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) q := by
    intro q hq
    simp only [hS0def, Finset.mem_filter] at hq
    exact ⟨Nat.prime_of_mem_primeFactors hq.1, hq.2⟩
  have hS1P : ∀ q ∈ S1, (fun ρ => ρ.Prime ∧ Nat.ModEq p ρ 1) q := by
    intro q hq
    simp only [hS1def, Finset.mem_filter] at hq
    exact ⟨Nat.prime_of_mem_primeFactors hq.1, hq.2⟩
  have hprod0 :
      ∏ i ∈ Finset.range S0.card, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i ≤
        ∏ q ∈ S0, q :=
    prod_nth_le_prod S0 hS0P
  have hprod1 :
      ∏ j ∈ Finset.range S1.card, Nat.nth (fun ρ => ρ.Prime ∧ Nat.ModEq p ρ 1) j ≤
        ∏ q ∈ S1, q :=
    prod_nth_le_prod S1 hS1P
  have hpos : ∀ i < S0.card, 0 < Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i := by
    intro i hi
    have hmem := mem_nth_of_card_lt S0 hS0P hi
    exact hmem.1.pos
  have hS0dvd : ∀ ρ ∈ S0, ρ ∣ x - 1 := by
    intro ρ hmem
    simp only [hS0def, Finset.mem_filter] at hmem
    have hprime : ρ.Prime := Nat.prime_of_mem_primeFactors hmem.1
    have hdvd : ρ ∣ x ^ p - 1 := Nat.dvd_of_mem_primeFactors hmem.1
    exact mem_s0_dvd_sub_one hp hx hprime hdvd hmem.2
  have hprod_S0_dvd : ∏ q ∈ S0, q ∣ x - 1 := by
    apply Finset.prod_primes_dvd (x - 1)
    · intro q hq
      simp only [hS0def, Finset.mem_filter] at hq
      exact (Nat.prime_of_mem_primeFactors hq.1).prime
    · exact hS0dvd
  have hprod_S_dvd : ∏ q ∈ S, q ∣ x ^ p - 1 := Nat.prod_primeFactors_dvd (x ^ p - 1)
  have hprod_split : (∏ q ∈ S0, q) * (∏ q ∈ S1, q) = ∏ q ∈ S, q := by
    have h := Finset.prod_filter_mul_prod_filter_not S (fun ρ => Nat.ModEq p ρ 1) (fun q => q)
    have h2 : (∏ q ∈ S1, q) * (∏ q ∈ S0, q) = ∏ q ∈ S, q := by
      simpa [hS0def, hS1def] using h
    calc (∏ q ∈ S0, q) * (∏ q ∈ S1, q) = (∏ q ∈ S1, q) * (∏ q ∈ S0, q) := mul_comm _ _
      _ = ∏ q ∈ S, q := h2
  have hcard_sub : S.card - S0.card = S1.card := by omega
  have hx0 : 0 < x - 1 := Nat.sub_pos_of_lt hx
  have hxp_gt1 : (1 : ℕ) < x ^ p := one_lt_pow₀ hx hp.pos.ne'
  have hNpos : 0 < x ^ p - 1 := Nat.sub_pos_of_lt hxp_gt1
  have hle_S0 : ∏ q ∈ S0, q ≤ x - 1 := Nat.le_of_dvd hx0 hprod_S0_dvd
  have hle_S : ∏ q ∈ S, q ≤ x ^ p - 1 := Nat.le_of_dvd hNpos hprod_S_dvd
  refine ⟨S0.card, hk_lt, hpos, ?_, ?_⟩
  · calc 1 + ∏ i ∈ Finset.range S0.card, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i
        ≤ 1 + ∏ q ∈ S0, q := Nat.add_le_add_left hprod0 1
      _ ≤ 1 + (x - 1) := Nat.add_le_add_left hle_S0 1
      _ = x := by omega
  · have hrange_eq : S.card - S0.card = S1.card := hcard_sub
    rw [hrange_eq]
    calc 1 + (∏ i ∈ Finset.range S0.card, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i) *
            ∏ j ∈ Finset.range S1.card, Nat.nth (fun ρ => ρ.Prime ∧ Nat.ModEq p ρ 1) j
        ≤ 1 + (∏ q ∈ S0, q) * (∏ q ∈ S1, q) := Nat.add_le_add_left (Nat.mul_le_mul hprod0 hprod1) 1
      _ = 1 + ∏ q ∈ S, q := by rw [hprod_split]
      _ ≤ 1 + (x ^ p - 1) := Nat.add_le_add_left hle_S 1
      _ = x ^ p := by
          have hge : (1 : ℕ) ≤ x ^ p := le_of_lt hxp_gt1
          omega

private theorem phi_eq_geom {p : ℕ} (hp : p.Prime) (x : ℤ) :
    (cyclotomic p ℤ).eval x = ∑ i ∈ Finset.range p, x ^ i := by
  have : Fact p.Prime := ⟨hp⟩
  rw [cyclotomic_prime]
  simp

private theorem phi_gt_one {p x : ℕ} (hp : p.Prime) (hx : 1 < x) :
    1 < ∑ i ∈ Finset.range p, x ^ i := by
  have h1mem : (1 : ℕ) ∈ Finset.range p := Finset.mem_range.mpr hp.two_le
  have hlt : ∑ i ∈ Finset.range p, (1 : ℕ) < ∑ i ∈ Finset.range p, x ^ i :=
    Finset.sum_lt_sum (fun i _ => Nat.one_le_pow i x (le_of_lt hx))
      ⟨1, h1mem, by simpa using hx⟩
  have hsum1 : ∑ _i ∈ Finset.range p, (1 : ℕ) = p := by simp
  rw [hsum1] at hlt
  exact lt_trans hp.one_lt hlt

private theorem s1_nonempty_of_not_dvd {p x : ℕ} (hp : p.Prime) (hx : 1 < x)
    (hndvd : ¬ p ∣ x - 1) :
    ∃ ρ ∈ (x ^ p - 1).primeFactors, Nat.ModEq p ρ 1 := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hxpos : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hx0
  have hxp_gt1 : (1 : ℕ) < x ^ p := one_lt_pow₀ hx hp.pos.ne'
  have hNpos : 0 < x ^ p - 1 := Nat.sub_pos_of_lt hxp_gt1
  have hNne : x ^ p - 1 ≠ 0 := ne_of_gt hNpos
  have hxp1 : (1 : ℕ) ≤ x ^ p := le_of_lt hxp_gt1
  have hNcast : ((x ^ p - 1 : ℕ) : ℤ) = (x : ℤ) ^ p - 1 := by
    rw [Nat.cast_sub hxp1]
    simp
  have hx1cast : ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 := by
    rw [Nat.cast_sub (le_of_lt hx)]
    simp
  have hphi1 : 1 < ∑ i ∈ Finset.range p, x ^ i := phi_gt_one hp hx
  obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hphi1)
  have hphi_cast : ((∑ i ∈ Finset.range p, x ^ i : ℕ) : ℤ) = (cyclotomic p ℤ).eval (x : ℤ) := by
    rw [phi_eq_geom hp]
    simp
  have hqdvdZ : (q : ℤ) ∣ (cyclotomic p ℤ).eval (x : ℤ) := by
    rw [← hphi_cast]
    exact Int.natCast_dvd_natCast.mpr hqdvd
  have hqne : q ≠ p := by
    intro heq
    have hqeqp : (q : ℤ) = (p : ℤ) := by rw [heq]
    have hpdvd_phi : (p : ℤ) ∣ (cyclotomic p ℤ).eval (x : ℤ) := by
      rw [← hqeqp]
      exact hqdvdZ
    have hPhi_dvd_pow : (cyclotomic p ℤ).eval (x : ℤ) ∣ (x : ℤ) ^ p - 1 :=
      ⟨(x : ℤ) - 1, (cyclo_mul_sub_one_eq hp (x : ℤ)).symm⟩
    have hpdvd_pow : (p : ℤ) ∣ (x : ℤ) ^ p - 1 := dvd_trans hpdvd_phi hPhi_dvd_pow
    have hpdvd_sub : (p : ℤ) ∣ (x : ℤ) - 1 :=
      ((prime_dvd_pow_self_sub_one_iff hp hxpos).mp hpdvd_pow).1
    have hpdvd_subN : p ∣ x - 1 := by
      have : (p : ℤ) ∣ ((x - 1 : ℕ) : ℤ) := by rw [hx1cast]; exact hpdvd_sub
      exact Int.natCast_dvd_natCast.mp this
    exact hndvd hpdvd_subN
  have hmod : Nat.ModEq p q 1 :=
    prime_modEq_one_of_dvd_cyclotomic_eval hqprime hp hqne hxpos hqdvdZ
  have hPhi_dvd_pow : (cyclotomic p ℤ).eval (x : ℤ) ∣ (x : ℤ) ^ p - 1 :=
    ⟨(x : ℤ) - 1, (cyclo_mul_sub_one_eq hp (x : ℤ)).symm⟩
  have hqdvd_pow : (q : ℤ) ∣ (x : ℤ) ^ p - 1 := dvd_trans hqdvdZ hPhi_dvd_pow
  have hqdvd_N : q ∣ x ^ p - 1 := by
    have : (q : ℤ) ∣ ((x ^ p - 1 : ℕ) : ℤ) := by rw [hNcast]; exact hqdvd_pow
    exact Int.natCast_dvd_natCast.mp this
  have hmem : q ∈ (x ^ p - 1).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hqprime, hqdvd_N, hNne⟩
  exact ⟨q, hmem, hmod⟩

private theorem phi_gt_prime {p x : ℕ} (hp : p.Prime) (hx : 1 < x) :
    (p : ℤ) < (cyclotomic p ℤ).eval (x : ℤ) := by
  rw [phi_eq_geom hp]
  have hx1 : (1 : ℤ) ≤ (x : ℤ) := by exact_mod_cast le_of_lt hx
  have hxlt : (1 : ℤ) < (x : ℤ) := by exact_mod_cast hx
  calc (p : ℤ) = ∑ _i ∈ Finset.range p, (1 : ℤ) := by simp
    _ < ∑ i ∈ Finset.range p, (x : ℤ) ^ i := by
        apply Finset.sum_lt_sum
        · intro i _
          exact one_le_pow₀ hx1
        · exact ⟨1, Finset.mem_range.mpr hp.two_le, by simpa using hxlt⟩

private theorem sq_dvd_phi_sub_p {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {x t : ℕ} (hx : (x : ℤ) = 1 + (p : ℤ) * (t : ℤ)) :
    (p : ℤ) ^ 2 ∣ (cyclotomic p ℤ).eval (x : ℤ) - (p : ℤ) := by
  have h := odd_sq_dvd_geom_sum₂_sub (R := ℤ) (1 : ℤ) (t : ℤ) (p := p) hodd
  have hsum : (∑ i ∈ Finset.range p, ((1 : ℤ) + (p : ℤ) * (t : ℤ)) ^ i * (1 : ℤ) ^ (p - 1 - i))
      = (cyclotomic p ℤ).eval (x : ℤ) := by
    rw [phi_eq_geom hp]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx]
    simp
  have hpow : (p : ℤ) * (1 : ℤ) ^ (p - 1) = (p : ℤ) := by simp
  rw [hsum, hpow] at h
  exact h

private theorem exists_m_of_sq_dvd {p : ℕ} (hp : p.Prime) {Φ : ℤ}
    (hdvd : (p : ℤ) ^ 2 ∣ Φ - (p : ℤ)) (hlt : (p : ℤ) < Φ) :
    ∃ m : ℤ, Φ = (p : ℤ) * m ∧ 1 < m ∧ ¬ (p : ℤ) ∣ m := by
  obtain ⟨k, hk⟩ := hdvd
  have hppos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hpsq : (0 : ℤ) < (p : ℤ) ^ 2 := by positivity
  have hsub : (0 : ℤ) < Φ - (p : ℤ) := by omega
  rw [hk] at hsub
  have hkpos : (0 : ℤ) < k := pos_of_mul_pos_right hsub (le_of_lt hpsq)
  use 1 + k * (p : ℤ)
  constructor
  · have hΦ : Φ = (p : ℤ) + (p : ℤ) ^ 2 * k := by rw [← hk]; ring
    rw [hΦ]
    ring
  · constructor
    · have hkp : (0 : ℤ) < k * (p : ℤ) := mul_pos hkpos hppos
      linarith
    · intro hdvd2
      have hdvd3 : (p : ℤ) ∣ k * (p : ℤ) := dvd_mul_left _ _
      have hdvd1 : (p : ℤ) ∣ (1 : ℤ) := by
        have hsub2 : (1 + k * (p : ℤ)) - k * (p : ℤ) = 1 := by ring
        have h := dvd_sub hdvd2 hdvd3
        simpa [hsub2] using h
      have hle : (p : ℕ) ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa using hdvd1)
      have hle2 : p ≤ 1 := Nat.le_of_dvd (by decide) hle
      have hlt2 : 1 < p := hp.one_lt
      omega

private theorem s1_nonempty_of_dvd_odd {p x : ℕ} (hp : p.Prime) (hx : 1 < x)
    (hne2 : p ≠ 2) (hdvd : p ∣ x - 1) :
    ∃ ρ ∈ (x ^ p - 1).primeFactors, Nat.ModEq p ρ 1 := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hxpos : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hx0
  have hxp_gt1 : (1 : ℕ) < x ^ p := one_lt_pow₀ hx hp.pos.ne'
  have hNpos : 0 < x ^ p - 1 := Nat.sub_pos_of_lt hxp_gt1
  have hNne : x ^ p - 1 ≠ 0 := ne_of_gt hNpos
  have hxp1 : (1 : ℕ) ≤ x ^ p := le_of_lt hxp_gt1
  have hNcast : ((x ^ p - 1 : ℕ) : ℤ) = (x : ℤ) ^ p - 1 := by
    rw [Nat.cast_sub hxp1]
    simp
  obtain ⟨t, ht⟩ := hdvd
  have hx1 : (1 : ℕ) ≤ x := le_of_lt hx
  have hxeq : x = 1 + p * t := by
    have hsub : x - 1 + 1 = x := Nat.sub_add_cancel hx1
    rw [ht] at hsub
    omega
  have hxZ : (x : ℤ) = 1 + (p : ℤ) * (t : ℤ) := by
    have hcast : ((x : ℕ) : ℤ) = ((1 + p * t : ℕ) : ℤ) := by rw [hxeq]
    simpa using hcast
  have hodd : Odd p := hp.odd_of_ne_two hne2
  have hsq : (p : ℤ) ^ 2 ∣ (cyclotomic p ℤ).eval (x : ℤ) - (p : ℤ) :=
    sq_dvd_phi_sub_p hp hodd hxZ
  have hlt : (p : ℤ) < (cyclotomic p ℤ).eval (x : ℤ) := phi_gt_prime hp hx
  obtain ⟨m, hm_eq, hm_gt1, hm_ndiv⟩ := exists_m_of_sq_dvd hp hsq hlt
  have hm_nonneg : (0 : ℤ) ≤ m := le_of_lt (lt_trans zero_lt_one hm_gt1)
  set m_nat := m.toNat with hm_nat_def
  have hm_cast : ((m_nat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm_nonneg
  have hm_nat_gt1 : 1 < m_nat := by
    have h : (1 : ℤ) < ((m_nat : ℕ) : ℤ) := by rw [hm_cast]; exact hm_gt1
    exact_mod_cast h
  have hm_nat_ndiv : ¬ p ∣ m_nat := by
    intro hdiv
    have hdivZ : (p : ℤ) ∣ ((m_nat : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hdiv
    rw [hm_cast] at hdivZ
    exact hm_ndiv hdivZ
  obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hm_nat_gt1)
  have hqdvdZ : (q : ℤ) ∣ m := by
    have h : (q : ℤ) ∣ ((m_nat : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hqdvd
    rw [hm_cast] at h
    exact h
  have hm_dvd_phi : m ∣ (cyclotomic p ℤ).eval (x : ℤ) := ⟨(p : ℤ), by rw [hm_eq]; ring⟩
  have hqdvd_phi : (q : ℤ) ∣ (cyclotomic p ℤ).eval (x : ℤ) := dvd_trans hqdvdZ hm_dvd_phi
  have hqne : q ≠ p := by
    intro heq
    have hdiv : p ∣ m_nat := by simpa [heq] using hqdvd
    exact hm_nat_ndiv hdiv
  have hmod : Nat.ModEq p q 1 :=
    prime_modEq_one_of_dvd_cyclotomic_eval hqprime hp hqne hxpos hqdvd_phi
  have hPhi_dvd_pow : (cyclotomic p ℤ).eval (x : ℤ) ∣ (x : ℤ) ^ p - 1 :=
    ⟨(x : ℤ) - 1, (cyclo_mul_sub_one_eq hp (x : ℤ)).symm⟩
  have hqdvd_pow : (q : ℤ) ∣ (x : ℤ) ^ p - 1 := dvd_trans hqdvd_phi hPhi_dvd_pow
  have hqdvd_N : q ∣ x ^ p - 1 := by
    have : (q : ℤ) ∣ ((x ^ p - 1 : ℕ) : ℤ) := by rw [hNcast]; exact hqdvd_pow
    exact Int.natCast_dvd_natCast.mp this
  have hmem : q ∈ (x ^ p - 1).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hqprime, hqdvd_N, hNne⟩
  exact ⟨q, hmem, hmod⟩

private theorem prime_eq_two_of_not_modeq {ρ : ℕ} (hρ : ρ.Prime)
    (h : ¬ Nat.ModEq 2 ρ 1) : ρ = 2 := by
  rcases hρ.eq_two_or_odd with rfl | hmod
  · rfl
  · exfalso
    apply h
    change ρ % 2 = 1 % 2
    simpa using hmod

private theorem nth_zero_le_of_mem {P : ℕ → Prop} {x : ℕ} (hx : P x) :
    Nat.nth P 0 ≤ x := by
  by_cases hfin : (Set.ofPred P).Finite
  · have hcard : 0 < hfin.toFinset.card := by
      have hmem : x ∈ hfin.toFinset := by
        rw [hfin.mem_toFinset]
        exact hx
      exact Finset.card_pos.mpr ⟨x, hmem⟩
    have hleast := Nat.isLeast_nth_of_lt_card (p := P) hfin (n := 0) hcard
    have hxmem : x ∈ {i | P i ∧ ∀ k < (0 : ℕ), Nat.nth P k < i} :=
      ⟨hx, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    exact hleast.2 hxmem
  · have hinf : (Set.ofPred P).Infinite := Set.not_finite.mp hfin
    have hleast := Nat.isLeast_nth_of_infinite (p := P) hinf 0
    have hxmem : x ∈ {i | P i ∧ ∀ k < (0 : ℕ), Nat.nth P k < i} :=
      ⟨hx, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    exact hleast.2 hxmem

private theorem p2_empty_case {x : ℕ} (hx : 1 < x)
    (hempty : ¬ ∃ ρ ∈ (x ^ 2 - 1).primeFactors, Nat.ModEq 2 ρ 1) :
    ∃ k < (x ^ 2 - 1).primeFactors.card,
      (∀ i < k, 0 < Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 2 ρ 1) i) ∧
      1 + ∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 2 ρ 1) i ≤ x ∧
        1 + (∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq 2 ρ 1) i) *
            ∏ j ∈ Finset.range ((x ^ 2 - 1).primeFactors.card - k),
              Nat.nth (fun ρ => ρ.Prime ∧ Nat.ModEq 2 ρ 1) j ≤ x ^ 2 := by
  have hx2le : (2 : ℕ) ≤ x := by omega
  have hpow4 : (4 : ℕ) ≤ x ^ 2 := by
    calc (4 : ℕ) = 2 ^ 2 := by decide
      _ ≤ x ^ 2 := Nat.pow_le_pow_left hx2le 2
  have hxp_gt1 : (1 : ℕ) < x ^ 2 := by omega
  have hNpos : 0 < x ^ 2 - 1 := Nat.sub_pos_of_lt hxp_gt1
  have hNne : x ^ 2 - 1 ≠ 0 := ne_of_gt hNpos
  have hNgt1 : 1 < x ^ 2 - 1 := by omega
  have hall2 : ∀ ρ ∈ (x ^ 2 - 1).primeFactors, ρ = 2 := by
    intro ρ hmem
    have hprime : ρ.Prime := Nat.prime_of_mem_primeFactors hmem
    have hnmod : ¬ Nat.ModEq 2 ρ 1 := fun hmod => hempty ⟨ρ, hmem, hmod⟩
    exact prime_eq_two_of_not_modeq hprime hnmod
  have hcard_le1 : (x ^ 2 - 1).primeFactors.card ≤ 1 := by
    have hsub : (x ^ 2 - 1).primeFactors ⊆ {2} := by
      intro ρ hmem
      simp only [Finset.mem_singleton]
      exact hall2 ρ hmem
    calc (x ^ 2 - 1).primeFactors.card ≤ ({2} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := by simp
  have hcard_ge1 : 1 ≤ (x ^ 2 - 1).primeFactors.card := by
    obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hNgt1)
    have hmem : q ∈ (x ^ 2 - 1).primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨hqprime, hqdvd, hNne⟩
    exact Finset.card_pos.mpr ⟨q, hmem⟩
  have hcard : (x ^ 2 - 1).primeFactors.card = 1 := by omega
  refine ⟨0, by rw [hcard]; decide, fun i hi => absurd hi (Nat.not_lt_zero i), ?_, ?_⟩
  · simp
    omega
  · simp only [Finset.range_zero, Finset.prod_empty, hcard, Nat.sub_zero]
    rw [Finset.prod_range_one]
    have hle3 : Nat.nth (fun ρ => ρ.Prime ∧ Nat.ModEq 2 ρ 1) 0 ≤ 3 := by
      apply nth_zero_le_of_mem
      constructor
      · exact Nat.prime_three
      · decide
    omega

/-- The `p`-hybrid bound (Theorem 1 for prime `n = p`). For a prime `p`, `x > 1` and
`ω_p = ω(x^p - 1)`, let `r_{i,0}` and `r_{j,1}` enumerate the primes `≢ 1` and `≡ 1 (mod p)`
(`Nat.nth`, `0`-indexed here). The source's
`x ≥ min_{0 ≤ k < ω_p} max(1 + ∏_{i ≤ k} r_{i,0},
  (1 + ∏_{i ≤ k} r_{i,0} ∏_{j ≤ ω_p - k} r_{j,1})^{1/p})`
is stated equivalently as the existence of `k < ω_p` meeting both bounds, the second after
raising to the `p`-th power. The source's factors are all primes, and since `Nat.nth`
returns `0` past the end of a finite set, the statement requires every factor to be a genuine
(positive) element of its prime class.

Source: Gustav Kjærbye Bagger, *Hybrid Bounds for Prime Divisors*, INTEGERS 26 (2026),
Article A95, Proposition 2 (`integers-2026-A95-prop-2`). -/
public theorem prime_hybrid_bound {p : ℕ} (hp : p.Prime) {x : ℕ} (hx : 1 < x) :
    ∃ k < (x ^ p - 1).primeFactors.card,
      (∀ i < k, 0 < Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i) ∧
      1 + ∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i ≤ x ∧
        1 + (∏ i ∈ Finset.range k, Nat.nth (fun ρ => ρ.Prime ∧ ¬ Nat.ModEq p ρ 1) i) *
            ∏ j ∈ Finset.range ((x ^ p - 1).primeFactors.card - k),
              Nat.nth (fun ρ => ρ.Prime ∧ Nat.ModEq p ρ 1) j ≤ x ^ p := by
  by_cases hs1 : ∃ ρ ∈ (x ^ p - 1).primeFactors, Nat.ModEq p ρ 1
  · exact main_of_s1_nonempty hp hx hs1
  · by_cases hp2 : p = 2
    · subst hp2
      exact p2_empty_case hx hs1
    · by_cases hdiv : p ∣ x - 1
      · have hs1' := s1_nonempty_of_dvd_odd hp hx hp2 hdiv
        exact absurd hs1' hs1
      · have hs1' := s1_nonempty_of_not_dvd hp hx hdiv
        exact absurd hs1' hs1

end MetaMathlibExt
