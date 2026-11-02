/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.NumberTheory.PowModTotient
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Kummer's congruence

This file proves Kummer's congruence for the modified Bernoulli quotients using
Voronoi's finite-sum congruence and the p-adic norm on `ℚ`.
-/

@[expose] public section

namespace MetaMathlibExt

private theorem kummer_prime_ne_two {p k : ℕ} [Fact (Nat.Prime p)]
    (hk : ¬ (p - 1) ∣ k) : p ≠ 2 := by
  intro hp
  subst p
  exact hk (by simp)

private theorem kummer_index_pos {p k : ℕ} (hk : ¬ (p - 1) ∣ k) : 0 < k := by
  apply Nat.pos_of_ne_zero
  intro hk0
  subst k
  exact hk (dvd_zero _)

private theorem kummer_bernoulli_norm_le {p k : ℕ} [Fact (Nat.Prime p)]
    (hp2 : p ≠ 2) : padicNorm p (bernoulli k) ≤ (p : ℚ) := by
  have hp := (Fact.out : Nat.Prime p)
  have hpq : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_le
  rcases lt_trichotomy k 1 with hk | rfl | hk
  · have hk0 : k = 0 := by omega
    subst k
    simpa [bernoulli_zero, padicNorm.one] using hpq
  · have hpdvd2 : ¬p ∣ 2 := by
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have hnorm2 : padicNorm p (2 : ℚ) = 1 := (padicNorm.nat_eq_one_iff 2).2 hpdvd2
    rw [bernoulli_one, padicNorm.div, padicNorm.neg, hnorm2]
    simpa [padicNorm.one] using hpq
  · rcases Nat.even_or_odd k with heven | hodd
    · obtain ⟨d, hd⟩ := heven
      have hkd : k = 2 * d := by omega
      rw [hkd]
      obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen d
      have hB : bernoulli (2 * d) = (z : ℚ) -
          ∑ q ∈ Finset.range (2 * d + 2) with q.Prime ∧ q - 1 ∣ 2 * d,
            (1 : ℚ) / q :=
        eq_sub_iff_add_eq.mpr hz.symm
      rw [hB]
      refine padicNorm.sub.trans (max_le ?_ ?_)
      · exact (padicNorm.of_int z).trans hpq
      · refine padicNorm.sum_le' ?_ (by positivity)
        intro q hq
        obtain ⟨-, hqprime, -⟩ := Finset.mem_filter.mp hq
        by_cases hqp : q = p
        · subst q
          simp [show (p : ℚ) ≠ 0 by positivity]
        · have hnot : ¬p ∣ q := by
            intro hdvd
            exact hqp ((Nat.prime_dvd_prime_iff_eq hp hqprime).mp hdvd).symm
          rw [padicNorm.div, padicNorm.one, (padicNorm.nat_eq_one_iff q).2 hnot]
          simpa using hpq
    · rw [bernoulli_eq_zero_of_odd hodd hk, padicNorm.zero]
      positivity

private theorem kummer_sum_mul_mod_pow (N c k : ℕ) (hN : 0 < N) (hc : c.Coprime N) :
    ∑ j ∈ Finset.range N, ((c * j) % N) ^ k = ∑ j ∈ Finset.range N, j ^ k := by
  let f : Fin N → Fin N := fun j => ⟨(c * j) % N, Nat.mod_lt _ hN⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    have hval := congrArg (fun x : Fin N => x.1) hab
    change (c * a.1) % N = (c * b.1) % N at hval
    have hmod : c * a.1 ≡ c * b.1 [MOD N] := hval
    have habmod := hmod.cancel_left_of_coprime hc.symm.gcd_eq_one
    exact habmod.eq_of_lt_of_lt a.2 b.2
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  refine Finset.sum_bij (fun j _ => (c * j) % N) ?_ ?_ ?_ ?_
  · intro j _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hN)
  · intro a ha b hb hab
    have hmod : c * a ≡ c * b [MOD N] := hab
    have habmod := hmod.cancel_left_of_coprime hc.symm.gcd_eq_one
    exact habmod.eq_of_lt_of_lt (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)
  · intro b hb
    obtain ⟨a, ha⟩ := hf_surj ⟨b, Finset.mem_range.mp hb⟩
    have haval := congrArg (fun x : Fin N => x.1) ha
    change (c * a.1) % N = b at haval
    exact ⟨a.1, Finset.mem_range.mpr a.2, haval⟩
  · simp

private theorem kummer_add_pow_split (x y k : ℕ) (hk : 0 < k) :
    (x + y) ^ k = y ^ k + k * x * y ^ (k - 1) +
      ∑ i ∈ Finset.Icc 2 k, x ^ i * y ^ (k - i) * k.choose i := by
  have hrange : Finset.range (k + 1) = {0, 1} ∪ Finset.Icc 2 k := by
    ext i
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_Icc]
    omega
  have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Icc 2 k) := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc]
    omega
  rw [add_pow, hrange, Finset.sum_union hdisj]
  simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
    Finset.sum_singleton, pow_zero, one_mul, Nat.choose_zero_right, Nat.choose_one_right]
  simp only [Nat.sub_zero, Nat.cast_id, pow_one]
  ac_rfl

private def kummer_W (N c k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range N, j ^ (k - 1) * (c * j / N)

private def kummer_U (p s c k : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range (p ^ s)).filter (fun j => ¬p ∣ j),
    j ^ (k - 1) * (c * j / p ^ s)

private def kummer_R (N c k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range N, (c * j / N) * ((c * j) % N) ^ (k - 1)

private def kummer_H (N c k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range N, ∑ i ∈ Finset.Icc 2 k,
    (N * (c * j / N)) ^ i * ((c * j) % N) ^ (k - i) * k.choose i

private def kummer_D (N c k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range N, ((c * j / N : ℕ) : ℤ) *
    ((((c * j) % N : ℕ) : ℤ) ^ (k - 1) - ((c * j : ℕ) : ℤ) ^ (k - 1))

private theorem kummer_pointwise_expansion (N c k j : ℕ) (hk : 0 < k) :
    (c * j) ^ k = ((c * j) % N) ^ k +
      k * N * ((c * j / N) * ((c * j) % N) ^ (k - 1)) +
      ∑ i ∈ Finset.Icc 2 k,
        (N * (c * j / N)) ^ i * ((c * j) % N) ^ (k - i) * k.choose i := by
  have hdiv : c * j = N * (c * j / N) + (c * j) % N := by
    nth_rw 1 [← Nat.div_add_mod (c * j) N]
  calc
    (c * j) ^ k = (N * (c * j / N) + (c * j) % N) ^ k := congrArg (· ^ k) hdiv
    _ = ((c * j) % N) ^ k + k * (N * (c * j / N)) *
        ((c * j) % N) ^ (k - 1) +
        ∑ i ∈ Finset.Icc 2 k,
          (N * (c * j / N)) ^ i * ((c * j) % N) ^ (k - i) * k.choose i :=
      kummer_add_pow_split _ _ _ hk
    _ = _ := by ring

private theorem kummer_power_sum_identity (N c k : ℕ) (hN : 0 < N)
    (hc : c.Coprime N) (hk : 0 < k) :
    c ^ k * (∑ j ∈ Finset.range N, j ^ k) =
      (∑ j ∈ Finset.range N, j ^ k) + k * N * kummer_R N c k + kummer_H N c k := by
  calc
    c ^ k * (∑ j ∈ Finset.range N, j ^ k) =
        ∑ j ∈ Finset.range N, (c * j) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow]
    _ = ∑ j ∈ Finset.range N,
        (((c * j) % N) ^ k +
          k * N * ((c * j / N) * ((c * j) % N) ^ (k - 1)) +
          ∑ i ∈ Finset.Icc 2 k,
            (N * (c * j / N)) ^ i * ((c * j) % N) ^ (k - i) * k.choose i) := by
      apply Finset.sum_congr rfl
      intro j _
      exact kummer_pointwise_expansion N c k j hk
    _ = (∑ j ∈ Finset.range N, ((c * j) % N) ^ k) +
        k * N * kummer_R N c k + kummer_H N c k := by
      simp only [Finset.sum_add_distrib, kummer_R, kummer_H]
      rw [Finset.mul_sum]
    _ = _ := by rw [kummer_sum_mul_mod_pow N c k hN hc]

private theorem kummer_R_sub_W (N c k : ℕ) :
    (kummer_R N c k : ℤ) - (c : ℤ) ^ (k - 1) * (kummer_W N c k : ℤ) =
      kummer_D N c k := by
  simp only [kummer_R, kummer_W, kummer_D, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow]
  ring

private theorem kummer_D_dvd (N c k : ℕ) : (N : ℤ) ∣ kummer_D N c k := by
  apply Finset.dvd_sum
  intro j _
  apply dvd_mul_of_dvd_right
  have hmod := (Nat.mod_modEq (c * j) N).pow (k - 1)
  have hdvd := hmod.dvd
  rw [← neg_sub]
  exact dvd_neg.mpr hdvd

private def kummer_padicBound (p : ℕ) (e : ℤ) (q : ℚ) : Prop :=
  padicNorm p q ≤ (p : ℚ) ^ (-e)

private theorem kummer_bound_mono {p : ℕ} [Fact (Nat.Prime p)] {e f : ℤ} {q : ℚ}
    (hef : f ≤ e) (hq : kummer_padicBound p e q) : kummer_padicBound p f q := by
  exact hq.trans (zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : Nat.Prime p).one_le)
    (neg_le_neg hef))

private theorem kummer_bound_sub {p : ℕ} [Fact (Nat.Prime p)] {e : ℤ} {q r : ℚ}
    (hq : kummer_padicBound p e q) (hr : kummer_padicBound p e r) :
    kummer_padicBound p e (q - r) := by
  exact padicNorm.sub.trans (max_le hq hr)

private theorem kummer_bound_add {p : ℕ} [Fact (Nat.Prime p)] {e : ℤ} {q r : ℚ}
    (hq : kummer_padicBound p e q) (hr : kummer_padicBound p e r) :
    kummer_padicBound p e (q + r) := by
  exact padicNorm.nonarchimedean.trans (max_le hq hr)

private theorem kummer_bound_sum {p : ℕ} [Fact (Nat.Prime p)] {e : ℤ}
    {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, kummer_padicBound p e (f i)) :
    kummer_padicBound p e (∑ i ∈ s, f i) := by
  exact padicNorm.sum_le' hf (zpow_nonneg (by positivity) _)

private theorem kummer_bound_mul {p : ℕ} [Fact (Nat.Prime p)] {e f : ℤ} {q r : ℚ}
    (hq : kummer_padicBound p e q) (hr : kummer_padicBound p f r) :
    kummer_padicBound p (e + f) (q * r) := by
  rw [kummer_padicBound, padicNorm.mul]
  calc
    padicNorm p q * padicNorm p r ≤ (p : ℚ) ^ (-e) * (p : ℚ) ^ (-f) :=
      mul_le_mul hq hr (padicNorm.nonneg _) (zpow_nonneg (by positivity) _)
    _ = (p : ℚ) ^ (-(e + f)) := by
      rw [← zpow_add₀ (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)]
      congr 1
      ring

private theorem kummer_bound_int {p : ℕ} [Fact (Nat.Prime p)] (z : ℤ) :
    kummer_padicBound p 0 z := by
  simpa [kummer_padicBound] using padicNorm.of_int (p := p) z

private theorem kummer_bound_nat_div {p : ℕ} [Fact (Nat.Prime p)] (a d : ℕ) (hd : 0 < d) :
    kummer_padicBound p (-(d : ℤ)) ((a : ℚ) / d) := by
  by_cases ha : a = 0
  · subst a
    simp [kummer_padicBound]
  · have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    have hdq : (d : ℚ) ≠ 0 := by positivity
    rw [kummer_padicBound, padicNorm.eq_zpow_of_nonzero (div_ne_zero haq hdq),
      padicValRat.div haq hdq, padicValRat.of_nat, padicValRat.of_nat]
    apply zpow_le_zpow_right₀ (by exact_mod_cast (Fact.out : Nat.Prime p).one_le)
    have hv := Nat.padicValNat_le_self (p := p) d
    omega

private theorem kummer_bound_p {p : ℕ} [Fact (Nat.Prime p)] :
    kummer_padicBound p 1 (p : ℚ) := by
  simp [kummer_padicBound, padicNorm.padicNorm_p_of_prime]

private theorem kummer_bound_p_pow {p s : ℕ} [Fact (Nat.Prime p)] :
    kummer_padicBound p (s : ℤ) ((p : ℚ) ^ s) := by
  induction s with
  | zero => simp [kummer_padicBound]
  | succ s ih =>
      rw [pow_succ]
      simpa [Nat.cast_succ] using kummer_bound_mul ih (kummer_bound_p (p := p))

private theorem kummer_bound_of_pow_dvd {p s : ℕ} [Fact (Nat.Prime p)] {z : ℤ}
    (hz : (p ^ s : ℤ) ∣ z) : kummer_padicBound p (s : ℤ) z := by
  exact (padicNorm.dvd_iff_norm_le (p := p)).mp hz

private theorem kummer_H_dvd_sq (N c k : ℕ) : N ^ 2 ∣ kummer_H N c k := by
  apply Finset.dvd_sum
  intro j _
  apply Finset.dvd_sum
  intro i hi
  have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
  refine dvd_mul_of_dvd_left (dvd_mul_of_dvd_left ?_ _) _
  exact pow_dvd_pow_of_dvd_of_le (dvd_mul_right N (c * j / N)) hi2

private theorem kummer_H_bound {p s c k : ℕ} [Fact (Nat.Prime p)] (hk : 0 < k) :
    kummer_padicBound p ((s : ℤ) - k)
      ((kummer_H (p ^ s) c k : ℚ) / ((k : ℚ) * (p ^ s : ℕ))) := by
  obtain ⟨A, hA⟩ := kummer_H_dvd_sq (p ^ s) c k
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hkq : (k : ℚ) ≠ 0 := by positivity
  have heq : (kummer_H (p ^ s) c k : ℚ) / ((k : ℚ) * (p ^ s : ℕ)) =
      (p : ℚ) ^ s * ((A : ℚ) / k) := by
    rw [hA]
    push_cast
    field_simp
  rw [heq]
  simpa [sub_eq_add_neg] using
    kummer_bound_mul (kummer_bound_p_pow (p := p) (s := s))
      (kummer_bound_nat_div (p := p) A k hk)

private noncomputable def kummer_E (N k : ℕ) : ℚ :=
  ∑ i ∈ Finset.range k,
    bernoulli i * (Nat.choose (k + 1) i : ℚ) * (N : ℚ) ^ (k - i) / ((k : ℚ) + 1)

private theorem kummer_sum_range_pow_div (N k : ℕ) (hN : 0 < N) :
    (∑ j ∈ Finset.range N, (j : ℚ) ^ k) / (N : ℚ) = bernoulli k + kummer_E N k := by
  have hfactor :
      (∑ i ∈ Finset.range k,
        bernoulli i * (Nat.choose (k + 1) i : ℚ) * (N : ℚ) ^ (k + 1 - i) /
          ((k : ℚ) + 1)) = (N : ℚ) * kummer_E N k := by
    rw [kummer_E, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]
    ring
  rw [sum_range_pow, Finset.sum_range_succ, hfactor]
  have hlast : bernoulli k * (Nat.choose (k + 1) k : ℚ) *
      (N : ℚ) ^ (k + 1 - k) / ((k : ℚ) + 1) = bernoulli k * N := by
    rw [show k + 1 - k = 1 by omega, Nat.choose_succ_self_right]
    push_cast
    field_simp
  rw [hlast]
  field_simp
  ring

private theorem kummer_E_bound {p s k : ℕ} [Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    kummer_padicBound p ((s : ℤ) - k - 2) (kummer_E (p ^ s) k) := by
  apply kummer_bound_sum
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have hB : kummer_padicBound p (-1) (bernoulli i) := by
    simpa [kummer_padicBound] using kummer_bernoulli_norm_le (p := p) (k := i) hp2
  have hcoef : kummer_padicBound p (-(k + 1 : ℕ))
      ((Nat.choose (k + 1) i : ℚ) / ((k : ℚ) + 1)) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      kummer_bound_nat_div (p := p) (Nat.choose (k + 1) i) (k + 1) (by omega)
  have hpow : kummer_padicBound p ((s * (k - i) : ℕ) : ℤ)
      (((p ^ s : ℕ) : ℚ) ^ (k - i)) := by
    simpa [pow_mul] using kummer_bound_p_pow (p := p) (s := s * (k - i))
  have hterm := kummer_bound_mul (kummer_bound_mul hB hcoef) hpow
  have heq : bernoulli i * (Nat.choose (k + 1) i : ℚ) *
      ((p ^ s : ℕ) : ℚ) ^ (k - i) / ((k : ℚ) + 1) =
      (bernoulli i * ((Nat.choose (k + 1) i : ℚ) / ((k : ℚ) + 1))) *
        ((p ^ s : ℕ) : ℚ) ^ (k - i) := by ring
  rw [heq]
  refine kummer_bound_mono ?_ hterm
  have hs : s ≤ s * (k - i) := by
    have : 1 ≤ k - i := by omega
    simpa using Nat.mul_le_mul_left s this
  have hs' : (s : ℤ) ≤ (s * (k - i) : ℕ) := by exact_mod_cast hs
  omega

private theorem kummer_voronoi_identity (N c k : ℕ) (hN : 0 < N)
    (hc : c.Coprime N) (hk : 0 < k) :
    (((c : ℚ) ^ k - 1) * bernoulli k / k -
        (c : ℚ) ^ (k - 1) * kummer_W N c k) =
      (kummer_D N c k : ℚ) +
        (kummer_H N c k : ℚ) / ((k : ℚ) * N) -
        (((c : ℚ) ^ k - 1) / k) * kummer_E N k := by
  let S : ℚ := ∑ j ∈ Finset.range N, (j : ℚ) ^ k
  have hpower : (c : ℚ) ^ k * S = S +
      (k : ℚ) * N * kummer_R N c k + kummer_H N c k := by
    dsimp [S]
    exact_mod_cast kummer_power_sum_identity N c k hN hc hk
  have hmain : (((c : ℚ) ^ k - 1) * S) / ((k : ℚ) * N) =
      kummer_R N c k + (kummer_H N c k : ℚ) / ((k : ℚ) * N) := by
    field_simp
    linear_combination hpower
  have hfaul : S / (N : ℚ) = bernoulli k + kummer_E N k := by
    exact kummer_sum_range_pow_div N k hN
  have hB : bernoulli k = S / (N : ℚ) - kummer_E N k := by
    linarith
  have hRW : (kummer_R N c k : ℚ) -
      (c : ℚ) ^ (k - 1) * kummer_W N c k = kummer_D N c k := by
    exact_mod_cast kummer_R_sub_W N c k
  calc
    ((c : ℚ) ^ k - 1) * bernoulli k / k -
        (c : ℚ) ^ (k - 1) * kummer_W N c k =
      (((c : ℚ) ^ k - 1) * S) / ((k : ℚ) * N) -
        (((c : ℚ) ^ k - 1) / k) * kummer_E N k -
        (c : ℚ) ^ (k - 1) * kummer_W N c k := by
          rw [hB]
          ring
    _ = _ := by
      rw [hmain]
      linear_combination hRW

private theorem kummer_voronoi_bound {p s c k : ℕ} [Fact (Nat.Prime p)]
    (hp2 : p ≠ 2) (hc : c.Coprime p) (hcpos : 0 < c) (hk : 0 < k) :
    kummer_padicBound p ((s : ℤ) - 2 * k - 2)
      (((c : ℚ) ^ k - 1) * bernoulli k / k -
        (c : ℚ) ^ (k - 1) * kummer_W (p ^ s) c k) := by
  have hN : 0 < p ^ s := pow_pos (Fact.out : Nat.Prime p).pos _
  have hcN : c.Coprime (p ^ s) := hc.pow_right _
  rw [kummer_voronoi_identity (p ^ s) c k hN hcN hk]
  have hD0 : kummer_padicBound p (s : ℤ) (kummer_D (p ^ s) c k) := by
    apply kummer_bound_of_pow_dvd
    exact kummer_D_dvd (p ^ s) c k
  have hD : kummer_padicBound p ((s : ℤ) - 2 * k - 2)
      (kummer_D (p ^ s) c k) := kummer_bound_mono (by omega) hD0
  have hH0 := kummer_H_bound (p := p) (s := s) (c := c) hk
  have hH : kummer_padicBound p ((s : ℤ) - 2 * k - 2)
      ((kummer_H (p ^ s) c k : ℚ) / ((k : ℚ) * (p ^ s : ℕ))) :=
    kummer_bound_mono (by omega) hH0
  have hcpow : 1 ≤ c ^ k := Nat.one_le_pow k c hcpos
  have hcoef : kummer_padicBound p (-(k : ℤ)) (((c : ℚ) ^ k - 1) / k) := by
    simpa [Nat.cast_sub hcpow] using
      kummer_bound_nat_div (p := p) (c ^ k - 1) k hk
  have hE := kummer_E_bound (p := p) (s := s) (k := k) hp2
  have hprod : kummer_padicBound p ((s : ℤ) - 2 * k - 2)
      ((((c : ℚ) ^ k - 1) / k) * kummer_E (p ^ s) k) := by
    have hprod0 := kummer_bound_mul hcoef hE
    convert hprod0 using 1
    ring
  exact kummer_bound_sub (kummer_bound_add hD hH) hprod

private theorem kummer_multiple_term (p s c k i : ℕ) (hp : 0 < p) (hs : 0 < s) :
    (p * i) ^ (k - 1) * (c * (p * i) / p ^ s) =
      p ^ (k - 1) * (i ^ (k - 1) * (c * i / p ^ (s - 1))) := by
  have hspow : p ^ s = p * p ^ (s - 1) := by
    calc
      p ^ s = p ^ ((s - 1) + 1) := congrArg (p ^ ·) (by omega)
      _ = p ^ (s - 1) * p := pow_succ _ _
      _ = p * p ^ (s - 1) := mul_comm _ _
  have hdiv : c * (p * i) / p ^ s = c * i / p ^ (s - 1) := by
    rw [hspow, show c * (p * i) = p * (c * i) by ring]
    exact Nat.mul_div_mul_left _ _ hp
  rw [mul_pow, hdiv]
  ring

private theorem kummer_W_split (p s c k : ℕ) (hp : 0 < p) (hs : 0 < s) :
    kummer_W (p ^ s) c k =
      kummer_U p s c k + p ^ (k - 1) * kummer_W (p ^ (s - 1)) c k := by
  classical
  have hspow : p ^ s = p * p ^ (s - 1) := by
    calc
      p ^ s = p ^ ((s - 1) + 1) := congrArg (p ^ ·) (by omega)
      _ = p ^ (s - 1) * p := pow_succ _ _
      _ = p * p ^ (s - 1) := mul_comm _ _
  have hmul :
      (∑ j ∈ (Finset.range (p ^ s)).filter (fun j => p ∣ j),
        j ^ (k - 1) * (c * j / p ^ s)) =
        p ^ (k - 1) * kummer_W (p ^ (s - 1)) c k := by
    rw [kummer_W, Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun i _ => p * i) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_range, hspow]
        exact (Nat.mul_lt_mul_left hp).2 (Finset.mem_range.mp hi)
      · exact dvd_mul_right p i
    · intro a ha b hb hab
      exact Nat.mul_left_cancel hp hab
    · intro b hb
      obtain ⟨hbrange, hbdvd⟩ := Finset.mem_filter.mp hb
      obtain ⟨a, rfl⟩ := hbdvd
      have ha : a < p ^ (s - 1) := by
        apply (Nat.mul_lt_mul_left hp).mp
        simpa [hspow] using Finset.mem_range.mp hbrange
      exact ⟨a, Finset.mem_range.mpr ha, rfl⟩
    · intro i _
      exact (kummer_multiple_term p s c k i hp hs).symm
  have hpart := Finset.sum_filter_add_sum_filter_not (Finset.range (p ^ s))
    (fun j => ¬p ∣ j) (fun j => j ^ (k - 1) * (c * j / p ^ s))
  simp only [not_not] at hpart
  rw [kummer_W, kummer_U]
  calc
    (∑ j ∈ Finset.range (p ^ s), j ^ (k - 1) * (c * j / p ^ s)) =
        (∑ j ∈ (Finset.range (p ^ s)).filter (fun j => ¬p ∣ j),
          j ^ (k - 1) * (c * j / p ^ s)) +
        ∑ j ∈ (Finset.range (p ^ s)).filter (fun j => p ∣ j),
          j ^ (k - 1) * (c * j / p ^ s) := hpart.symm
    _ = _ := by rw [hmul]

private noncomputable def kummer_beta (p k : ℕ) : ℚ :=
  (1 - (p : ℚ) ^ (k - 1)) * bernoulli k / k

private theorem kummer_modified_bound {p s c k : ℕ} [Fact (Nat.Prime p)]
    (hp2 : p ≠ 2) (hc : c.Coprime p) (hcpos : 0 < c) (hs : 0 < s) (hk : 0 < k) :
    kummer_padicBound p ((s : ℤ) - 2 * k - 3)
      (((c : ℚ) ^ k - 1) * kummer_beta p k -
        (c : ℚ) ^ (k - 1) * kummer_U p s c k) := by
  have hnow := kummer_voronoi_bound (p := p) (s := s) hp2 hc hcpos hk
  have hnow' : kummer_padicBound p ((s : ℤ) - 2 * k - 3)
      (((c : ℚ) ^ k - 1) * bernoulli k / k -
        (c : ℚ) ^ (k - 1) * kummer_W (p ^ s) c k) :=
    kummer_bound_mono (by omega) hnow
  have hprev0 := kummer_voronoi_bound (p := p) (s := s - 1) hp2 hc hcpos hk
  have hprev : kummer_padicBound p ((s : ℤ) - 2 * k - 3)
      (((c : ℚ) ^ k - 1) * bernoulli k / k -
        (c : ℚ) ^ (k - 1) * kummer_W (p ^ (s - 1)) c k) := by
    apply kummer_bound_mono _ hprev0
    have hs' : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := by omega
    rw [hs']
    omega
  have hpint : kummer_padicBound p 0 ((p : ℚ) ^ (k - 1)) := by
    simpa using kummer_bound_int (p := p) (((p ^ (k - 1) : ℕ) : ℤ))
  have hmul : kummer_padicBound p ((s : ℤ) - 2 * k - 3)
      ((p : ℚ) ^ (k - 1) *
        (((c : ℚ) ^ k - 1) * bernoulli k / k -
          (c : ℚ) ^ (k - 1) * kummer_W (p ^ (s - 1)) c k)) := by
    simpa using kummer_bound_mul hpint hprev
  have hsplit : (kummer_W (p ^ s) c k : ℚ) =
      kummer_U p s c k + (p : ℚ) ^ (k - 1) * kummer_W (p ^ (s - 1)) c k := by
    exact_mod_cast kummer_W_split p s c k (Fact.out : Nat.Prime p).pos hs
  have heq : ((c : ℚ) ^ k - 1) * kummer_beta p k -
      (c : ℚ) ^ (k - 1) * kummer_U p s c k =
      (((c : ℚ) ^ k - 1) * bernoulli k / k -
        (c : ℚ) ^ (k - 1) * kummer_W (p ^ s) c k) -
      (p : ℚ) ^ (k - 1) *
        (((c : ℚ) ^ k - 1) * bernoulli k / k -
          (c : ℚ) ^ (k - 1) * kummer_W (p ^ (s - 1)) c k) := by
    rw [hsplit]
    unfold kummer_beta
    ring
  rw [heq]
  exact kummer_bound_sub hnow' hmul

private theorem kummer_exists_generator (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ c : ℕ, c.Coprime p ∧ 0 < c ∧
      ∀ k : ℕ, ¬(p - 1) ∣ k → ¬p ∣ c ^ k - 1 := by
  let _ : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime (Fact.out : Nat.Prime p)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  let c := (g : ZMod p).val
  have hc : c.Coprime p := ZMod.val_coe_unit_coprime g
  have hcpos : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hc0
    have hp1 : p = 1 := by simpa [c, hc0] using hc
    exact (Fact.out : Nat.Prime p).ne_one hp1
  have horder : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
    exact ZMod.card_units p
  refine ⟨c, hc, hcpos, fun k hk hdvd => ?_⟩
  have hcpow : 1 ≤ c ^ k := Nat.one_le_pow k c hcpos
  have hz : ((c ^ k - 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (c ^ k - 1) p).2 hdvd
  have hpowz : (c : ZMod p) ^ k = 1 := by
    apply sub_eq_zero.mp
    simpa [Nat.cast_sub hcpow] using hz
  have hcval : (c : ZMod p) = (g : ZMod p) := ZMod.natCast_zmod_val _
  have hgpow : g ^ k = 1 := by
    apply Units.ext
    change (g : ZMod p) ^ k = 1
    rw [← hcval]
    exact hpowz
  apply hk
  rw [← horder]
  exact orderOf_dvd_iff_pow_eq_one.mpr hgpow

private theorem kummer_pow_modEq {p t a u v : ℕ} [Fact (Nat.Prime p)]
    (ha : a.Coprime p) (huv : u ≡ v [MOD (p - 1) * p ^ t]) :
    a ^ u ≡ a ^ v [MOD p ^ (t + 1)] := by
  have hp := (Fact.out : Nat.Prime p)
  have hmod : 1 < p ^ (t + 1) := Nat.one_lt_pow (by omega) hp.one_lt
  have hcop : a.Coprime (p ^ (t + 1)) := ha.pow_right _
  have htot : (p ^ (t + 1)).totient = (p - 1) * p ^ t := by
    rw [Nat.totient_prime_pow hp (by omega)]
    ac_rfl
  have huv' : u % (p ^ (t + 1)).totient = v % (p ^ (t + 1)).totient := by
    rw [htot]
    exact huv
  rw [Nat.ModEq]
  calc
    a ^ u % p ^ (t + 1) = a ^ (u % (p ^ (t + 1)).totient) % p ^ (t + 1) :=
      Nat.pow_totient_mod hmod hcop
    _ = a ^ (v % (p ^ (t + 1)).totient) % p ^ (t + 1) := by rw [huv']
    _ = a ^ v % p ^ (t + 1) := (Nat.pow_totient_mod hmod hcop).symm

private theorem kummer_approximants_modEq {p m n t s c : ℕ} [Fact (Nat.Prime p)]
    (hc : c.Coprime p) (hm : 0 < m) (hn : 0 < n)
    (hcong : m ≡ n [MOD (p - 1) * p ^ t]) :
    c ^ (m - 1) * kummer_U p s c m ≡
      c ^ (n - 1) * kummer_U p s c n [MOD p ^ (t + 1)] := by
  have hone : 1 ≡ 1 [MOD (p - 1) * p ^ t] := Nat.ModEq.refl 1
  have hmnsub : m - 1 ≡ n - 1 [MOD (p - 1) * p ^ t] :=
    hcong.sub (by omega) (by omega) hone
  have hcPow := kummer_pow_modEq hc hmnsub
  have hU : kummer_U p s c m ≡ kummer_U p s c n [MOD p ^ (t + 1)] := by
    apply Nat.ModEq.sum
    intro j hj
    have hjnot : ¬p ∣ j := (Finset.mem_filter.mp hj).2
    have hjcop : j.Coprime p :=
      ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hjnot).symm
    have hjPow := kummer_pow_modEq hjcop hmnsub
    exact hjPow.mul_right (c * j / p ^ s)
  exact hcPow.mul hU

private theorem kummer_approximants_bound {p m n t s c : ℕ} [Fact (Nat.Prime p)]
    (hc : c.Coprime p) (hm : 0 < m) (hn : 0 < n)
    (hcong : m ≡ n [MOD (p - 1) * p ^ t]) :
    kummer_padicBound p ((t : ℤ) + 1)
      ((c : ℚ) ^ (m - 1) * kummer_U p s c m -
        (c : ℚ) ^ (n - 1) * kummer_U p s c n) := by
  have hmod := kummer_approximants_modEq (s := s) hc hm hn hcong
  have hdvd0 := hmod.dvd
  have hdvd : (p ^ (t + 1) : ℤ) ∣
      (c ^ (m - 1) * kummer_U p s c m : ℤ) -
        (c ^ (n - 1) * kummer_U p s c n : ℤ) := by
    rw [← neg_sub]
    exact dvd_neg.mpr hdvd0
  have hb := kummer_bound_of_pow_dvd (p := p) (s := t + 1) hdvd
  simpa [Int.cast_sub, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hb

private theorem kummer_beta_norm_le_one {p c k X : ℕ} {e : ℤ} [Fact (Nat.Prime p)]
    (hcpos : 0 < c) (hunit : ¬p ∣ c ^ k - 1) (he : 0 ≤ e)
    (happrox : kummer_padicBound p e
      (((c : ℚ) ^ k - 1) * kummer_beta p k - (X : ℚ))) :
    padicNorm p (kummer_beta p k) ≤ 1 := by
  have happrox0 := kummer_bound_mono he happrox
  have hX : kummer_padicBound p 0 (X : ℚ) := by
    simpa using kummer_bound_int (p := p) ((X : ℤ))
  have hprod0 : kummer_padicBound p 0 (((c : ℚ) ^ k - 1) * kummer_beta p k) := by
    have heq : ((c : ℚ) ^ k - 1) * kummer_beta p k =
        (((c : ℚ) ^ k - 1) * kummer_beta p k - X) + X := by ring
    rw [heq]
    exact kummer_bound_add happrox0 hX
  have hcpow : 1 ≤ c ^ k := Nat.one_le_pow k c hcpos
  have hunitNorm : padicNorm p ((c : ℚ) ^ k - 1) = 1 := by
    simpa [Nat.cast_sub hcpow] using (padicNorm.nat_eq_one_iff (p := p) (c ^ k - 1)).2 hunit
  rw [kummer_padicBound, neg_zero, zpow_zero, padicNorm.mul, hunitNorm, one_mul] at hprod0
  exact hprod0

private theorem kummer_power_difference_bound {p m n t c : ℕ} [Fact (Nat.Prime p)]
    (hc : c.Coprime p) (hcong : m ≡ n [MOD (p - 1) * p ^ t]) :
    kummer_padicBound p ((t : ℤ) + 1) ((c : ℚ) ^ n - (c : ℚ) ^ m) := by
  have hmod := kummer_pow_modEq hc hcong
  have hb := kummer_bound_of_pow_dvd (p := p) (s := t + 1) hmod.dvd
  simpa [Int.cast_sub, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hb

private theorem kummer_beta_difference_bound {p m n t : ℕ} [Fact (Nat.Prime p)]
    (hm_dvd : ¬(p - 1) ∣ m) (hn_dvd : ¬(p - 1) ∣ n)
    (hcong : m ≡ n [MOD (p - 1) * p ^ t]) :
    kummer_padicBound p ((t : ℤ) + 1) (kummer_beta p m - kummer_beta p n) := by
  have hp2 := kummer_prime_ne_two hm_dvd
  have hm := kummer_index_pos hm_dvd
  have hn := kummer_index_pos hn_dvd
  obtain ⟨c, hc, hcpos, hcunit⟩ := kummer_exists_generator p
  have hmunit := hcunit m hm_dvd
  have hnunit := hcunit n hn_dvd
  let s := t + 2 * m + 2 * n + 4
  have hs : 0 < s := by simp [s]
  have hAm0 := kummer_modified_bound (p := p) (s := s) (c := c) (k := m)
    hp2 hc hcpos hs hm
  have hAn0 := kummer_modified_bound (p := p) (s := s) (c := c) (k := n)
    hp2 hc hcpos hs hn
  have hAm : kummer_padicBound p ((t : ℤ) + 1)
      (((c : ℚ) ^ m - 1) * kummer_beta p m -
        (c : ℚ) ^ (m - 1) * kummer_U p s c m) := by
    apply kummer_bound_mono _ hAm0
    dsimp [s]
    omega
  have hAn : kummer_padicBound p ((t : ℤ) + 1)
      (((c : ℚ) ^ n - 1) * kummer_beta p n -
        (c : ℚ) ^ (n - 1) * kummer_U p s c n) := by
    apply kummer_bound_mono _ hAn0
    dsimp [s]
    omega
  have hbetaN : padicNorm p (kummer_beta p n) ≤ 1 := by
    apply kummer_beta_norm_le_one (c := c) (e := (t : ℤ) + 1)
      (X := c ^ (n - 1) * kummer_U p s c n) hcpos hnunit (by omega)
    simpa [Nat.cast_mul, Nat.cast_pow] using hAn
  have hbetaN0 : kummer_padicBound p 0 (kummer_beta p n) := by
    simpa [kummer_padicBound] using hbetaN
  have hX := kummer_approximants_bound (s := s) hc hm hn hcong
  have hcdiff := kummer_power_difference_bound hc hcong
  have hcorr : kummer_padicBound p ((t : ℤ) + 1)
      (((c : ℚ) ^ n - (c : ℚ) ^ m) * kummer_beta p n) := by
    simpa using kummer_bound_mul hcdiff hbetaN0
  have htotal : kummer_padicBound p ((t : ℤ) + 1)
      (((c : ℚ) ^ m - 1) * (kummer_beta p m - kummer_beta p n)) := by
    have hsum := kummer_bound_add (kummer_bound_add (kummer_bound_sub hAm hAn) hX) hcorr
    have heq : ((c : ℚ) ^ m - 1) * (kummer_beta p m - kummer_beta p n) =
        ((((c : ℚ) ^ m - 1) * kummer_beta p m -
            (c : ℚ) ^ (m - 1) * kummer_U p s c m) -
          (((c : ℚ) ^ n - 1) * kummer_beta p n -
            (c : ℚ) ^ (n - 1) * kummer_U p s c n) +
          ((c : ℚ) ^ (m - 1) * kummer_U p s c m -
            (c : ℚ) ^ (n - 1) * kummer_U p s c n)) +
          ((c : ℚ) ^ n - (c : ℚ) ^ m) * kummer_beta p n := by ring
    rw [heq]
    exact hsum
  have hcpow : 1 ≤ c ^ m := Nat.one_le_pow m c hcpos
  have hunitNorm : padicNorm p ((c : ℚ) ^ m - 1) = 1 := by
    simpa [Nat.cast_sub hcpow] using
      (padicNorm.nat_eq_one_iff (p := p) (c ^ m - 1)).2 hmunit
  rw [kummer_padicBound, padicNorm.mul, hunitNorm, one_mul] at htotal
  exact htotal

/-- **Kummer's congruence.** Let $p$ be a prime, let $B_j$ denote the $j$-th Bernoulli number,
with $B_1 = -1/2$, and let $t$ be a natural number. Let $m$ and $n$ be natural numbers, neither
divisible by $p - 1$, with $m \equiv n \pmod{(p-1)p^t}$. Then the rational numbers
$$\frac{(1 - p^{m-1}) B_m}{m} \quad \text{and} \quad \frac{(1 - p^{n-1}) B_n}{n}$$
are either equal, or their difference has $p$-adic valuation at least $t + 1$.

In other words, the two numbers agree modulo $p^{t+1}$; equality is listed as a separate case
because the $p$-adic valuation of $0$ is taken to be $0$.

Proof: We use Voronoi's finite-sum congruence in p-adic norm form, following
Ireland--Rosen, Ch. 15 §2, and Washington, Cor. 5.14, back to Kummer's 1851 paper.

Proves `Wanted` entry `kummer_congruence`.

Source: Ernst Eduard Kummer, "Über eine allgemeine Eigenschaft der rationalen Entwickelungscoefficienten einer bestimmten Gattung analytischer Functionen," Journal für die reine und angewandte Mathematik 41 (1851), 368–372, DOI 10.1515/crll.1851.41.368, https://doi.org/10.1515/crll.1851.41.368.
-/
public theorem kummer_congruence {p m n t : ℕ} [Fact (Nat.Prime p)]
    (hm_dvd : ¬ (p - 1) ∣ m) (hn_dvd : ¬ (p - 1) ∣ n)
    (hcong : m ≡ n [MOD (p - 1) * p ^ t]) :
    ((1 - (p : ℚ) ^ (m - 1)) * bernoulli m / (m : ℚ)) =
      ((1 - (p : ℚ) ^ (n - 1)) * bernoulli n / (n : ℚ)) ∨
    (t : ℤ) + 1 ≤ padicValRat p
      (((1 - (p : ℚ) ^ (m - 1)) * bernoulli m / (m : ℚ)) -
        ((1 - (p : ℚ) ^ (n - 1)) * bernoulli n / (n : ℚ))) := by
  change kummer_beta p m = kummer_beta p n ∨
    (t : ℤ) + 1 ≤ padicValRat p (kummer_beta p m - kummer_beta p n)
  have hbound := kummer_beta_difference_bound hm_dvd hn_dvd hcong
  by_cases hzero : kummer_beta p m = kummer_beta p n
  · exact Or.inl hzero
  · right
    have hne : kummer_beta p m - kummer_beta p n ≠ 0 := sub_ne_zero.mpr hzero
    rw [kummer_padicBound, padicNorm.eq_zpow_of_nonzero hne] at hbound
    have hpq : (1 : ℚ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    have hexp := (zpow_le_zpow_iff_right₀ hpq).mp hbound
    omega

end MetaMathlibExt
