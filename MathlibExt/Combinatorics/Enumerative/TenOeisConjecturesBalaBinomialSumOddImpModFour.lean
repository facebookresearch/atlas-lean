/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Odd values of Bala's binomial sum are `1` modulo `4`

For a natural number `n`, let `a(n) = ∑ k ∈ Finset.range (n + 1), C(2n+1,n+k+1)·(-2)^k`.
If `a(n)` is odd, then `a(n) ≡ 1 mod 4`
(`MetaMathlibExt.bala_binomial_sum_odd_imp_mod_four`).

## Proof outline

Modulo `4`, only the terms `k = 0, 1` of the sum survive, so `a(n) ≡ C₀ - 2·C₁` where
`C₀ = C(2n+1,n+1)` and `C₁ = C(2n+1,n+2)`. If `a(n)` is odd then `C₀` is odd, and one step
of Lucas' theorem for `p = 2` shows `C₀` is odd only when `n + 1` is a power of two.
For `n + 1 = 2^t` with `t ≥ 1`, Vandermonde's identity writes `C₀` as a sum whose first
term is `1`, whose middle term is `2` modulo `4`, and whose remaining terms are multiples
of `4`, giving `C₀ ≡ 3 mod 4`; since `n` is then odd, `C₁` is odd as well, so
`a(n) ≡ 3 - 2 = 1 mod 4`.

## References

Statements from Sela Fried, "Proofs of Ten Conjectures From the OEIS", *Journal of Integer
Sequences* 29 (2026), Article 26.1.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Fried/fried21.html>).
-/

namespace MetaMathlibExt

/-- Lucas one-step for `p = 2`. -/
private theorem lucas_two (N K : ℕ) :
    N.choose K ≡ (N % 2).choose (K % 2) * (N / 2).choose (K / 2) [MOD 2] :=
  @Choose.choose_modEq_choose_mod_mul_choose_div_nat N K 2 (Fact.mk Nat.prime_two)

/-- `Nat.ModEq` mod 2 preserves oddness. -/
private theorem modeq_two_odd_iff {a b : ℕ} (h : a ≡ b [MOD 2]) :
    Odd a ↔ Odd b := by
  have h' : a % 2 = b % 2 := h
  rw [Nat.odd_iff, Nat.odd_iff]
  omega

/-- Central binomial coefficients are even for positive `m`. -/
private theorem even_two_mul_choose_self {m : ℕ} (hm : 0 < m) :
    Even ((2 * m).choose m) := by
  have h := Nat.two_dvd_centralBinom_of_one_le hm
  rw [Nat.centralBinom_eq_two_mul_choose] at h
  exact even_iff_two_dvd.mpr h

/-- Classification: `C(2n+1,n+1)` odd implies `n + 1` is a power of two. -/
private theorem odd_choose_imp_pow_two (n : ℕ) (h : Odd ((2 * n + 1).choose (n + 1))) :
    ∃ t, n + 1 = 2 ^ t := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hL := lucas_two (2 * n + 1) (n + 1)
    have hmod : (2 * n + 1) % 2 = 1 := by omega
    have hdiv : (2 * n + 1) / 2 = n := by omega
    rw [hmod, hdiv] at hL
    have hC1 : ((1 : ℕ).choose ((n + 1) % 2)) = 1 := by
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with h0 | h0 <;> simp [h0]
    rw [hC1, one_mul] at hL
    have hOdd : Odd (n.choose ((n + 1) / 2)) := (modeq_two_odd_iff hL).mp h
    rcases eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by norm_num⟩
    · rcases Nat.even_or_odd n with hnEven | hnOdd
      · obtain ⟨m, rfl⟩ := hnEven
        have hm : 0 < m := by omega
        have hdiv2 : (m + m + 1) / 2 = m := by omega
        rw [hdiv2] at hOdd
        have h2m : m + m = 2 * m := by omega
        rw [h2m] at hOdd
        have hEven := even_two_mul_choose_self hm
        exact absurd hOdd (Nat.not_odd_iff_even.mpr hEven)
      · obtain ⟨m, rfl⟩ := hnOdd
        have hdiv2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
        rw [hdiv2] at hOdd
        have hlt : m < 2 * m + 1 := by omega
        obtain ⟨t, ht⟩ := ih m hlt hOdd
        exact ⟨t + 1, by rw [pow_succ', ← ht]; omega⟩

/-- `C(2U,j)` is odd when `j` is even and `C(U,j/2)` is odd. -/
private theorem odd_choose_two_mul_of_even {U j : ℕ} (hj : Even j)
    (h : Odd (U.choose (j / 2))) : Odd ((2 * U).choose j) := by
  have hL := lucas_two (2 * U) j
  have hmod : (2 * U) % 2 = 0 := by omega
  have hdiv : (2 * U) / 2 = U := by omega
  have hjmod : j % 2 = 0 := Nat.even_iff.mp hj
  rw [hmod, hdiv, hjmod] at hL
  have hC00 : ((0 : ℕ).choose 0) = 1 := rfl
  rw [hC00, one_mul] at hL
  exact (modeq_two_odd_iff hL).mpr h

/-- `C(2U,j)` is even when `j` is odd. -/
private theorem even_choose_two_mul_of_odd {U j : ℕ} (hj : Odd j) :
    Even ((2 * U).choose j) := by
  have hL := lucas_two (2 * U) j
  have hmod : (2 * U) % 2 = 0 := by omega
  have hdiv : (2 * U) / 2 = U := by omega
  have hjmod : j % 2 = 1 := Nat.odd_iff.mp hj
  rw [hmod, hdiv, hjmod] at hL
  have hC01 : ((0 : ℕ).choose 1) = 0 := rfl
  rw [hC01, zero_mul] at hL
  have h' : (2 * U).choose j % 2 = 0 := by
    have h2 : (2 * U).choose j % 2 = (0 : ℕ) % 2 := hL
    omega
  exact Nat.even_iff.mpr h'

/-- Every entry of row `2^t - 1` of Pascal's triangle is odd. -/
private theorem odd_choose_two_pow_sub_one (t : ℕ) (j : ℕ) (hj : j < 2 ^ t) :
    Odd ((2 ^ t - 1).choose j) := by
  induction t generalizing j with
  | zero =>
    have hj0 : j = 0 := by
      have h1 : (2 : ℕ) ^ 0 = 1 := pow_zero 2
      omega
    subst hj0
    decide
  | succ t ih =>
    have hU : 2 ^ (t + 1) - 1 = 2 * (2 ^ t - 1) + 1 := by
      have hpos : 0 < 2 ^ t := by positivity
      have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := pow_succ' 2 t
      omega
    rw [hU]
    rcases j with _ | k
    · rw [Nat.choose_zero_right]
      exact odd_one
    · rw [Nat.choose_succ_succ']
      have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := pow_succ' 2 t
      rcases Nat.even_or_odd k with hkeven | hkodd
      · have h1 : Odd ((2 * (2 ^ t - 1)).choose k) :=
          odd_choose_two_mul_of_even hkeven (ih (k / 2) (by omega))
        have h2 : Even ((2 * (2 ^ t - 1)).choose (k + 1)) :=
          even_choose_two_mul_of_odd (hkeven.add_one)
        exact h1.add_even h2
      · have h1 : Even ((2 * (2 ^ t - 1)).choose k) :=
          even_choose_two_mul_of_odd hkodd
        have h2 : Odd ((2 * (2 ^ t - 1)).choose (k + 1)) :=
          odd_choose_two_mul_of_even (hkodd.add_one) (ih ((k + 1) / 2) (by omega))
        exact h1.add_odd h2

/-- `C(N,K) * K = N * C(N-1,K-1)`. -/
private theorem choose_mul_eq (N K : ℕ) (hN : 1 ≤ N) (hK : 1 ≤ K) :
    N.choose K * K = N * (N - 1).choose (K - 1) := by
  obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  obtain ⟨K', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : K ≠ 0)
  have e1 : N' + 1 - 1 = N' := by omega
  have e2 : K' + 1 - 1 = K' := by omega
  rw [e1, e2]
  have h1 := Nat.choose_succ_right_eq (N' + 1) K'
  have h2 := Nat.choose_mul_succ_eq N' K'
  rw [h1, ← h2]
  exact mul_comm _ _

/-- For `0 < k < 2^t` with `k ≠ 2^(t-1)`, `4 ∣ C(2^t,k)`. -/
private theorem four_dvd_choose_two_pow {t k : ℕ} (ht : 1 ≤ t)
    (hk0 : 0 < k) (hkM : k < 2 ^ t) (hkne : k ≠ 2 ^ (t - 1)) :
    4 ∣ (2 ^ t).choose k := by
  have hO : Odd ((2 ^ t - 1).choose (k - 1)) :=
    odd_choose_two_pow_sub_one t (k - 1) (by omega)
  have h2t1 : 1 ≤ (2:ℕ) ^ t := by
    have h1 : 0 < (2:ℕ) ^ t := by positivity
    omega
  have hId := choose_mul_eq (2 ^ t) k h2t1 (by omega)
  obtain ⟨v, u, hu, hk_eq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : k ≠ 0)
  have hu0 : u ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hk_eq
    omega
  have h2vdvd : (2:ℕ) ^ v ∣ k := ⟨u, hk_eq⟩
  have h2vle : (2:ℕ) ^ v ≤ k := Nat.le_of_dvd hk0 h2vdvd
  have hplt : (2:ℕ) ^ v < 2 ^ t := lt_of_le_of_lt h2vle hkM
  have hv_lt : v < t := (Nat.pow_lt_pow_iff_right (by norm_num : (1:ℕ) < 2)).mp hplt
  have hv_ne : v ≠ t - 1 := by
    intro hv_eq
    rw [hv_eq] at hk_eq
    have ht2 : (2:ℕ) ^ t = 2 ^ (t - 1) * 2 := by
      have h := pow_succ (2:ℕ) (t - 1)
      rw [Nat.sub_add_cancel ht] at h
      exact h
    have h2pos : 0 < (2:ℕ) ^ (t - 1) := by positivity
    have hu2 : u < 2 := by
      have hlt : 2 ^ (t - 1) * u < 2 ^ (t - 1) * 2 := by
        rw [← hk_eq, ← ht2]
        exact hkM
      rw [mul_comm (2 ^ (t - 1)) u, mul_comm (2 ^ (t - 1)) 2] at hlt
      exact (mul_lt_mul_iff_left₀ h2pos).mp hlt
    have hu1 : u = 1 := by
      rcases hu with ⟨r, rfl⟩
      omega
    rw [hu1, mul_one] at hk_eq
    exact hkne hk_eq
  have hv_le : v + 2 ≤ t := by omega
  have hvt : v ≤ t := by omega
  have hpow : (2:ℕ) ^ t = 2 ^ v * 2 ^ (t - v) := by
    rw [← pow_add, Nat.add_sub_cancel' hvt]
  have hId2 : (2 ^ t).choose k * u = 2 ^ (t - v) * (2 ^ t - 1).choose (k - 1) := by
    have h' : (2 ^ t).choose k * u * 2 ^ v
        = 2 ^ (t - v) * (2 ^ t - 1).choose (k - 1) * 2 ^ v := by
      calc (2 ^ t).choose k * u * 2 ^ v
          = (2 ^ t).choose k * (2 ^ v * u) := by ring
        _ = (2 ^ t).choose k * k := by rw [← hk_eq]
        _ = 2 ^ t * (2 ^ t - 1).choose (k - 1) := hId
        _ = (2 ^ v * 2 ^ (t - v)) * (2 ^ t - 1).choose (k - 1) := by rw [hpow]
        _ = 2 ^ (t - v) * (2 ^ t - 1).choose (k - 1) * 2 ^ v := by ring
    have h2v0 : (2:ℕ) ^ v ≠ 0 := by positivity
    exact mul_right_cancel₀ h2v0 h'
  have hu_dvd : u ∣ 2 ^ (t - v) * (2 ^ t - 1).choose (k - 1) :=
    ⟨(2 ^ t).choose k, hId2.symm.trans (mul_comm ((2 ^ t).choose k) u)⟩
  have hcop : Nat.Coprime u (2 ^ (t - v)) := by
    have hpos : 0 < t - v := by omega
    have h2 : Nat.Coprime u 2 := Nat.coprime_two_right.mpr hu
    exact (Nat.coprime_pow_right_iff hpos u 2).mpr h2
  have huO : u ∣ (2 ^ t - 1).choose (k - 1) := hcop.dvd_of_dvd_mul_left hu_dvd
  obtain ⟨O', hO'⟩ := huO
  have hC : (2 ^ t).choose k = 2 ^ (t - v) * O' := by
    have key : (2 ^ t).choose k * u = (2 ^ (t - v) * O') * u := by
      rw [hId2, hO']
      ring
    exact mul_right_cancel₀ hu0 key
  have h4 : (4:ℕ) ∣ 2 ^ (t - v) := by
    obtain ⟨w, hw⟩ : ∃ w, t - v = 2 + w := ⟨t - v - 2, by omega⟩
    rw [hw]
    exact ⟨2 ^ w, by rw [pow_add]; norm_num⟩
  rw [hC]
  exact dvd_mul_of_dvd_left h4 O'

/-- `C(2^t, 2^(t-1)) = 2 * C(2^t - 1, 2^(t-1) - 1)`. -/
private theorem choose_two_pow_half {t : ℕ} (ht : 1 ≤ t) :
    (2 ^ t).choose (2 ^ (t - 1)) = 2 * ((2 ^ t - 1).choose (2 ^ (t - 1) - 1)) := by
  have h2t1 : 1 ≤ (2:ℕ) ^ t := by
    have h1 : 0 < (2:ℕ) ^ t := by positivity
    omega
  have hs1 : 1 ≤ (2:ℕ) ^ (t - 1) := by
    have h1 : 0 < (2:ℕ) ^ (t - 1) := by positivity
    omega
  have hId := choose_mul_eq (2 ^ t) (2 ^ (t - 1)) h2t1 hs1
  have ht2 : (2:ℕ) ^ t = 2 * 2 ^ (t - 1) := by
    have h := pow_succ' (2:ℕ) (t - 1)
    rw [Nat.sub_add_cancel ht] at h
    exact h
  have h2 : (2:ℕ) ^ (t - 1) ≠ 0 := by positivity
  have key : (2 ^ t).choose (2 ^ (t - 1)) * 2 ^ (t - 1)
      = (2 * ((2 ^ t - 1).choose (2 ^ (t - 1) - 1))) * 2 ^ (t - 1) := by
    calc (2 ^ t).choose (2 ^ (t - 1)) * 2 ^ (t - 1)
        = 2 ^ t * (2 ^ t - 1).choose (2 ^ (t - 1) - 1) := hId
      _ = (2 * 2 ^ (t - 1)) * (2 ^ t - 1).choose (2 ^ (t - 1) - 1) := by rw [ht2]
      _ = (2 * ((2 ^ t - 1).choose (2 ^ (t - 1) - 1))) * 2 ^ (t - 1) := by ring
  exact mul_right_cancel₀ h2 key

/-- Split a range sum at three distinct indices to compute it mod 4. -/
private theorem sum_split_three {M s : ℕ} (g : ℕ → ℕ) (hs0 : 0 < s) (hsM : s < M)
    (h0 : g 0 = 1) (hM : g M = 0) (hs : g s % 4 = 2)
    (hrest : ∀ k ∈ (((Finset.range (M + 1)).erase 0).erase s).erase M, 4 ∣ g k) :
    (∑ k ∈ Finset.range (M + 1), g k) % 4 = 3 := by
  have h0mem : 0 ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
  have peel0 := Finset.add_sum_erase (Finset.range (M + 1)) g h0mem
  have hsmem : s ∈ (Finset.range (M + 1)).erase 0 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have peel1 := Finset.add_sum_erase ((Finset.range (M + 1)).erase 0) g hsmem
  have hMmem : M ∈ (((Finset.range (M + 1)).erase 0).erase s) :=
    Finset.mem_erase.mpr
      ⟨by omega, Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩
  have peel2 := Finset.add_sum_erase (((Finset.range (M + 1)).erase 0).erase s) g hMmem
  have h4rest : 4 ∣ ∑ k ∈ (((Finset.range (M + 1)).erase 0).erase s).erase M, g k :=
    Finset.dvd_sum hrest
  have hS : ∑ k ∈ Finset.range (M + 1), g k
      = g 0 + (g s + (g M + ∑ k ∈ (((Finset.range (M + 1)).erase 0).erase s).erase M, g k)) := by
    rw [← peel0, ← peel1, ← peel2]
  rw [hS, h0, hM]
  have hS3 : (∑ k ∈ (((Finset.range (M + 1)).erase 0).erase s).erase M, g k) % 4 = 0 := by
    rcases h4rest with ⟨q, hq⟩
    omega
  omega

/-- For `t ≥ 1`, `C(2^(t+1)-1, 2^t) ≡ 3 mod 4`. -/
private theorem mod_four_choose_two_pow {t : ℕ} (ht : 1 ≤ t) :
    ((2 ^ (t + 1) - 1).choose (2 ^ t)) % 4 = 3 := by
  have hM2 : (2:ℕ) ^ t = 2 * 2 ^ (t - 1) := by
    have h := pow_succ' (2:ℕ) (t - 1)
    rw [Nat.sub_add_cancel ht] at h
    exact h
  have hMge : 2 ≤ (2:ℕ) ^ t := by
    have h1 : 0 < (2:ℕ) ^ (t - 1) := by positivity
    omega
  have hs0 : 0 < (2:ℕ) ^ (t - 1) := by positivity
  have hsM : (2:ℕ) ^ (t - 1) < 2 ^ t := by omega
  have hMs : 2 ^ t - 2 ^ (t - 1) = 2 ^ (t - 1) := by omega
  have hV : 2 ^ (t + 1) - 1 = (2 ^ t - 1) + 2 ^ t := by
    have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := pow_succ' 2 t
    omega
  rw [hV, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  dsimp only
  rw [Nat.succ_eq_add_one]
  have h0 : (fun k => (2 ^ t - 1).choose k * (2 ^ t).choose (2 ^ t - k)) 0 = 1 := by
    change (2 ^ t - 1).choose 0 * (2 ^ t).choose (2 ^ t - 0) = 1
    rw [Nat.choose_zero_right, Nat.sub_zero, Nat.choose_self, mul_one]
  have hM : (fun k => (2 ^ t - 1).choose k * (2 ^ t).choose (2 ^ t - k)) (2 ^ t) = 0 := by
    change (2 ^ t - 1).choose (2 ^ t) * (2 ^ t).choose (2 ^ t - 2 ^ t) = 0
    have hlt : 2 ^ t - 1 < 2 ^ t := by omega
    rw [Nat.choose_eq_zero_of_lt hlt, zero_mul]
  have hs : (fun k => (2 ^ t - 1).choose k * (2 ^ t).choose (2 ^ t - k)) (2 ^ (t - 1)) % 4 = 2 := by
    change ((2 ^ t - 1).choose (2 ^ (t - 1)) * (2 ^ t).choose (2 ^ t - 2 ^ (t - 1))) % 4 = 2
    rw [hMs, choose_two_pow_half ht]
    have hE1 : Odd ((2 ^ t - 1).choose (2 ^ (t - 1))) :=
      odd_choose_two_pow_sub_one t _ hsM
    have hO' : Odd ((2 ^ t - 1).choose (2 ^ (t - 1) - 1)) :=
      odd_choose_two_pow_sub_one t _ (by omega)
    have hPodd : Odd ((2 ^ t - 1).choose (2 ^ (t - 1)) * (2 ^ t - 1).choose (2 ^ (t - 1) - 1)) :=
      hE1.mul hO'
    have heq : (2 ^ t - 1).choose (2 ^ (t - 1)) * (2 * ((2 ^ t - 1).choose (2 ^ (t - 1) - 1)))
        = 2 * ((2 ^ t - 1).choose (2 ^ (t - 1)) * (2 ^ t - 1).choose (2 ^ (t - 1) - 1)) := by
      ring
    rw [heq]
    rcases hPodd with ⟨r, hr⟩
    rw [hr]
    omega
  have hrest : ∀ k ∈ (((Finset.range (2 ^ t + 1)).erase 0).erase (2 ^ (t - 1))).erase (2 ^ t),
      4 ∣ (fun k => (2 ^ t - 1).choose k * (2 ^ t).choose (2 ^ t - k)) k := by
    intro k hk
    simp only [Finset.mem_erase, Finset.mem_range] at hk
    rcases hk with ⟨hkM', hks, hk0', hklt⟩
    have hj0 : 0 < 2 ^ t - k := by omega
    have hjM : 2 ^ t - k < 2 ^ t := by omega
    have hjne : 2 ^ t - k ≠ 2 ^ (t - 1) := by
      intro hcon
      have hk_eq : k = 2 ^ (t - 1) := by omega
      exact hks hk_eq
    have h4 : 4 ∣ (2 ^ t).choose (2 ^ t - k) := four_dvd_choose_two_pow ht hj0 hjM hjne
    change 4 ∣ (2 ^ t - 1).choose k * (2 ^ t).choose (2 ^ t - k)
    exact dvd_mul_of_dvd_right h4 _
  have hfin := sum_split_three
    (fun k => (2 ^ t - 1).choose k * (2 ^ t).choose (2 ^ t - k)) hs0 hsM h0 hM hs hrest
  exact hfin

/-- For `n ≥ 1`, the Bala sum is `C₀ + C₁·(-2) + R` with `4 ∣ R`. -/
private theorem bala_sum_split {n : ℕ} (hn : 1 ≤ n) :
    ∃ R : ℤ, (∑ k ∈ Finset.range (n + 1), ((2*n+1).choose (n+k+1) : ℤ)*(-2)^k)
      = ((2*n+1).choose (n+1) : ℤ) + ((2*n+1).choose (n+2) : ℤ)*(-2) + R
      ∧ (4:ℤ) ∣ R := by
  have h0mem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have h1mem : 1 ∈ (Finset.range (n + 1)).erase 0 :=
    Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_range.mpr (by omega)⟩
  have peel0 := Finset.add_sum_erase (Finset.range (n + 1))
    (fun k => ((2*n+1).choose (n+k+1) : ℤ)*(-2)^k) h0mem
  have peel1 := Finset.add_sum_erase ((Finset.range (n + 1)).erase 0)
    (fun k => ((2*n+1).choose (n+k+1) : ℤ)*(-2)^k) h1mem
  refine ⟨∑ k ∈ ((Finset.range (n + 1)).erase 0).erase 1,
    ((2*n+1).choose (n+k+1) : ℤ)*(-2)^k, ?_, ?_⟩
  · rw [← peel0, ← peel1]
    have h01 : n + 0 + 1 = n + 1 := by omega
    have h11 : n + 1 + 1 = n + 2 := by omega
    rw [h01, h11, pow_zero, pow_one, mul_one]
    ring
  · apply Finset.dvd_sum
    intro k hk
    simp only [Finset.mem_erase, Finset.mem_range] at hk
    rcases hk with ⟨hk1, hk0, hklt⟩
    have hk2 : 2 ≤ k := by omega
    have hpow : (-2:ℤ)^k = 4 * (-2)^(k-2) := by
      have hke : k = 2 + (k-2) := by omega
      rw [hke, pow_add]
      norm_num
    rw [hpow]
    exact dvd_mul_of_dvd_right (dvd_mul_right 4 _) _

/-- The Bala binomial sum identity `(n+2)·C₁ = n·C₀`. -/
private theorem bala_choose_identity (n : ℕ) :
    (n + 2) * (2*n+1).choose (n+2) = n * (2*n+1).choose (n+1) := by
  have h := Nat.choose_succ_right_eq (2*n+1) (n+1)
  have e1 : n + 1 + 1 = n + 2 := by omega
  have e2 : 2*n+1-(n+1) = n := by omega
  rw [e1, e2] at h
  calc (n + 2) * (2*n+1).choose (n+2)
      = (2*n+1).choose (n+2) * (n+2) := mul_comm _ _
    _ = (2*n+1).choose (n+1) * n := h
    _ = n * (2*n+1).choose (n+1) := mul_comm _ _

@[expose] public section

/-- **Odd values of Bala's binomial sum are $1$ modulo $4$.** For a natural number $n$, let
$a(n) = \sum_{k=0}^{n} \binom{2n+1}{n+k+1} (-2)^k$. If $a(n)$ is odd, then $a(n) \equiv 1 \pmod 4$.

The paper's $a(n)$ is A026641 (the number of even-outdegree nodes in all ordered trees with $n$
edges); its proof works with this binomial sum (Bala's formula, display (13)), which is taken as
the definition here.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 7 (`jis-2026-26.1.8-thm-7`). -/
public theorem bala_binomial_sum_odd_imp_mod_four (n : ℕ)
    (h : Odd (∑ k ∈ Finset.range (n + 1), ((2 * n + 1).choose (n + k + 1) : ℤ) * (-2) ^ k)) :
    (∑ k ∈ Finset.range (n + 1), ((2 * n + 1).choose (n + k + 1) : ℤ) * (-2) ^ k) % 4 = 1 := by
  rcases eq_zero_or_pos n with rfl | hn
  · decide
  · obtain ⟨R, hS, hR⟩ := bala_sum_split hn
    have hSodd : (∑ k ∈ Finset.range (n + 1), ((2*n+1).choose (n+k+1) : ℤ)*(-2)^k) % 2 = 1 :=
      Int.odd_iff.mp h
    have hEeven : ((((2*n+1).choose (n+2) : ℤ)*(-2))+R) % 2 = 0 := by
      rcases hR with ⟨q, hq⟩
      omega
    have hC0mod2 : (((2*n+1).choose (n+1) : ℤ)) % 2 = 1 := by omega
    have hC0odd : Odd ((2*n+1).choose (n+1)) :=
      (Int.odd_natCast _).mp (Int.odd_iff.mpr hC0mod2)
    obtain ⟨t, ht⟩ := odd_choose_imp_pow_two n hC0odd
    have ht1 : 1 ≤ t := by
      rcases t with _ | t'
      · simp at ht
        omega
      · omega
    have hpow2 : 2 ^ (t + 1) = 2 * 2 ^ t := pow_succ' 2 t
    have hC0mod : ((2*n+1).choose (n+1)) % 4 = 3 := by
      have h2n1 : 2*n+1 = 2^(t+1)-1 := by omega
      rw [h2n1, ht]
      exact mod_four_choose_two_pow ht1
    have hC0z : (((2*n+1).choose (n+1) : ℤ)) % 4 = 3 := by omega
    have h2teven : Even ((2:ℕ)^t) := by
      have hM2 : (2:ℕ)^t = 2 * 2^(t-1) := by
        have h := pow_succ' (2:ℕ) (t - 1)
        rw [Nat.sub_add_cancel ht1] at h
        exact h
      exact ⟨2^(t-1), by rw [hM2, two_mul]⟩
    have hnodd : Odd n := by
      have hnp1even : Even (n+1) := by rw [ht]; exact h2teven
      have h1 : (n+1) % 2 = 0 := Nat.even_iff.mp hnp1even
      have h2 : n % 2 = 1 := by omega
      exact Nat.odd_iff.mpr h2
    have hId := bala_choose_identity n
    have hC1odd : Odd ((2*n+1).choose (n+2)) := by
      by_contra hcon
      rw [Nat.not_odd_iff_even] at hcon
      have hLeven : Even ((n+2) * (2*n+1).choose (n+2)) := by
        have hdvd : 2 ∣ (2*n+1).choose (n+2) := even_iff_two_dvd.mp hcon
        exact even_iff_two_dvd.mpr (dvd_mul_of_dvd_right hdvd _)
      have hRodd : Odd (n * (2*n+1).choose (n+1)) := hnodd.mul hC0odd
      rw [hId] at hLeven
      exact (Nat.not_odd_iff_even.mpr hLeven) hRodd
    have hC1z : Odd (((2*n+1).choose (n+2) : ℤ)) := (Int.odd_natCast _).mpr hC1odd
    have hC1zmod : (((2*n+1).choose (n+2) : ℤ)) % 2 = 1 := Int.odd_iff.mp hC1z
    have hRz : R % 4 = 0 := by
      rcases hR with ⟨q, hq⟩
      omega
    omega

end

end MetaMathlibExt
