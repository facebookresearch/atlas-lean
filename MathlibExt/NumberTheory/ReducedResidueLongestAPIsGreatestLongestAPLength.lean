/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Radical.Basic
public import MathlibExt.NumberTheory.ReducedResidueLongestAP
import MathlibExt.NumberTheory.ReducedResiduePrimeBound
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.LinearCombination

/-!
# Maximum longest progression length over all reduced residue windows

For `n > 1`, the largest value of the longest progression length `f_m(n)` over all integers `m`
is `max (n / rad n) (gpf n - 1)`, where `rad n` is the product of the distinct prime factors of
`n` and `gpf n` is its largest prime factor.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6.
-/

namespace MetaMathlibExt

@[expose] public section

open UniqueFactorizationMonoid

namespace isGreatest_longestAPLength

private theorem upper_bound (m : ℤ) {n : ℕ} (hn : 1 < n) :
    longestAPLength m n ≤ max (n / radical n) (n.primeFactors.sup id - 1) := by
  apply csSup_le'
  rintro s ⟨b, d, hd, hmem⟩
  by_cases hsub : n.primeFactors ⊆ d.primeFactors
  · have hrd := Nat.le_of_dvd hd ((Nat.radical_dvd_iff hd.ne').mpr hsub)
    have hspan : n ≤ (n / radical n) * d := calc
      n = n / radical n * radical n := (Nat.div_mul_cancel radical_dvd_self).symm
      _ ≤ n / radical n * d := Nat.mul_le_mul_left _ hrd
    by_contra! hs
    have hq : n / radical n < s := lt_of_le_of_lt (Nat.le_max_left _ _) hs
    have hfirst := (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem 0 (by omega))).1).1
    have hlast :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp (hmem (n / radical n) hq)).1).2
    have hspan' : (n : ℤ) ≤ ((n / radical n : ℕ) : ℤ) * (d : ℤ) := by
      exact_mod_cast hspan
    simp only [Nat.cast_zero, zero_mul, add_zero] at hfirst
    omega
  · obtain ⟨p, hpn, hpd⟩ := Finset.not_subset.mp hsub
    have hp := Nat.prime_of_mem_primeFactors hpn
    have hs : s ≤ longestAPLengthWithDiff m n d :=
      le_csSup ⟨n, fun _ ⟨_, ht⟩ => apLength_le hd ht⟩ ⟨b, hmem⟩
    have hprime := longestAPLengthWithDiff_le_prime_sub_one m hn hd hp
      (Nat.dvd_of_mem_primeFactors hpn) (fun hdiv => hpd (hp.mem_primeFactors hdiv hd.ne'))
    have hmax : p ≤ n.primeFactors.sup id := Finset.le_sup (f := id) hpn
    have h1 : s ≤ p - 1 := hs.trans hprime
    have h2 : p - 1 ≤ n.primeFactors.sup id - 1 := by omega
    exact (h1.trans h2).trans (Nat.le_max_right _ _)

private theorem lower_bound (m : ℤ) {n : ℕ} (hn : n ≠ 0) :
    n / radical n ≤ longestAPLength m n := by
  let r := radical n
  have hr : 0 < r := Nat.radical_pos n
  obtain ⟨k, hk, _⟩ := existsUnique_add_zsmul_mem_Ioc (show (0 : ℤ) < r by exact_mod_cast hr) 1 m
  change m < 1 + k * (r : ℤ) ∧ 1 + k * (r : ℤ) ≤ m + r at hk
  unfold longestAPLength
  refine le_csSup ⟨n, fun _ ⟨_, _, hd, ht⟩ => apLength_le hd ht⟩
    ⟨1 + k * (r : ℤ), r, hr, fun i hi => ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · have hspan : (i + 1) * r ≤ n := calc
      (i + 1) * r ≤ (n / r) * r := Nat.mul_le_mul_right r hi
      _ = n := Nat.div_mul_cancel radical_dvd_self
    have hspan' : ((i : ℤ) + 1) * r ≤ n := by exact_mod_cast hspan
    have hi₀ : 0 ≤ (i : ℤ) * r := by positivity
    apply Finset.mem_Icc.mpr
    constructor <;> linarith [hk.1, hk.2]
  · have hcop : IsCoprime (1 + k * (r : ℤ) + i * r) (r : ℤ) := by
      simp [isCoprime_one_left]
    apply Int.isCoprime_iff_gcd_eq_one.mp
    apply (hcop.pow_right (n := n)).of_isCoprime_of_dvd_right
    exact_mod_cast Nat.dvd_radical_pow_self hn

private theorem exists_le_gpf_sub_one {n : ℕ} (hn : 1 < n) :
    ∃ m : ℤ, n.primeFactors.sup id - 1 ≤ longestAPLength m n := by
  obtain ⟨P, hPmem, hPsup⟩ :=
    Finset.exists_mem_eq_sup _ (Nat.nonempty_primeFactors.mpr hn) id
  have hPsup' : n.primeFactors.sup id = P := hPsup
  rw [hPsup']
  have hP : P.Prime := Nat.prime_of_mem_primeFactors hPmem
  have hP2 : 2 ≤ P := hP.two_le
  have hPr : P ∣ radical n := by
    rw [Nat.radical_eq_prod_primeFactors]
    exact Finset.dvd_prod_of_mem _ hPmem
  have hr : 0 < radical n := Nat.radical_pos n
  have hrn : radical n ∣ n := radical_dvd_self
  set M := radical n / P with hMdef
  have hPM : P * M = radical n := by
    rw [hMdef, mul_comm]
    exact Nat.div_mul_cancel hPr
  have hMpos : 0 < M := by
    rw [hMdef]
    exact Nat.div_pos (Nat.le_of_dvd hr hPr) hP.pos
  have hPnotM : ¬ P ∣ M := by
    intro hdiv
    obtain ⟨t, ht⟩ := hdiv
    have hPP : P * P ∣ radical n := ⟨t, by rw [← hPM, ht]; ring⟩
    have hunit : IsUnit P := UniqueFactorizationMonoid.squarefree_radical (a := n) P hPP
    rw [Nat.isUnit_iff] at hunit
    exact hP.ne_one hunit
  let : Fact P.Prime := ⟨hP⟩
  have hMne : (M : ZMod P) ≠ 0 := fun h => hPnotM ((ZMod.natCast_eq_zero_iff ..).mp h)
  let x : ZMod P := -(1 : ZMod P) / (M : ZMod P)
  have hdiv0 : (P : ℤ) ∣ 1 + (x.val : ℤ) * (M : ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    push_cast
    rw [ZMod.natCast_zmod_val, show x = -(1 : ZMod P) / (M : ZMod P) from rfl,
      div_mul_cancel₀ _ hMne, add_neg_cancel]
  set b : ℤ := 1 + ((x.val + 1 : ℕ) : ℤ) * (M : ℤ) with hbdef
  unfold longestAPLength
  refine ⟨b - 1,
    le_csSup ⟨n, fun _ ⟨_, _, hd, ht⟩ => apLength_le hd ht⟩ ⟨b, M, hMpos, fun i hi => ?_⟩⟩
  have hi2 : i ≤ P - 2 := by omega
  have hspan : i * M < n := by
    have h1 : i * M ≤ (P - 2) * M := Nat.mul_le_mul_right M hi2
    have h2 : (P - 2) * M < P * M := (Nat.mul_lt_mul_right hMpos).mpr (by omega)
    have h4 : radical n ≤ n := Nat.le_of_dvd (by omega) hrn
    omega
  have hlt : ((i * M : ℕ) : ℤ) < (n : ℤ) := by exact_mod_cast hspan
  rw [Nat.cast_mul] at hlt
  have hnn : (0 : ℤ) ≤ (i : ℤ) * (M : ℤ) := by positivity
  have hb1 : (1 : ℤ) ≤ b := by
    have hpos : (0 : ℤ) ≤ ((x.val + 1 : ℕ) : ℤ) * ((M : ℕ) : ℤ) := by positivity
    rw [hbdef]
    linarith
  have htb : b + (i : ℤ) * (M : ℤ) = 1 + ((x.val + 1 + i : ℕ) : ℤ) * ((M : ℕ) : ℤ) := by
    rw [hbdef]
    push_cast
    ring
  have hF2 : ¬ (P : ℤ) ∣ b + (i : ℤ) * (M : ℤ) := by
    intro hPt
    rw [htb] at hPt
    have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hPt
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv0
    push_cast at h1 h0
    have hJM : ((x.val + 1 + i : ℕ) : ZMod P) * ((M : ℕ) : ZMod P) =
        ((x.val : ℕ) : ZMod P) * ((M : ℕ) : ZMod P) := by
      push_cast
      linear_combination h1 - h0
    have hji : ((x.val + 1 + i : ℕ) : ZMod P) = ((x.val : ℕ) : ZMod P) :=
      mul_right_cancel₀ hMne hJM
    have hdvd : (P : ℤ) ∣ ((x.val + 1 + i : ℕ) : ℤ) - ((x.val : ℕ) : ℤ) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast at hji ⊢
      rw [hji, sub_self]
    have hji_eq : ((x.val + 1 + i : ℕ) : ℤ) - ((x.val : ℕ) : ℤ) = ((1 + i : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hji_eq] at hdvd
    have hle : P ≤ 1 + i := Nat.le_of_dvd (by omega) (Int.natCast_dvd_natCast.mp hdvd)
    omega
  have hF1 : ∀ q : ℕ, q.Prime → q ∣ n → q ≠ P → ¬ (q : ℤ) ∣ b + (i : ℤ) * (M : ℤ) := by
    intro q hq hqn hne hqt
    have hqmem : q ∈ n.primeFactors := hq.mem_primeFactors hqn (by omega)
    have hqr : q ∣ radical n := by
      rw [Nat.radical_eq_prod_primeFactors]
      exact Finset.dvd_prod_of_mem _ hqmem
    have hqPM : q ∣ P * M := by
      rw [hPM]
      exact hqr
    have hqM : q ∣ M := by
      rcases (hq.dvd_mul.mp hqPM) with h | h
      · exfalso
        exact hne ((hP.dvd_iff_eq hq.ne_one).mp h).symm
      · exact h
    have hqjM : (q : ℤ) ∣ ((x.val + 1 + i : ℕ) : ℤ) * ((M : ℕ) : ℤ) :=
      (Int.natCast_dvd_natCast.mpr hqM).mul_left _
    rw [htb] at hqt
    have hsub := dvd_sub hqt hqjM
    rw [add_sub_cancel_right] at hsub
    have h2 : q ∣ 1 := by exact_mod_cast hsub
    exact hq.ne_one (Nat.dvd_one.mp h2)
  have ht0 : (0 : ℤ) ≤ b + (i : ℤ) * (M : ℤ) := by linarith
  have hcop : Nat.Coprime (b + (i : ℤ) * (M : ℤ)).natAbs n := by
    by_contra hcon
    have hgcd : Nat.gcd (b + (i : ℤ) * (M : ℤ)).natAbs n ≠ 1 := hcon
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hgcd
    have hqT : q ∣ (b + (i : ℤ) * (M : ℤ)).natAbs := hqdvd.trans (Nat.gcd_dvd_left _ _)
    have hqn : q ∣ n := hqdvd.trans (Nat.gcd_dvd_right _ _)
    have hqt : (q : ℤ) ∣ b + (i : ℤ) * (M : ℤ) := by
      have h := Int.natCast_dvd_natCast.mpr hqT
      rwa [Int.natAbs_of_nonneg ht0] at h
    rcases eq_or_ne q P with rfl | hne
    · exact hF2 hqt
    · exact hF1 q hq hqn hne hqt
  have hIsCop : IsCoprime (b + (i : ℤ) * (M : ℤ)) ((n : ℕ) : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr (by exact hcop)
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩, ?_⟩
  exact Int.isCoprime_iff_gcd_eq_one.mp hIsCop

end isGreatest_longestAPLength

open isGreatest_longestAPLength in
/-- **Maximum longest progression length over all reduced residue windows.** Let $n > 1$ be a
natural number, $\operatorname{rad}(n)$ the product of its distinct prime factors and
$\operatorname{gpf}(n)$ its largest prime factor. For an integer $m$ let $f_m(n)$ be the length of
the longest arithmetic progression with positive common difference contained in the set $R_m(n)$
of integers $a$ with $m + 1 \le a \le m + n$ and $\gcd(a, n) = 1$. Then the largest value of
$f_m(n)$ over all integers $m$ is $\max(n / \operatorname{rad}(n), \operatorname{gpf}(n) - 1)$.

Source: Chaninat Phothila, Natthakan Thoket and Narakorn Rompurk Kanasri, *Length of the Longest
Arithmetic Progressions in a Certain Reduced Residue System*, INTEGERS 26 (2026), Article A6,
Theorem 2 (`integers-2026-A6-thm-2`). -/
public theorem isGreatest_longestAPLength {n : ℕ} (hn : 1 < n) :
    IsGreatest (Set.range fun m : ℤ => longestAPLength m n)
      (max (n / radical n) (n.primeFactors.sup id - 1))
    := by
  obtain ⟨m, hm⟩ := exists_le_gpf_sub_one hn
  have hmax : max (n / radical n) (n.primeFactors.sup id - 1) ≤ longestAPLength m n :=
    max_le (lower_bound m (by omega)) hm
  have hle : longestAPLength m n ≤ max (n / radical n) (n.primeFactors.sup id - 1) :=
    upper_bound m hn
  constructor
  · exact ⟨m, le_antisymm hle hmax⟩
  · rintro _ ⟨m', rfl⟩
    exact upper_bound m' hn

end

end MetaMathlibExt
