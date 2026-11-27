/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.NumberTheory.QuadraticForms.GaussClassNumber
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Hua's bound for the class number `h(-4D)`

This module proves `gaussClassNumber_neg_four_mul_lt`: for every positive integer `D`, the Gauss
class number of the discriminant `-4D` satisfies `h(-4D) < (4/π) √D log(2e√D)`. This is the bound
that Chakraborty and Sharma, *A Note on Terai's Conjecture Related to Exponential Diophantine
Equations*, INTEGERS 26 (2026), Article A67, Theorem 3, quote from Hua's textbook.

The proof here is elementary and does not use Dirichlet's class number formula. A reduced form
`(a, 2β, c)` of discriminant `-4D` has `3a² ≤ 4D`, and `β` is a square root of `-D` modulo `a`
lying in `(-a/2, a/2]`. So `h(-4D)` is at most `∑_{a ≤ A} R(a)`, where `A = ⌊√(4D/3)⌋` and `R(a)`
is the number of square roots of `-D` modulo `a`. By the Chinese remainder theorem `R` is
submultiplicative, and counting roots modulo prime powers gives `R(a) ≤ ∑_{e ∣ a} G(e)` for a
multiplicative function `G` with `G(p ^ k) ≤ p ^ ⌊k/2⌋`. The map `∏ p ^ k ↦ ∏ p ^ ⌈k/2⌉` is
injective on the support of `G`, so `∑_{e ≤ A} G(e)/e ≤ ∑_{n ≤ A} 1/n`. Hence
`h(-4D) ≤ A (1 + log A)`, which is below Hua's bound because `2/√3 < 4/π`.
-/

open Finset

namespace MetaMathlibExt.gaussClassNumber_neg_four_mul_lt

/-- The number `R(n)` of square roots of `-D` modulo `n`, that is, of residues `x < n` with
`n ∣ x ^ 2 + D`. -/
private def rootCount (D n : ℕ) : ℕ := #{x ∈ range n | n ∣ x ^ 2 + D}

/-- A residue class modulo a divisor `M` of `N` has `N / M` elements in `[0, N)`. -/
private theorem card_range_filter_modEq {N M : ℕ} (hM : 0 < M) (hMN : M ∣ N) (v : ℕ) :
    #{x ∈ range N | x ≡ v [MOD M]} = N / M := by
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hM, Nat.mod_eq_zero_of_dvd hMN]
  simp

/-- If `p ^ k ∣ x ^ 2 + D` with `k > v_p(D)`, then `x ≠ 0` and `2 v_p(x) = v_p(D)`. -/
private theorem two_mul_factorization_eq {p D x k : ℕ} (hp : p.Prime) (hD : D ≠ 0)
    (hk : D.factorization p < k) (hx : p ^ k ∣ x ^ 2 + D) :
    x ≠ 0 ∧ 2 * x.factorization p = D.factorization p := by
  set j := D.factorization p with hj
  have hpj : p ^ j ∣ D := Nat.ordProj_dvd D p
  have hpj1 : ¬ p ^ (j + 1) ∣ D := Nat.pow_succ_factorization_not_dvd hD hp
  have hdvd : ∀ n ≤ k, p ^ n ∣ x ^ 2 + D := fun n hn => (pow_dvd_pow p hn).trans hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hpj1 (by simpa using hdvd (j + 1) hk)
  refine ⟨hx0, ?_⟩
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
  have hfac : (x ^ 2).factorization p = 2 * x.factorization p := by
    simp [Nat.factorization_pow]
  rcases lt_trichotomy (2 * x.factorization p) j with h | h | h
  · exfalso
    have h1 : p ^ (2 * x.factorization p + 1) ∣ D := (pow_dvd_pow p h).trans hpj
    have h2 : p ^ (2 * x.factorization p + 1) ∣ x ^ 2 :=
      (Nat.dvd_add_left h1).mp (hdvd _ (by omega))
    rw [hp.pow_dvd_iff_le_factorization hx2, hfac] at h2
    omega
  · exact h
  · exfalso
    have h1 : p ^ (j + 1) ∣ x ^ 2 := by
      rw [hp.pow_dvd_iff_le_factorization hx2, hfac]; omega
    exact hpj1 ((Nat.dvd_add_right h1).mp (hdvd (j + 1) hk))

/-- If `p ^ k ∣ D`, the roots modulo `p ^ k` are the multiples of `p ^ ⌈k/2⌉`, so there are at
most `p ^ ⌊k/2⌋` of them. -/
private theorem rootCount_le_of_le {p D k : ℕ} (hp : p.Prime) (hk : k ≤ D.factorization p) :
    rootCount D (p ^ k) ≤ p ^ (k / 2) := by
  have hpk : p ^ k ∣ D := (pow_dvd_pow p hk).trans (Nat.ordProj_dvd D p)
  have hsub : {x ∈ range (p ^ k) | p ^ k ∣ x ^ 2 + D} ⊆
      {x ∈ range (p ^ k) | x ≡ 0 [MOD p ^ ((k + 1) / 2)]} := by
    intro x hx
    simp only [mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rw [Nat.modEq_zero_iff_dvd]
    have hx2 : p ^ k ∣ x ^ 2 := (Nat.dvd_add_left hpk).mp hx.2
    rcases eq_or_ne x 0 with rfl | hx0
    · exact dvd_zero _
    · rw [hp.pow_dvd_iff_le_factorization hx0]
      rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hx0), Nat.factorization_pow] at hx2
      simp only [Finsupp.smul_apply, smul_eq_mul] at hx2
      omega
  calc rootCount D (p ^ k) ≤ _ := card_le_card hsub
    _ = p ^ k / p ^ ((k + 1) / 2) :=
      card_range_filter_modEq (pow_pos hp.pos _) (pow_dvd_pow p (by omega)) 0
    _ = p ^ (k / 2) := by rw [Nat.pow_div (by omega) hp.pos]; congr 1; omega

/-- If `v_p(D)` is odd, there are no roots modulo `p ^ k` for `k > v_p(D)`. -/
private theorem rootCount_eq_zero_of_odd {p D k : ℕ} (hp : p.Prime) (hD : D ≠ 0)
    (hk : D.factorization p < k) (hj : Odd (D.factorization p)) :
    rootCount D (p ^ k) = 0 := by
  rw [rootCount, card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  have h := (two_mul_factorization_eq hp hD hk hx).2
  rw [← h] at hj
  exact (Nat.not_even_iff_odd.mpr hj) (even_two_mul _)

/-- A root `x` with `v_p(x) = m` is `p ^ m` times a unit. -/
private theorem eq_pow_mul_of_factorization {p x m : ℕ} (hp : p.Prime) (hx0 : x ≠ 0)
    (hm : x.factorization p = m) : ∃ u, x = p ^ m * u ∧ ¬ p ∣ u := by
  refine ⟨ordCompl[p] x, ?_, Nat.not_dvd_ordCompl hp hx0⟩
  rw [← hm, Nat.ordProj_mul_ordCompl_eq_self]

/-- If `v_2(D) = 2m` and `2m < k ≤ 2m + 2`, every root modulo `2 ^ k` is `2 ^ m` times an odd
number, so there are at most `2 ^ (m + 1)` roots. -/
private theorem rootCount_two_le {D k m : ℕ} (hD : D ≠ 0) (hm : D.factorization 2 = 2 * m)
    (hk : 2 * m < k) (hk2 : k ≤ 2 * m + 2) :
    rootCount D (2 ^ k) ≤ 2 ^ (m + 1) := by
  have hsub : {x ∈ range (2 ^ k) | 2 ^ k ∣ x ^ 2 + D} ⊆
      {x ∈ range (2 ^ k) | x ≡ 2 ^ m [MOD 2 ^ (m + 1)]} := by
    intro x hx
    simp only [mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    obtain ⟨hx0, hv⟩ := two_mul_factorization_eq Nat.prime_two hD (by omega) hx.2
    obtain ⟨u, rfl, hu⟩ := eq_pow_mul_of_factorization Nat.prime_two hx0
      (show x.factorization 2 = m by omega)
    obtain ⟨t, rfl⟩ : ∃ t, u = 2 * t + 1 := ⟨u / 2, by omega⟩
    have : 2 ^ m * (2 * t + 1) = 2 ^ m + 2 ^ (m + 1) * t := by ring
    rw [this, Nat.ModEq, Nat.add_mul_mod_self_left]
  calc rootCount D (2 ^ k) ≤ _ := card_le_card hsub
    _ = 2 ^ k / 2 ^ (m + 1) :=
      card_range_filter_modEq (by positivity) (pow_dvd_pow 2 (by omega)) _
    _ ≤ 2 ^ (m + 1) := by
      rw [Nat.pow_div (by omega) (by norm_num)]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- If `p ^ (s + e) ∣ (u - w)(u + w)` and `p ^ (e + 1) ∤ 2u`, then `p ^ s` divides `u - w` or
`u + w`. -/
private theorem dvd_sub_or_dvd_add {p s e : ℕ} [Fact p.Prime] {u w : ℤ}
    (he : ¬ (p : ℤ) ^ (e + 1) ∣ 2 * u) (h : (p : ℤ) ^ (s + e) ∣ (u - w) * (u + w)) :
    (p : ℤ) ^ s ∣ u - w ∨ (p : ℤ) ^ s ∣ u + w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hne1 : u - w ≠ 0 := by rintro h0; rw [h0] at h1; exact h1 (dvd_zero _)
  have hne2 : u + w ≠ 0 := by rintro h0; rw [h0] at h2; exact h2 (dvd_zero _)
  rw [padicValInt_dvd_iff] at h h1 h2
  simp only [hne1, hne2, mul_ne_zero hne1 hne2, false_or, not_le] at h h1 h2
  rw [padicValInt.mul hne1 hne2] at h
  have hmin : padicValInt p (u - w) ≤ e ∨ padicValInt p (u + w) ≤ e := by
    by_contra hc
    push Not at hc
    apply he
    have h3 : (p : ℤ) ^ (e + 1) ∣ (u - w) + (u + w) := by
      apply dvd_add <;> rw [padicValInt_dvd_iff] <;> right <;> omega
    convert h3 using 1
    ring
  omega

/-- If `v_p(D) = 2m` and `k > 2m + e`, where `p ^ (e + 1)` divides no `2u` with `p ∤ u`, all
roots modulo `p ^ k` lie in the two classes `±x₀` modulo `p ^ (k - m - e)`, so there are at most
`2 p ^ (m + e)` of them. -/
private theorem rootCount_le_two_mul {p D k e m : ℕ} (hp : p.Prime) (hD : D ≠ 0)
    (hm : D.factorization p = 2 * m) (hke : 2 * m + e < k)
    (he : ∀ u : ℤ, ¬ (p : ℤ) ∣ u → ¬ (p : ℤ) ^ (e + 1) ∣ 2 * u) :
    rootCount D (p ^ k) ≤ 2 * p ^ (m + e) := by
  have := Fact.mk hp
  have hk : D.factorization p < k := by omega
  have hMpos : 0 < p ^ (k - m - e) := pow_pos hp.pos _
  have hMdvd : p ^ (k - m - e) ∣ p ^ k := pow_dvd_pow p (by omega)
  have hcount : p ^ k / p ^ (k - m - e) = p ^ (m + e) := by
    rw [Nat.pow_div (by omega) hp.pos]; congr 1; omega
  rcases (filter (fun x => p ^ k ∣ x ^ 2 + D) (range (p ^ k))).eq_empty_or_nonempty with
    h0 | ⟨x₀, hx₀⟩
  · rw [rootCount, h0, card_empty]; exact Nat.zero_le _
  simp only [mem_filter, mem_range] at hx₀
  obtain ⟨hx₀0, hv₀⟩ := two_mul_factorization_eq hp hD hk hx₀.2
  obtain ⟨u₀, hxu₀, hu₀⟩ :=
    eq_pow_mul_of_factorization hp hx₀0 (show x₀.factorization p = m by omega)
  have hsub : {x ∈ range (p ^ k) | p ^ k ∣ x ^ 2 + D} ⊆
      {x ∈ range (p ^ k) | x ≡ x₀ [MOD p ^ (k - m - e)]} ∪
        {x ∈ range (p ^ k) | x ≡ p ^ k - x₀ [MOD p ^ (k - m - e)]} := by
    intro x hx
    simp only [mem_filter, mem_union, mem_range] at hx ⊢
    obtain ⟨hx0, hv⟩ := two_mul_factorization_eq hp hD hk hx.2
    obtain ⟨u, hxu, hu⟩ :=
      eq_pow_mul_of_factorization hp hx0 (show x.factorization p = m by omega)
    have hdiff : ((p ^ k : ℕ) : ℤ) ∣
        ((p ^ m : ℕ) : ℤ) ^ 2 * (((u : ℤ) - u₀) * ((u : ℤ) + u₀)) := by
      have h1 : ((p ^ k : ℕ) : ℤ) ∣ ((x ^ 2 + D : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hx.2
      have h2 : ((p ^ k : ℕ) : ℤ) ∣ ((x₀ ^ 2 + D : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr hx₀.2
      convert dvd_sub h1 h2 using 1
      rw [hxu, hxu₀]; push_cast; ring
    have hsplit : ((p ^ k : ℕ) : ℤ) =
        ((p ^ m : ℕ) : ℤ) ^ 2 * (p : ℤ) ^ (k - 2 * m - e + e) := by
      push_cast; rw [← pow_mul, ← pow_add]; congr 1; omega
    rw [hsplit] at hdiff
    have hpm : ((p ^ m : ℕ) : ℤ) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (by exact_mod_cast (pow_pos hp.pos m).ne')
    have hu' : ¬ (p : ℤ) ∣ (u : ℤ) := by exact_mod_cast hu
    have hM : ((p ^ (k - m - e) : ℕ) : ℤ) = ((p ^ m : ℕ) : ℤ) * (p : ℤ) ^ (k - 2 * m - e) := by
      push_cast; rw [← pow_add]; congr 1; omega
    rcases dvd_sub_or_dvd_add (he u hu') ((mul_dvd_mul_iff_left hpm).mp hdiff) with h | h
    · refine Or.inl ⟨hx.1, ?_⟩
      rw [Nat.modEq_iff_dvd, hM, hxu, hxu₀]
      push_cast
      rw [show ((p : ℤ) ^ m * u₀ - (p : ℤ) ^ m * u) = (p : ℤ) ^ m * (u₀ - u) by ring]
      exact mul_dvd_mul_left _ (by rw [← dvd_neg, neg_sub]; exact h)
    · refine Or.inr ⟨hx.1, ?_⟩
      rw [Nat.modEq_iff_dvd, Nat.cast_sub hx₀.1.le]
      have hMk : ((p ^ (k - m - e) : ℕ) : ℤ) ∣ ((p ^ k : ℕ) : ℤ) :=
        Int.natCast_dvd_natCast.mpr hMdvd
      have hsum : ((p ^ (k - m - e) : ℕ) : ℤ) ∣ (x : ℤ) + x₀ := by
        rw [hM, hxu, hxu₀]
        push_cast
        rw [show ((p : ℤ) ^ m * u + (p : ℤ) ^ m * u₀) = (p : ℤ) ^ m * (u + u₀) by ring]
        exact mul_dvd_mul_left _ h
      convert dvd_sub hMk hsum using 1
      ring
  calc rootCount D (p ^ k) ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ = 2 * p ^ (m + e) := by
      rw [card_range_filter_modEq hMpos hMdvd, card_range_filter_modEq hMpos hMdvd, hcount]
      ring

/-- Local weights at a prime `p`, with `j = v_p(D)`: `g 0 = 1`; for `1 ≤ i ≤ j`, `g i = p ^ (i/2)`
if `i` is even and `0` otherwise; if `j` is even, `g (j + 1) = p ^ (j/2)`, and for `p = 2` also
`g (j + 3) = 2 ^ (j/2 + 1)`; all other weights vanish. Their partial sums bound the number of
roots modulo `p ^ k`. -/
private def g (D p i : ℕ) : ℕ :=
  if i = 0 then 1
  else if i ≤ D.factorization p then (if Even i then p ^ (i / 2) else 0)
  else if Even (D.factorization p) ∧ i = D.factorization p + 1 then p ^ (D.factorization p / 2)
  else if Even (D.factorization p) ∧ p = 2 ∧ i = D.factorization p + 3 then
    2 ^ (D.factorization p / 2 + 1)
  else 0

private theorem g_zero (D p : ℕ) : g D p 0 = 1 := by simp [g]

private theorem g_le (D p i : ℕ) (hp : 0 < p) : g D p i ≤ p ^ (i / 2) := by
  unfold g
  split_ifs with h0 h1 h2 h3 h4
  · simp [h0]
  · exact le_rfl
  · exact Nat.zero_le _
  · exact Nat.pow_le_pow_right hp (by obtain ⟨r, hr⟩ := h3.1; omega)
  · obtain ⟨hj, rfl, hi⟩ := h4
    exact Nat.pow_le_pow_right hp (by obtain ⟨r, hr⟩ := hj; omega)
  · exact Nat.zero_le _

/-- Of two weights at `2t - 1` and `2t`, one vanishes. -/
private theorem g_pair (D p t : ℕ) (ht : 0 < t) : g D p (2 * t - 1) = 0 ∨ g D p (2 * t) = 0 := by
  by_cases h : 2 * t ≤ D.factorization p
  · left
    have hodd : ¬ Even (2 * t - 1) := by rw [Nat.not_even_iff_odd]; exact ⟨t - 1, by omega⟩
    simp [g, show 2 * t - 1 ≠ 0 by omega, show 2 * t - 1 ≤ D.factorization p by omega, hodd]
  · right
    have h1 : ¬ (Even (D.factorization p) ∧ 2 * t = D.factorization p + 1) := by
      rintro ⟨⟨r, hr⟩, h'⟩; omega
    have h2 : ¬ (Even (D.factorization p) ∧ p = 2 ∧ 2 * t = D.factorization p + 3) := by
      rintro ⟨⟨r, hr⟩, -, h'⟩; omega
    simp only [g, show 2 * t ≠ 0 by omega, h, h1, h2, ↓reduceIte]

private theorem g_even_self {D p m : ℕ} (hm : D.factorization p = 2 * m) :
    g D p (2 * m) = p ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp [g]
  · simp [g, hm, show 2 * m ≠ 0 by omega]

private theorem g_succ {D p m : ℕ} (hm : D.factorization p = 2 * m) :
    g D p (2 * m + 1) = p ^ m := by
  simp [g, hm]

private theorem g_add_three {D m : ℕ} (hm : D.factorization 2 = 2 * m) :
    g D 2 (2 * m + 3) = 2 ^ (m + 1) := by
  simp [g, hm]

/-- The number of roots modulo `p ^ k` is at most `∑_{i ≤ k} g i`. -/
private theorem rootCount_pow_le {p D : ℕ} (hp : p.Prime) (hD : D ≠ 0) (k : ℕ) :
    rootCount D (p ^ k) ≤ ∑ i ∈ range (k + 1), g D p i := by
  rcases le_or_gt k (D.factorization p) with hk | hk
  · -- `k ≤ v_p(D)`: the roots are the multiples of `p ^ ⌈k/2⌉`
    refine (rootCount_le_of_le hp hk).trans ?_
    have hmem : 2 * (k / 2) ∈ range (k + 1) := mem_range.mpr (by omega)
    refine le_trans ?_ (single_le_sum (fun _ _ => Nat.zero_le _) hmem)
    rcases Nat.eq_zero_or_pos (k / 2) with h0 | h0
    · simp [h0, g_zero]
    · have he : Even (2 * (k / 2)) := even_two_mul _
      simp [g, show 2 * (k / 2) ≠ 0 by omega, show 2 * (k / 2) ≤ D.factorization p by omega, he]
  rcases Nat.even_or_odd (D.factorization p) with ⟨m, hm⟩ | hodd
  · rw [← two_mul] at hm
    have hpair : ∑ i ∈ ({2 * m, 2 * m + 1} : Finset ℕ), g D p i ≤
        ∑ i ∈ range (k + 1), g D p i :=
      sum_le_sum_of_subset (by intro i; simp only [mem_insert, mem_singleton, mem_range]; omega)
    rw [sum_pair (by omega), g_even_self hm, g_succ hm] at hpair
    by_cases hp2 : p = 2
    · subst hp2
      rcases le_or_gt k (2 * m + 2) with hk2 | hk2
      · calc rootCount D (2 ^ k) ≤ 2 ^ (m + 1) := rootCount_two_le hD hm (by omega) hk2
          _ = 2 ^ m + 2 ^ m := by ring
          _ ≤ _ := hpair
      · have htriple : ∑ i ∈ ({2 * m, 2 * m + 1, 2 * m + 3} : Finset ℕ), g D 2 i ≤
            ∑ i ∈ range (k + 1), g D 2 i :=
          sum_le_sum_of_subset (by intro i; simp only [mem_insert, mem_singleton, mem_range]; omega)
        rw [sum_insert (by simp), sum_pair (by omega), g_even_self hm, g_succ hm,
          g_add_three hm] at htriple
        calc rootCount D (2 ^ k) ≤ 2 * 2 ^ (m + 1) :=
              rootCount_le_two_mul Nat.prime_two hD hm (by omega) (fun u hu h4 => hu (by
                have : (4 : ℤ) ∣ 2 * u := by simpa using h4
                omega))
          _ = 2 ^ m + (2 ^ m + 2 ^ (m + 1)) := by ring
          _ ≤ _ := htriple
    · calc rootCount D (p ^ k) ≤ 2 * p ^ (m + 0) :=
            rootCount_le_two_mul hp hD hm (by omega) (fun u hu h2 => by
              simp only [zero_add, pow_one] at h2
              rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h2 with h | h
              · have := Int.le_of_dvd (by norm_num) h
                have : (p : ℤ) ≠ 2 := by exact_mod_cast hp2
                have := hp.two_le
                omega
              · exact hu h)
        _ = p ^ m + p ^ m := by ring
        _ ≤ _ := hpair
  · rw [rootCount_eq_zero_of_odd hp hD hk hodd]
    exact Nat.zero_le _

private theorem rootCount_one (D : ℕ) : rootCount D 1 = 1 := by
  simp [rootCount]

/-- Chinese remainder theorem: `R(mn) ≤ R(m) R(n)` for coprime `m` and `n`. -/
private theorem rootCount_mul_le {D m n : ℕ} (hmn : m.Coprime n) (hm : 0 < m) (hn : 0 < n) :
    rootCount D (m * n) ≤ rootCount D m * rootCount D n := by
  rw [rootCount, rootCount, rootCount, ← card_product]
  refine card_le_card_of_injOn (fun x => (x % m, x % n)) ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx
    simp only [coe_product, coe_filter, mem_range, Set.mem_prod, Set.mem_ofPred_eq]
    have hmod : ∀ r, 0 < r → r ∣ x ^ 2 + D → r ∣ (x % r) ^ 2 + D := fun r _ hr =>
      (Nat.modEq_zero_iff_dvd.mp (((Nat.mod_modEq x r).pow 2).add_right D |>.trans
        (Nat.modEq_zero_iff_dvd.mpr hr)))
    exact ⟨⟨Nat.mod_lt _ hm, hmod m hm (dvd_trans (dvd_mul_right m n) hx.2)⟩,
      ⟨Nat.mod_lt _ hn, hmod n hn (dvd_trans (dvd_mul_left n m) hx.2)⟩⟩
  · intro x hx y hy hxy
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hx hy
    simp only [Prod.mk.injEq] at hxy
    have h : x ≡ y [MOD m * n] := (Nat.modEq_and_modEq_iff_modEq_mul hmn).mp ⟨hxy.1, hxy.2⟩
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h

/-- The multiplicative function `G` with `G (p ^ i) = g D p i`. -/
private def G (D : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun e => if e = 0 then 0 else e.factorization.prod (g D), by simp⟩

private theorem G_apply {D e : ℕ} (he : e ≠ 0) : G D e = e.factorization.prod (g D) := by
  simp [G, he]

private theorem G_isMultiplicative (D : ℕ) : (G D).IsMultiplicative := by
  refine ⟨by simp [G_apply], fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn; subst hmn; simp [G]
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn; subst hmn; simp [G]
  rw [G_apply (mul_ne_zero hm hn), G_apply hm, G_apply hn, Nat.factorization_mul_of_coprime hmn,
    Finsupp.prod_add_index_of_disjoint
      (by simpa [Nat.support_factorization] using hmn.disjoint_primeFactors)]

private theorem G_prime_pow {D p : ℕ} (hp : p.Prime) (i : ℕ) : G D (p ^ i) = g D p i := by
  rw [G_apply (pow_ne_zero _ hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (g_zero D p)]

/-- `R(a) ≤ ∑_{e ∣ a} G(e)`. -/
private theorem rootCount_le_G_mul_zeta {D : ℕ} (hD : D ≠ 0) (a : ℕ) :
    rootCount D a ≤ (G D * ArithmeticFunction.zeta) a := by
  induction a using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    rw [ArithmeticFunction.mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    simp_rw [G_prime_pow hp]
    exact rootCount_pow_le hp hD n
  | zero => simp [rootCount]
  | one => simp [rootCount_one, (G_isMultiplicative D).map_one]
  | coprime a b ha hb hab iha ihb =>
    calc rootCount D (a * b) ≤ rootCount D a * rootCount D b :=
          rootCount_mul_le hab (by omega) (by omega)
      _ ≤ (G D * ArithmeticFunction.zeta) a * (G D * ArithmeticFunction.zeta) b :=
          Nat.mul_le_mul iha ihb
      _ = (G D * ArithmeticFunction.zeta) (a * b) :=
          (((G_isMultiplicative D).mul ArithmeticFunction.isMultiplicative_zeta).map_mul_of_coprime
            hab).symm

/-- The compression map `∏ p ^ k ↦ ∏ p ^ ⌈k/2⌉`. -/
private def ν (e : ℕ) : ℕ := e.factorization.prod fun p k => p ^ ((k + 1) / 2)

private theorem ν_factorization (e : ℕ) :
    (ν e).factorization = e.factorization.mapRange (fun k => (k + 1) / 2) (by simp) := by
  have h : ν e = (e.factorization.mapRange (fun k => (k + 1) / 2) (by simp)).prod (· ^ ·) := by
    rw [ν, Finsupp.prod_mapRange_index (by simp)]
  rw [h, Nat.factorization_prod_pow_eq_self]
  intro p hp
  exact Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)

private theorem ν_pos (e : ℕ) : 0 < ν e := by
  rw [ν, Finsupp.prod]
  refine Finset.prod_pos fun p hp => pow_pos ?_ _
  exact (Nat.prime_of_mem_primeFactors hp).pos

/-- `G(e) ν(e) ≤ e`, since `g D p k ≤ p ^ ⌊k/2⌋`. -/
private theorem G_mul_ν_le {D e : ℕ} (he : e ≠ 0) : G D e * ν e ≤ e := by
  rw [G_apply he, ν, ← Finsupp.prod_mul]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self he]
  refine Finset.prod_le_prod fun p hp => ?_
  have hp' : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
  calc g D p (e.factorization p) * p ^ ((e.factorization p + 1) / 2)
      ≤ p ^ (e.factorization p / 2) * p ^ ((e.factorization p + 1) / 2) :=
        Nat.mul_le_mul_right _ (g_le D p _ hp')
    _ = p ^ e.factorization p := by rw [← pow_add]; congr 1; omega

private theorem factorization_eq_zero_or_g_ne_zero {D e : ℕ} (he : e ≠ 0) (hG : G D e ≠ 0) (p : ℕ) :
    e.factorization p = 0 ∨ g D p (e.factorization p) ≠ 0 := by
  rw [G_apply he, Finsupp.prod, Finset.prod_ne_zero_iff] at hG
  by_cases hp : e.factorization p = 0
  · exact Or.inl hp
  · exact Or.inr (hG p (Finsupp.mem_support_iff.mpr hp))

/-- `ν` is injective on the support of `G`, since of the exponents `2t - 1` and `2t`, which have
the same image, at most one carries a nonzero weight. -/
private theorem ν_injOn (D : ℕ) : Set.InjOn ν {e | e ≠ 0 ∧ G D e ≠ 0} := by
  intro e he e' he' h
  apply Nat.eq_of_factorization_eq he.1 he'.1
  intro p
  have hp := DFunLike.congr_fun (congrArg Nat.factorization h) p
  rw [ν_factorization, ν_factorization, Finsupp.mapRange_apply, Finsupp.mapRange_apply] at hp
  have h1 := factorization_eq_zero_or_g_ne_zero he.1 he.2 p
  have h2 := factorization_eq_zero_or_g_ne_zero he'.1 he'.2 p
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨t, ht, ht1, ht2⟩ : ∃ t, 0 < t ∧ e.factorization p = 2 * t - 1 ∧
        e'.factorization p = 2 * t := ⟨(e.factorization p + 1) / 2, by omega, by omega, by omega⟩
    rcases g_pair D p t ht with h0 | h0
    · rcases h1 with h1 | h1 <;> [omega; exact h1 (ht1 ▸ h0)]
    · rcases h2 with h2 | h2 <;> [omega; exact h2 (ht2 ▸ h0)]
  · obtain ⟨t, ht, ht1, ht2⟩ : ∃ t, 0 < t ∧ e'.factorization p = 2 * t - 1 ∧
        e.factorization p = 2 * t := ⟨(e'.factorization p + 1) / 2, by omega, by omega, by omega⟩
    rcases g_pair D p t ht with h0 | h0
    · rcases h2 with h2 | h2 <;> [omega; exact h2 (ht1 ▸ h0)]
    · rcases h1 with h1 | h1 <;> [omega; exact h1 (ht2 ▸ h0)]

/-- `∑_{e ≤ N} G(e)/e ≤ ∑_{n ≤ N} 1/n`. -/
private theorem sum_G_div_le (D N : ℕ) :
    ∑ e ∈ Ioc 0 N, (G D e : ℝ) / e ≤ ∑ n ∈ Ioc 0 N, (1 : ℝ) / n := by
  set S := (Ioc 0 N).filter (fun e => G D e ≠ 0) with hS
  have hinj : Set.InjOn ν S := fun e he e' he' h => by
    simp only [hS, coe_filter, mem_Ioc, Set.mem_ofPred_eq] at he he'
    exact ν_injOn D ⟨by omega, he.2⟩ ⟨by omega, he'.2⟩ h
  calc ∑ e ∈ Ioc 0 N, (G D e : ℝ) / e = ∑ e ∈ S, (G D e : ℝ) / e := by
        rw [hS, sum_filter_of_ne]
        intro e _ he h0
        simp [h0] at he
    _ ≤ ∑ e ∈ S, (1 : ℝ) / ν e := by
        refine sum_le_sum fun e he => ?_
        simp only [hS, mem_filter, mem_Ioc] at he
        have hle := G_mul_ν_le (D := D) (e := e) (by omega)
        rw [div_le_div_iff₀ (by exact_mod_cast he.1.1) (by exact_mod_cast ν_pos e), one_mul]
        exact_mod_cast hle
    _ = ∑ n ∈ S.image ν, (1 : ℝ) / n := (sum_image (f := fun n : ℕ => (1 : ℝ) / n) hinj).symm
    _ ≤ ∑ n ∈ Ioc 0 N, (1 : ℝ) / n := by
        refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro n hn
        simp only [mem_image, hS, mem_filter, mem_Ioc] at hn
        obtain ⟨e, ⟨⟨he0, heN⟩, hG⟩, rfl⟩ := hn
        have hle := G_mul_ν_le (D := D) (e := e) (by omega)
        have hG1 : 1 ≤ G D e := Nat.one_le_iff_ne_zero.mpr hG
        refine mem_Ioc.mpr ⟨ν_pos e, ?_⟩
        nlinarith [ν_pos e]

/-- `∑_{a ≤ A} R(a) ≤ A (1 + log A)`. -/
private theorem sum_rootCount_le {D : ℕ} (hD : D ≠ 0) (A : ℕ) :
    (∑ a ∈ Ioc 0 A, (rootCount D a : ℝ)) ≤ A * (1 + Real.log A) := by
  calc (∑ a ∈ Ioc 0 A, (rootCount D a : ℝ))
      ≤ ∑ a ∈ Ioc 0 A, ((G D * ArithmeticFunction.zeta) a : ℝ) := by
        exact_mod_cast sum_le_sum fun a _ => rootCount_le_G_mul_zeta hD a
    _ = ∑ e ∈ Ioc 0 A, (G D e : ℝ) * ((A / e : ℕ) : ℝ) := by
        have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (G D) A
        rw [ArithmeticFunction.natCoe_nat] at h
        exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
    _ ≤ ∑ e ∈ Ioc 0 A, (G D e : ℝ) * ((A : ℝ) / e) :=
        sum_le_sum fun e _ => mul_le_mul_of_nonneg_left Nat.cast_div_le (Nat.cast_nonneg _)
    _ = A * ∑ e ∈ Ioc 0 A, (G D e : ℝ) / e := by
        rw [mul_sum]; refine sum_congr rfl fun e _ => by ring
    _ ≤ A * ∑ n ∈ Ioc 0 A, (1 : ℝ) / n :=
        mul_le_mul_of_nonneg_left (sum_G_div_le D A) (Nat.cast_nonneg _)
    _ = A * (harmonic A : ℝ) := by
        rw [harmonic_eq_sum_Icc]; push_cast
        rw [← Finset.Icc_add_one_left_eq_Ioc]; simp [one_div]
    _ ≤ A * (1 + Real.log A) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log A) (Nat.cast_nonneg _)

/-- A reduced form `(a, b, c)` of discriminant `-4D` has `0 < a`, `-a < b ≤ a ≤ c` and
`b ^ 2 - 4ac = -4D`. -/
private theorem facts_of_mem {D : ℕ} {q : ℤ × ℤ × ℤ}
    (hq : q ∈ reducedFormsOfDiscriminant (-4 * D)) :
    0 < q.1 ∧ -q.1 < q.2.1 ∧ q.2.1 ≤ q.1 ∧ q.1 ≤ q.2.2 ∧
      q.2.1 ^ 2 - 4 * q.1 * q.2.2 = -4 * D := by
  simp only [reducedFormsOfDiscriminant, mem_filter] at hq
  obtain ⟨-, hred, hdisc⟩ := hq
  have hpos := hred.pos
  have hb := hred.loose_bounds
  refine ⟨hpos, ?_, hb.2, hred.le, by rw [← hdisc, discrim]⟩
  rcases hb.1.lt_or_eq with h | h
  · exact h
  · exfalso
    have := hred.boundary (Or.inl (by rw [← h, abs_neg, abs_of_pos hpos]))
    linarith

/-- For such a form, `b = 2β` with `a ∣ β ^ 2 + D`, and `3a² ≤ 4D`. -/
private theorem root_of_mem {D : ℕ} {a b c : ℤ} (ha : 0 < a) (hb1 : -a < b) (hb2 : b ≤ a)
    (hac : a ≤ c) (hdisc : b ^ 2 - 4 * a * c = -4 * D) :
    ∃ β : ℤ, b = 2 * β ∧ a ∣ β ^ 2 + D ∧ 3 * a ^ 2 ≤ 4 * D := by
  have h2 : (2 : ℤ) ∣ b := by
    have : Even (b ^ 2) := ⟨2 * (a * c - D), by linarith⟩
    exact even_iff_two_dvd.mp ((Int.even_pow' two_ne_zero).mp this)
  obtain ⟨β, rfl⟩ := h2
  refine ⟨β, rfl, ⟨c, by linarith⟩, ?_⟩
  nlinarith

/-- The reduced forms of discriminant `-4D` inject into the pairs `(a, x)` with
`a ≤ ⌊√(4D/3)⌋` and `x` a root modulo `a`, via `(a, 2β, c) ↦ (a, β mod a)`. -/
private theorem card_reducedForms_le {D : ℕ} :
    #(reducedFormsOfDiscriminant (-4 * D)) ≤
      ∑ a ∈ Ioc 0 (Nat.sqrt (4 * D / 3)), rootCount D a := by
  simp only [rootCount]
  rw [← card_sigma]
  refine card_le_card_of_injOn
    (fun q => (⟨q.1.toNat, ((q.2.1 / 2) % q.1).toNat⟩ : Σ _ : ℕ, ℕ)) ?_ ?_
  · intro q hq
    obtain ⟨ha, hb1, hb2, hac, hdisc⟩ := facts_of_mem (mem_coe.mp hq)
    obtain ⟨β, hβ, hdvd, h3⟩ := root_of_mem ha hb1 hb2 hac hdisc
    have hβ2 : q.2.1 / 2 = β := by rw [hβ]; omega
    simp only [coe_sigma, Set.mem_sigma_iff, coe_Ioc, Set.mem_Ioc, coe_filter, mem_range,
      Set.mem_ofPred_eq, hβ2]
    have hr0 : 0 ≤ β % q.1 := Int.emod_nonneg _ ha.ne'
    have hr1 : β % q.1 < q.1 := Int.emod_lt_of_pos _ ha
    refine ⟨⟨by omega, ?_⟩, by omega, ?_⟩
    · rw [Nat.le_sqrt, Nat.le_div_iff_mul_le (by norm_num)]
      have : ((q.1.toNat * q.1.toNat * 3 : ℕ) : ℤ) ≤ ((4 * D : ℕ) : ℤ) := by
        push_cast; rw [Int.toNat_of_nonneg ha.le]; nlinarith
      exact_mod_cast this
    · rw [← Int.natCast_dvd_natCast]
      push_cast
      rw [Int.toNat_of_nonneg ha.le, Int.toNat_of_nonneg hr0]
      have hmod : (β % q.1) ^ 2 + D ≡ β ^ 2 + D [ZMOD q.1] :=
        ((Int.mod_modEq β q.1).pow 2).add_right _
      exact (Int.ModEq.dvd_iff hmod).mpr hdvd
  · intro q hq q' hq' h
    obtain ⟨ha, hb1, hb2, hac, hdisc⟩ := facts_of_mem (mem_coe.mp hq)
    obtain ⟨ha', hb1', hb2', hac', hdisc'⟩ := facts_of_mem (mem_coe.mp hq')
    obtain ⟨β, hβ, -, -⟩ := root_of_mem ha hb1 hb2 hac hdisc
    obtain ⟨β', hβ', -, -⟩ := root_of_mem ha' hb1' hb2' hac' hdisc'
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    obtain ⟨h1, h2⟩ := h
    have haa : q.1 = q'.1 := by
      rw [← Int.toNat_of_nonneg ha.le, ← Int.toNat_of_nonneg ha'.le, h1]
    have hβ2 : q.2.1 / 2 = β := by rw [hβ]; omega
    have hβ2' : q'.2.1 / 2 = β' := by rw [hβ']; omega
    rw [hβ2, hβ2', ← haa] at h2
    have hmod : β % q.1 = β' % q.1 := by
      rw [← Int.toNat_of_nonneg (Int.emod_nonneg β ha.ne'),
        ← Int.toNat_of_nonneg (Int.emod_nonneg β' ha.ne'), h2]
    have hdvd : q.1 ∣ β' - β := Int.ModEq.dvd hmod
    have hββ : β' - β = 0 :=
      Int.eq_zero_of_abs_lt_dvd hdvd (by rw [abs_lt]; constructor <;> linarith)
    have hb : q.2.1 = q'.2.1 := by rw [hβ, hβ']; linarith
    have hc : q.2.2 = q'.2.2 := by
      have : 4 * q.1 * q.2.2 = 4 * q.1 * q'.2.2 := by
        rw [haa] at hdisc ⊢; rw [hb] at hdisc; linarith
      have h4 : (4 * q.1) ≠ 0 := by positivity
      exact mul_left_cancel₀ h4 this
    exact Prod.ext haa (Prod.ext hb hc)

/-- If `3A² ≤ 4D`, then `A (1 + log A) < (4/π) √D log(2e√D)`, since `2/√3 < 4/π`. -/
private theorem final_estimate {D A : ℕ} (hD : 0 < D) (hA : 3 * A ^ 2 ≤ 4 * D) :
    (A : ℝ) * (1 + Real.log A) <
      4 / Real.pi * Real.sqrt D * Real.log (2 * Real.exp 1 * Real.sqrt D) := by
  have hs : 1 ≤ Real.sqrt D := Real.one_le_sqrt.mpr (by exact_mod_cast hD)
  have hs2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt (Nat.cast_nonneg _)
  set s := Real.sqrt D with hsdef
  have hlog : Real.log (2 * Real.exp 1 * s) = Real.log 2 + 1 + Real.log s := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_exp]
  rw [hlog]
  have hL : 0 < Real.log 2 + 1 + Real.log s := by
    have := Real.log_nonneg hs
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith
  have hpi := Real.pi_pos
  have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
  have hAR : 3 * (A : ℝ) ^ 2 ≤ 4 * s ^ 2 := by rw [hs2]; exact_mod_cast hA
  rcases Nat.eq_zero_or_pos A with h0 | hApos
  · simp only [h0, Nat.cast_zero, zero_mul]
    positivity
  have hA1 : (1 : ℝ) ≤ A := by exact_mod_cast hApos
  have hA2s : (A : ℝ) ≤ 2 * s := by nlinarith
  have hlogA : Real.log A ≤ Real.log 2 + Real.log s := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) hA2s
  have hpiA : Real.pi * A < 4 * s := by
    have hpi_sq : Real.pi ^ 2 < 10 := by nlinarith
    have h1 : (Real.pi * A) ^ 2 < (4 * s) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h1
  calc (A : ℝ) * (1 + Real.log A) ≤ A * (Real.log 2 + 1 + Real.log s) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ < 4 / Real.pi * s * (Real.log 2 + 1 + Real.log s) := by
        apply mul_lt_mul_of_pos_right _ hL
        rw [div_mul_eq_mul_div, lt_div_iff₀ hpi]; linarith

end MetaMathlibExt.gaussClassNumber_neg_four_mul_lt

namespace MetaMathlibExt

open gaussClassNumber_neg_four_mul_lt

@[expose] public section

/-- **Hua's class number bound.** For every positive integer $D$, the Gauss class number
$h(-4D)$, the number of primitive, reduced, positive definite binary quadratic forms of
discriminant $-4D$, satisfies $h(-4D) < \frac{4}{\pi} \sqrt{D} \log(2e\sqrt{D})$, where $\log$ is
the natural logarithm.

The source quotes this bound from Hua's textbook for the class number of positive binary
quadratic forms; it is read here as the primitive (Gauss) class number.

Source: Kalyan Chakraborty and Meenu Sharma, *A Note on Terai's Conjecture Related to Exponential
Diophantine Equations*, INTEGERS 26 (2026), Article A67, Theorem 3 (`integers-2026-A67-thm-3`). -/
public theorem gaussClassNumber_neg_four_mul_lt (D : ℕ) (hD : 0 < D) :
    (gaussClassNumber (-4 * D) : ℝ) <
      4 / Real.pi * Real.sqrt D * Real.log (2 * Real.exp 1 * Real.sqrt D) := by
  have hA : 3 * Nat.sqrt (4 * D / 3) ^ 2 ≤ 4 * D := by
    have := Nat.sqrt_le' (4 * D / 3)
    omega
  calc (gaussClassNumber (-4 * D) : ℝ) ≤ #(reducedFormsOfDiscriminant (-4 * D)) := by
        unfold gaussClassNumber
        exact_mod_cast card_filter_le _ _
    _ ≤ ∑ a ∈ Ioc 0 (Nat.sqrt (4 * D / 3)), (rootCount D a : ℝ) := by
        exact_mod_cast card_reducedForms_le
    _ ≤ _ := sum_rootCount_le hD.ne' _
    _ < _ := final_estimate hD hA

end

end MetaMathlibExt
