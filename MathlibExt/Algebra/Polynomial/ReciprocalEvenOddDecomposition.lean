/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.ReciprocalZeroOneFirstOddExponent
import Mathlib.Algebra.Polynomial.Expand

/-! # Even–odd decomposition of reciprocal integer polynomials -/

@[expose] public section

open Polynomial

namespace MathlibExt.Algebra.PalindromicZeroOneWanted

private theorem coeff_evenOdd_sum (a b : ℤ[X]) (l n : ℕ) :
    (a.comp (X ^ 2) + X ^ l * b.comp (X ^ 2)).coeff n =
      (if 2 ∣ n then a.coeff (n / 2) else 0) +
        (if l ≤ n then (if 2 ∣ n - l then b.coeff ((n - l) / 2) else 0) else 0) := by
  rw [coeff_add, coeff_X_pow_mul', ← expand_eq_comp_X_pow, ← expand_eq_comp_X_pow,
    coeff_expand two_pos, coeff_expand two_pos]

private theorem coeff_evenOdd_sum_even (a b : ℤ[X]) {l : ℕ} (hl : Odd l) (i : ℕ) :
    (a.comp (X ^ 2) + X ^ l * b.comp (X ^ 2)).coeff (2 * i) = a.coeff i := by
  obtain ⟨t, ht⟩ := hl
  rw [coeff_evenOdd_sum, ite_eq_left (dvd_mul_right 2 i), Nat.mul_div_cancel_left _ two_pos]
  by_cases hi : l ≤ 2 * i
  · rw [ite_eq_left hi, ite_eq_right (by omega), add_zero]
  · rw [ite_eq_right hi, add_zero]

private theorem coeff_evenOdd_sum_below (a b : ℤ[X]) {l n : ℕ} (hn : Odd n) (h : n < l) :
    (a.comp (X ^ 2) + X ^ l * b.comp (X ^ 2)).coeff n = 0 := by
  obtain ⟨t, ht⟩ := hn
  rw [coeff_evenOdd_sum, ite_eq_right (by omega), ite_eq_right (not_le.mpr h), add_zero]

private theorem coeff_evenOdd_sum_odd (a b : ℤ[X]) {l : ℕ} (hl : Odd l) (i : ℕ) :
    (a.comp (X ^ 2) + X ^ l * b.comp (X ^ 2)).coeff (l + 2 * i) = b.coeff i := by
  obtain ⟨t, ht⟩ := hl
  rw [coeff_evenOdd_sum, ite_eq_right (by omega), ite_eq_left (by omega),
    show l + 2 * i - l = 2 * i by omega, ite_eq_left (dvd_mul_right 2 i),
    Nat.mul_div_cancel_left _ two_pos, zero_add]

private theorem reciprocal_of_coeff_symm {p : ℤ[X]}
    (hsymm : ∀ i ≤ p.natDegree, p.coeff (p.natDegree - i) = p.coeff i) :
    IsReciprocalPoly p := by
  apply (isReciprocalPoly_iff p).mpr
  ext i
  rw [coeff_reverse]
  by_cases hi : i ≤ p.natDegree
  · rw [revAt_le hi, hsymm i hi]
  · rw [revAt_eq_self_of_lt (lt_of_not_ge hi)]

/-- **Even–odd decomposition of a reciprocal polynomial.** Let $h \in \mathbb{Z}[x]$ be an
irreducible reciprocal polynomial of degree $2k$ such that $h \ne g(x^2)$ for every
$g \in \mathbb{Z}[x]$. Then there is exactly one $h_e \in \mathbb{Z}[x]$ for which there is
exactly one $h_o \in \mathbb{Z}[x]$ for which there is exactly one natural number $\ell$
such that $h_e$ and $h_o$ are reciprocal, $\ell$ is odd and positive, $\deg h_e = k$,
$\deg h_o = \max(k - \ell, 0)$, $h(x) = h_e(x^2) + x^\ell h_o(x^2)$ and
$h_e(0)\,h_o(0) \ne 0$.

Since $\ell$ is odd, $h_e(x^2)$ is the even part of $h$, and $h_o(0) \ne 0$ then determines
$\ell$ and $h_o$; so this amounts to a unique triple $(h_e, h_o, \ell)$.

Source: Pradipto Banerjee and Amit Kundu, "On an
Irreducibility Question Concerning Palindromic
Non-cyclotomic 0,1-Polynomials", INTEGERS 24 (2024),
Article A71, Lemma 1. -/
theorem existsUnique_evenOdd_reciprocal (h : ℤ[X]) (k : ℕ)
    (hirr : Irreducible h) (hrec : IsReciprocalPoly h)
    (hdeg : h.natDegree = 2 * k)
    (hnsq : ¬ ∃ g : ℤ[X], h = g.comp (X ^ 2)) :
    ∃! he : ℤ[X], ∃! ho : ℤ[X], ∃! l : ℕ,
      IsReciprocalPoly he ∧ IsReciprocalPoly ho ∧ Odd l ∧ 0 < l ∧
        he.natDegree = k ∧ ho.natDegree = k - l ∧
        h = he.comp (X ^ 2) + X ^ l * ho.comp (X ^ 2) ∧
        he.eval 0 * ho.eval 0 ≠ 0 := by
  classical
  have hsymm (i : ℕ) (hi : i ≤ 2 * k) : h.coeff (2 * k - i) = h.coeff i := by
    rw [← revAt_le hi, ← hdeg, ← coeff_reverse, (isReciprocalPoly_iff h).mp hrec]
  have htop : h.coeff (2 * k) ≠ 0 := by
    rw [← hdeg, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hirr.ne_zero
  have hlarge (i : ℕ) (hi : 2 * k < i) : h.coeff i = 0 :=
    coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hi)
  -- Contracting keeps precisely the even coefficients. Some odd coefficient must survive.
  let he := h.contract 2
  have hce (i : ℕ) : he.coeff i = h.coeff (2 * i) := by
    change (h.contract 2).coeff i = _
    rw [coeff_contract (by decide : 2 ≠ 0), Nat.mul_comm]
  have hex : ∃ i, Odd i ∧ h.coeff i ≠ 0 := by
    by_contra hn
    apply hnsq
    refine ⟨he, ?_⟩
    ext i
    rw [← expand_eq_comp_X_pow]
    rcases Nat.even_or_odd i with ⟨j, hj⟩ | hi
    · rw [show i = 2 * j by omega, coeff_expand_mul' two_pos, hce]
    · obtain ⟨j, hj⟩ := hi
      rw [coeff_expand two_pos, ite_eq_right (by omega)]
      exact not_not.mp (fun hz => hn ⟨i, ⟨j, hj⟩, hz⟩)
  let l := Nat.find hex
  have hl : Odd l := (Nat.find_spec hex).1
  have hcl : h.coeff l ≠ 0 := (Nat.find_spec hex).2
  have hfirst (i : ℕ) (hi : Odd i) (hc : h.coeff i ≠ 0) : l ≤ i :=
    Nat.find_min' hex ⟨hi, hc⟩
  have hbelow (i : ℕ) (hi : Odd i) (hil : i < l) : h.coeff i = 0 := by
    by_contra hc
    exact (not_le.mpr hil) (hfirst i hi hc)
  -- Reflection sends the first nonzero odd coefficient to the last one.
  have hlbound : l ≤ 2 * k := (le_natDegree_of_ne_zero hcl).trans_eq hdeg
  have hmirror : h.coeff (2 * k - l) ≠ 0 := by rwa [hsymm l hlbound]
  have hodd_sub (i : ℕ) (hi : Odd i) (hib : i ≤ 2 * k) : Odd (2 * k - i) := by
    obtain ⟨t, ht⟩ := hi
    exact ⟨k - t - 1, by omega⟩
  have hlk : l ≤ k := by
    have := hfirst _ (hodd_sub l hl hlbound) hmirror
    omega
  have habove (i : ℕ) (hi : Odd i) (hil : 2 * k - l < i) : h.coeff i = 0 := by
    by_cases hib : i ≤ 2 * k
    · rw [← hsymm i hib]
      exact hbelow _ (hodd_sub i hi hib) (by omega)
    · exact hlarge i (lt_of_not_ge hib)
  let ho : ℤ[X] := ∑ i ∈ Finset.range (k - l + 1), monomial i (h.coeff (l + 2 * i))
  have hco (i : ℕ) : ho.coeff i = h.coeff (l + 2 * i) := by
    simp only [ho, finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
      Finset.mem_range]
    split_ifs with hi
    · rfl
    · obtain ⟨t, ht⟩ := hl
      exact (habove _ ⟨t + i, by omega⟩ (by omega)).symm
  have hedeg : he.natDegree = k := by
    apply natDegree_eq_of_le_of_coeff_ne_zero _ (by rwa [hce])
    exact natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by rw [hce, hlarge _ (by omega)]
  have hodeg : ho.natDegree = k - l := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · exact natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
        rw [hco]
        obtain ⟨t, ht⟩ := hl
        exact habove _ ⟨t + i, by omega⟩ (by omega)
    · rwa [hco, show l + 2 * (k - l) = 2 * k - l by omega]
  have herec : IsReciprocalPoly he := by
    apply reciprocal_of_coeff_symm
    rw [hedeg]
    intro i hi
    rw [hce, hce, show 2 * (k - i) = 2 * k - 2 * i by omega, hsymm _ (by omega)]
  have horec : IsReciprocalPoly ho := by
    apply reciprocal_of_coeff_symm
    rw [hodeg]
    intro i hi
    rw [hco, hco, show l + 2 * (k - l - i) = 2 * k - (l + 2 * i) by omega,
      hsymm _ (by omega)]
  have hdecomp : h = he.comp (X ^ 2) + X ^ l * ho.comp (X ^ 2) := by
    ext n
    rcases Nat.even_or_odd n with ⟨i, hi⟩ | hn
    · rw [show n = 2 * i by omega, coeff_evenOdd_sum_even _ _ hl, hce]
    · by_cases hnl : n < l
      · rw [coeff_evenOdd_sum_below _ _ hn hnl, hbelow n hn hnl]
      · obtain ⟨i, hi⟩ := hn
        obtain ⟨j, hj⟩ := hl
        rw [show n = l + 2 * (i - j) by omega, coeff_evenOdd_sum_odd _ _ ⟨j, hj⟩, hco]
  let P (a b : ℤ[X]) (j : ℕ) : Prop :=
    IsReciprocalPoly a ∧ IsReciprocalPoly b ∧ Odd j ∧ 0 < j ∧
      a.natDegree = k ∧ b.natDegree = k - j ∧
      h = a.comp (X ^ 2) + X ^ j * b.comp (X ^ 2) ∧ a.eval 0 * b.eval 0 ≠ 0
  have hP : P he ho l := by
    refine ⟨herec, horec, hl, hl.pos, hedeg, hodeg, hdecomp, ?_⟩
    rw [← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero, hce, hco, mul_zero, add_zero,
      ← hsymm 0 (Nat.zero_le _), Nat.sub_zero]
    exact mul_ne_zero htop hcl
  -- A valid decomposition recovers both parts and the shift from coefficients of `h`.
  have hunique (a b : ℤ[X]) (j : ℕ) (hp : P a b j) : a = he ∧ b = ho ∧ j = l := by
    obtain ⟨-, -, hj, -, -, -, heq, hconst⟩ := hp
    have hae (i : ℕ) : h.coeff (2 * i) = a.coeff i := by
      rw [heq, coeff_evenOdd_sum_even _ _ hj]
    have hbo (i : ℕ) : h.coeff (j + 2 * i) = b.coeff i := by
      rw [heq, coeff_evenOdd_sum_odd _ _ hj]
    have hcj : h.coeff j ≠ 0 := by
      intro hz
      have hb := hbo 0
      rw [mul_zero, add_zero, hz, coeff_zero_eq_eval_zero] at hb
      exact hconst (by rw [← hb, mul_zero])
    have hjl : j ≤ l := by
      by_contra hjl
      exact hcl (by rw [heq, coeff_evenOdd_sum_below _ _ hl (lt_of_not_ge hjl)])
    have hjeq := hjl.antisymm (hfirst j hj hcj)
    refine ⟨?_, ?_, hjeq⟩
    · ext i
      rw [hce, hae]
    · subst j
      ext i
      rw [hco, hbo]
  change ∃! a, ∃! b, ∃! j, P a b j
  refine ⟨he, ⟨ho, ⟨l, hP, fun j hj => (hunique he ho j hj).2.2⟩, ?_⟩, ?_⟩
  · rintro b ⟨j, hj, -⟩
    exact (hunique he b j hj).2.1
  · rintro a ⟨b, ⟨j, hj, -⟩, -⟩
    exact (hunique a b j hj).1

end MathlibExt.Algebra.PalindromicZeroOneWanted
