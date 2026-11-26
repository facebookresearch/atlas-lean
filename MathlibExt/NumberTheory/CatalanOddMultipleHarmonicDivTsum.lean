/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import MathlibExt.NumberTheory.HyperharmonicEulerSums

/-!
# Catalan–odd harmonic sums

The Catalan–odd harmonic sum with denominator $4^n n$ is evaluated in terms of
the Riemann zeta value $\zeta(k + 1)$: the odd harmonic numbers are identified
with generalized hyperharmonic numbers at $r = 1/2$, and duality for
hyperharmonic Euler sums reduces the two resulting sums to the odd zeta sum and
to a single term.
-/

namespace MetaMathlibExt

@[expose] public section

open Real

namespace catalan_oddMultipleHarmonic_div_tsum

private lemma prod_half_add (n : ℕ) :
    (∏ j ∈ Finset.range n, ((1 / 2 : ℂ) + j)) =
      ((2 * n).factorial : ℂ) / ((n.factorial : ℂ) * 4 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have hfact : ((n.factorial : ℂ)) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hA : ((2 * (n + 1)).factorial : ℂ) =
        (2 * n + 2 : ℂ) * (2 * n + 1 : ℂ) * ((2 * n).factorial : ℂ) := by
      have h : (2 * (n + 1)).factorial = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega]
        simp [Nat.factorial_succ]
        ring
      exact_mod_cast h
    have hB : (((n + 1).factorial : ℂ)) = ((n + 1 : ℕ) : ℂ) * ((n.factorial : ℂ)) := by
      exact_mod_cast Nat.factorial_succ n
    rw [hA, hB, pow_succ]
    push_cast
    field_simp
    ring

private lemma oddMultipleHarmonic_eq_sum_range (k n : ℕ) :
    (oddMultipleHarmonic k n : ℂ) =
      ∑ t ∈ (Finset.range n).powersetCard k,
        ∏ j ∈ t, ((1 / 2 : ℂ) + j)⁻¹ := by
  have hIcc : (Finset.Icc 1 n) =
      (Finset.range n).map ⟨fun j => j + 1, Nat.succ_injective⟩ := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range]
    constructor
    · intro h
      refine ⟨x - 1, by omega, ?_⟩
      change x - 1 + 1 = x
      exact Nat.sub_add_cancel h.1
    · rintro ⟨y, hy, rfl⟩; simp at hy ⊢; omega
  unfold oddMultipleHarmonic
  rw [Complex.ofReal_sum, hIcc, Finset.powersetCard_map, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro t _
  rw [Complex.ofReal_prod]
  have hmap : (Finset.mapEmbedding ⟨fun j => j + 1, Nat.succ_injective⟩).toEmbedding t =
      t.map ⟨fun j => j + 1, Nat.succ_injective⟩ := rfl
  rw [hmap, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro j _
  have hem : ((⟨fun j => j + 1, Nat.succ_injective⟩ : ℕ ↪ ℕ) j : ℂ) = (j : ℂ) + 1 := by
    change (((j + 1 : ℕ)) : ℂ) = (j : ℂ) + 1
    push_cast
    ring
  push_cast
  rw [hem]
  ring_nf

private lemma sum_complement (k n : ℕ) (hkn : k ≤ n) :
    (∑ s ∈ (Finset.range n).powersetCard (n - k),
        ∏ j ∈ s, ((1 / 2 : ℂ) + j)) =
      (∏ j ∈ Finset.range n, ((1 / 2 : ℂ) + j)) *
        (∑ t ∈ (Finset.range n).powersetCard k,
          ∏ j ∈ t, ((1 / 2 : ℂ) + j)⁻¹) := by
  set a : ℕ → ℂ := fun j => (1 / 2 : ℂ) + j with ha
  have ha_ne (j : ℕ) : a j ≠ 0 := by
    have h : a j = (((2 * j + 1 : ℕ) : ℂ)) / 2 := by simp [ha]; ring
    rw [h]
    exact div_ne_zero (by exact_mod_cast (by omega : 2 * j + 1 ≠ 0)) (by norm_num)
  have key : ∀ s ∈ (Finset.range n).powersetCard (n - k),
      ∏ j ∈ s, a j =
        (∏ j ∈ Finset.range n, a j) * ∏ j ∈ (Finset.range n) \ s, (a j)⁻¹ := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    have hsd : (∏ j ∈ (Finset.range n) \ s, a j) * (∏ j ∈ s, a j) =
        ∏ j ∈ Finset.range n, a j := Finset.prod_sdiff hs.1
    have hne : (∏ j ∈ (Finset.range n) \ s, a j) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact ha_ne j
    have hdiv : ∏ j ∈ s, a j =
        (∏ j ∈ Finset.range n, a j) / (∏ j ∈ (Finset.range n) \ s, a j) := by
      rw [eq_div_iff hne, mul_comm]
      exact hsd
    rw [hdiv, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  rw [Finset.sum_congr rfl (fun s hs => key s hs)]
  rw [Finset.mul_sum]
  apply Finset.sum_bij (fun s _ => (Finset.range n) \ s)
  · intro s hs
    rw [Finset.mem_powersetCard] at hs ⊢
    constructor
    · exact Finset.sdiff_subset
    · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hs.1, Finset.card_range, hs.2]
      omega
  · intro s₁ hs₁ s₂ hs₂ h
    rw [Finset.mem_powersetCard] at hs₁ hs₂
    have h1 : (Finset.range n) \ ((Finset.range n) \ s₁) = s₁ := by
      rw [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hs₁.1]
    have h2 : (Finset.range n) \ ((Finset.range n) \ s₂) = s₂ := by
      rw [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hs₂.1]
    rw [← h1, ← h2, h]
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    refine ⟨(Finset.range n) \ t, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      constructor
      · exact Finset.sdiff_subset
      · rw [Finset.card_sdiff, Finset.inter_eq_left.mpr ht.1, Finset.card_range, ht.2]
    · rw [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr ht.1]
  · intro s hs
    rfl

end catalan_oddMultipleHarmonic_div_tsum

open catalan_oddMultipleHarmonic_div_tsum in
/-- **Generalized hyperharmonic numbers at order one half.** The value $H_n^{[1/2]}(k)$ is
$\binom{2n}{n} O_n(k)/4^n$. This is Young, *Parametric Euler Sums of Generalized Hyperharmonic
Numbers*, INTEGERS 26 (2026), Article A81, (2.12). -/
lemma generalizedHyperharmonic_half_eq (k n : ℕ) :
    generalizedHyperharmonic n k (1 / 2 : ℂ) =
      ((2 * n).choose n : ℂ) / 4 ^ n * (oddMultipleHarmonic k n : ℂ) := by
  by_cases hkn : k ≤ n
  · unfold generalizedHyperharmonic
    simp only [hkn, ↓reduceIte]
    rw [sum_complement k n hkn, oddMultipleHarmonic_eq_sum_range k n, prod_half_add n]
    have hfact : ((n.factorial : ℂ)) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hnat : (2 * n).choose n * n.factorial * n.factorial = (2 * n).factorial := by
      have h := Nat.choose_mul_factorial_mul_factorial (n := 2 * n) (k := n) (by omega)
      rwa [show 2 * n - n = n by omega] at h
    have hcast : (((2 * n).choose n : ℂ)) * ((n.factorial : ℂ)) * ((n.factorial : ℂ)) =
        ((2 * n).factorial : ℂ) := by exact_mod_cast hnat
    have hscalar : ((2 * n).factorial : ℂ) / ((n.factorial : ℂ) * 4 ^ n) /
        (n.factorial : ℂ) = ((2 * n).choose n : ℂ) / 4 ^ n := by
      field_simp
      linear_combination -hcast
    rw [← div_mul_eq_mul_div, hscalar]
  · have hlt : n < k := Nat.lt_of_not_le hkn
    rw [generalizedHyperharmonic_of_lt hlt, oddMultipleHarmonic_of_lt hlt]
    simp

namespace catalan_oddMultipleHarmonic_div_tsum

private lemma zero_one_eq_one (n : ℕ) : generalizedHyperharmonic n 0 (1 : ℂ) = 1 := by
  have hcard : (Finset.range n).powersetCard n = {Finset.range n} := by
    ext s
    simp only [Finset.mem_powersetCard, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hcard⟩
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
    · intro h
      rw [h]
      exact ⟨Finset.Subset.refl _, Finset.card_range n⟩
  unfold generalizedHyperharmonic
  simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero, hcard, Finset.sum_singleton]
  rw [div_eq_one_iff_eq]
  · have h1 : (∏ j ∈ Finset.range n, ((1 : ℂ) + j)) =
        ∏ j ∈ Finset.range n, ((j + 1 : ℕ) : ℂ) := by
      apply Finset.prod_congr rfl; intro j _; push_cast; ring
    rw [h1, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  · exact_mod_cast n.factorial_ne_zero

private lemma zero_zero_eq_ite (n : ℕ) :
    generalizedHyperharmonic n 0 (0 : ℂ) = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp [generalizedHyperharmonic]
  | succ n =>
    have hcard : (Finset.range (n + 1)).powersetCard (n + 1) = {Finset.range (n + 1)} := by
      ext s
      simp only [Finset.mem_powersetCard, Finset.mem_singleton]
      constructor
      · rintro ⟨hsub, hcard⟩
        exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
      · intro h
        rw [h]
        exact ⟨Finset.Subset.refl _, Finset.card_range _⟩
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    unfold generalizedHyperharmonic
    simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero, hcard, Finset.sum_singleton]
    have hprod : (∏ j ∈ Finset.range (n + 1), ((0 : ℂ) + j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.zero_lt_succ n))
      simp
    rw [hprod, zero_div]

end catalan_oddMultipleHarmonic_div_tsum

/-- **Half-integer reciprocal power sums.** For integers $s > 1$,
$\sum_{n \ge 0} (n + 1/2)^{-s} = (2^s - 1)\zeta(s)$, by separating the even and odd terms
of the zeta series. See Young, INTEGERS 26 (2026), Article A81, Corollaries 2 and 3. -/
lemma hasSum_one_div_nat_add_half_pow (s : ℕ) (hs1 : 1 < s) :
    HasSum (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1 / 2) ^ s)
      ((2 ^ s - 1) * riemannZeta (s : ℂ)) := by
  have hs0 : s ≠ 0 := by omega
  have hsum : Summable (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s)
      ((Real.summable_one_div_nat_pow).mpr hs1)
    intro n
    rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
  have hzeta : HasSum (fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) (riemannZeta ((s : ℕ) : ℂ)) :=
    (Summable.hasSum_iff hsum).mpr (zeta_nat_eq_tsum_of_gt_one hs1).symm
  have heven : HasSum (fun n : ℕ => (1 : ℂ) / ((2 * n : ℕ) : ℂ) ^ s)
      (((2 : ℂ) ^ s)⁻¹ * riemannZeta ((s : ℕ) : ℂ)) := by
    have hpoint : ∀ n : ℕ, (1 : ℂ) / ((2 * n : ℕ) : ℂ) ^ s =
        ((2 : ℂ) ^ s)⁻¹ * ((1 : ℂ) / (n : ℂ) ^ s) := by
      intro n
      cases n with
      | zero => simp [hs0]
      | succ n =>
        have h2 : ((2 : ℂ)) ^ s ≠ 0 := pow_ne_zero _ (by norm_num)
        have h3 : (((n + 1 : ℕ) : ℂ)) ^ s ≠ 0 := by
          apply pow_ne_zero
          exact_mod_cast Nat.succ_ne_zero n
        push_cast
        rw [mul_pow]
        field_simp
    exact (hzeta.mul_left ((2 : ℂ) ^ s)⁻¹).congr_fun hpoint
  have hodd_sum : Summable (fun n : ℕ => (1 : ℂ) / ((2 * n + 1 : ℕ) : ℂ) ^ s) := by
    apply hsum.comp_injective
    exact (add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ))
  have hodd : HasSum (fun n : ℕ => (1 : ℂ) / ((2 * n + 1 : ℕ) : ℂ) ^ s)
      (∑' n : ℕ, (1 : ℂ) / ((2 * n + 1 : ℕ) : ℂ) ^ s) := hodd_sum.hasSum
  have hsplit : riemannZeta ((s : ℕ) : ℂ) =
      ((2 : ℂ) ^ s)⁻¹ * riemannZeta ((s : ℕ) : ℂ) +
        (∑' n : ℕ, (1 : ℂ) / ((2 * n + 1 : ℕ) : ℂ) ^ s) := by
    have h := HasSum.even_add_odd (f := fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s) heven hodd
    exact hzeta.unique h
  have hodd_val : (∑' n : ℕ, (1 : ℂ) / ((2 * n + 1 : ℕ) : ℂ) ^ s) =
      (1 - ((2 : ℂ) ^ s)⁻¹) * riemannZeta ((s : ℕ) : ℂ) := by
    linear_combination -hsplit
  have hhalf : HasSum (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1 / 2) ^ s)
      ((2 : ℂ) ^ s * (∑' n : ℕ, (1 : ℂ) / ((2 * n + 1 : ℕ) : ℂ) ^ s)) := by
    apply (hodd.mul_left ((2 : ℂ) ^ s)).congr_fun
    intro n
    have heq : ((n : ℂ) + 1 / 2) = (((2 * n + 1 : ℕ) : ℂ)) / 2 := by
      push_cast
      ring
    rw [heq, div_pow, one_div_div, div_eq_mul_one_div]
  rw [hodd_val] at hhalf
  simpa only [mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero s (by norm_num :
    (2 : ℂ) ≠ 0)), one_mul, sub_mul] using hhalf

namespace catalan_oddMultipleHarmonic_div_tsum

/-- **Half-integer zeta sum.** For every integer $k > 0$,
$\sum_{n \ge 0} (n + 1/2)^{-(k+1)} = (2^{k+1} - 1)\zeta(k+1)$.
See Young, INTEGERS 26 (2026), Article A81, Corollaries 2 and 3. -/
lemma half_shift_zeta_tsum (k : ℕ) (hk : 0 < k) :
    (∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1 / 2) ^ (k + 1)) =
      (2 ^ (k + 1) - 1) * riemannZeta ((k + 1 : ℕ) : ℂ) := by
  exact (hasSum_one_div_nat_add_half_pow (k + 1) (by omega)).tsum_eq

private lemma eulerSum_zero_one_half (k : ℕ) (hk : 0 < k) :
    hyperharmonicEulerSum 0 (1 : ℂ) ((k : ℤ) + 1) (1 / 2) =
      (2 ^ (k + 1) - 1) * riemannZeta ((k + 1 : ℕ) : ℂ) := by
  have hcongr : (∑' n : ℕ,
      generalizedHyperharmonic n 0 (1 : ℂ) / ((n : ℂ) + 1 / 2) ^ ((k : ℤ) + 1)) =
      (∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1 / 2) ^ (k + 1)) := by
    apply tsum_congr
    intro n
    rw [zero_one_eq_one]
    have hz : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hz, zpow_natCast]
  rw [hyperharmonicEulerSum_eq_tsum, hcongr]
  exact half_shift_zeta_tsum k hk

private lemma eulerSum_zero_zero_half (k : ℕ) :
    hyperharmonicEulerSum 0 (0 : ℂ) ((k : ℤ) + 1) (1 / 2) = (2 : ℂ) ^ (k + 1) := by
  have hf0 : (1 : ℂ) / (1 / 2 : ℂ) ^ ((k : ℤ) + 1) = (2 : ℂ) ^ (k + 1) := by
    have hcast : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, zpow_natCast, one_div, ← inv_pow]
    simp
  rw [hyperharmonicEulerSum_eq_tsum]
  rw [tsum_eq_single 0]
  · simp only [zero_zero_eq_ite, ↓reduceIte, Nat.cast_zero, zero_add]
    exact hf0
  · intro n hn
    simp [zero_zero_eq_ite n, hn]

private lemma term_eq (k n : ℕ) (hk : 0 < k) :
    (((catalan n : ℝ) * oddMultipleHarmonic k n / (4 ^ n * n) : ℝ) : ℂ) =
      generalizedHyperharmonic n k (1 / 2 : ℂ) / ((n : ℂ) + 0) ^ (1 : ℤ) -
        generalizedHyperharmonic n k (1 / 2 : ℂ) / ((n : ℂ) + 1) ^ (1 : ℤ) := by
  cases n with
  | zero =>
    have hH0 : generalizedHyperharmonic 0 k (1 / 2 : ℂ) = 0 :=
      generalizedHyperharmonic_of_lt hk _
    have hO0 : oddMultipleHarmonic k 0 = 0 := oddMultipleHarmonic_of_lt hk
    rw [hH0, hO0]
    simp
  | succ n =>
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hn1 : (((n : ℂ) + 1) + 1 : ℂ) ≠ 0 := by
      have h : (((n : ℂ) + 1) + 1 : ℂ) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [h]
      exact_mod_cast (by omega : n + 2 ≠ 0)
    have hchoose : (((2 * (n + 1)).choose (n + 1) : ℂ)) ≠ 0 := by
      have hpos : 0 < (2 * (n + 1)).choose (n + 1) := Nat.choose_pos (by omega)
      exact_mod_cast hpos.ne'
    have h4 : (4 : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hcat : (((n + 1 : ℕ) : ℂ) + 1) * ((catalan (n + 1) : ℂ)) =
        (((2 * (n + 1)).choose (n + 1) : ℂ)) := by
      have h := succ_mul_catalan_eq_centralBinom (n + 1)
      have h2 : ((n + 1) + 1) * catalan (n + 1) = (n + 1).centralBinom := h
      rw [Nat.centralBinom] at h2
      have hcast : ((((n + 1) + 1 : ℕ) : ℂ)) * ((catalan (n + 1) : ℂ)) =
          (((2 * (n + 1)).choose (n + 1) : ℂ)) := by exact_mod_cast h2
      convert hcast using 2
      push_cast
      ring
    have hO : (oddMultipleHarmonic k (n + 1) : ℂ) =
        generalizedHyperharmonic (n + 1) k (1 / 2 : ℂ) * (4 : ℂ) ^ (n + 1) /
          (((2 * (n + 1)).choose (n + 1) : ℂ)) := by
      rw [generalizedHyperharmonic_half_eq]
      field_simp
    rw [zpow_one, zpow_one, add_zero]
    push_cast
    rw [hO]
    field_simp
    ring_nf
    rw [show (2 + n * 2).choose (1 + n) = (2 * (n + 1)).choose (n + 1) by congr 1 <;> omega,
      ← hcat]
    push_cast
    ring_nf

private lemma dual_values (k : ℕ) (hk : 0 < k) :
    hyperharmonicEulerSum k (1 / 2 : ℂ) 1 0 =
        (2 ^ (k + 1) - 1) * riemannZeta ((k + 1 : ℕ) : ℂ) ∧
      hyperharmonicEulerSum k (1 / 2 : ℂ) 1 1 = (2 : ℂ) ^ (k + 1) ∧
      Summable (fun n : ℕ => generalizedHyperharmonic n k (1 / 2 : ℂ) /
        ((n : ℂ) + 0) ^ (1 : ℤ)) ∧
      Summable (fun n : ℕ => generalizedHyperharmonic n k (1 / 2 : ℂ) /
        ((n : ℂ) + 1) ^ (1 : ℤ)) := by
  have hr : ((1 / 2 : ℂ)).re < (0 : ℕ) + 1 := by
    have h : ((1 / 2 : ℂ)).re = (1 / 2 : ℝ) := by simp
    rw [h]
    norm_num
  have ht1 : ((1 : ℂ)).re < (k : ℕ) + 1 := by
    have h : ((1 : ℂ)).re = (1 : ℝ) := by simp
    rw [h]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have ht0 : ((0 : ℂ)).re < (k : ℕ) + 1 := by
    have h : ((0 : ℂ)).re = (0 : ℝ) := by simp
    rw [h]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    linarith
  obtain ⟨hs1, _, hdual1⟩ := hyperharmonicEulerSum_duality k 0 (1 / 2 : ℂ) 1 hr ht1
  obtain ⟨hs0, _, hdual0⟩ := hyperharmonicEulerSum_duality k 0 (1 / 2 : ℂ) 0 hr ht0
  have hval1' : hyperharmonicEulerSum 0 (1 : ℂ) ((k : ℤ) + 1) (1 - 1 / 2) =
      (2 ^ (k + 1) - 1) * riemannZeta ((k + 1 : ℕ) : ℂ) := by
    convert eulerSum_zero_one_half k hk using 3
    norm_num
  have hval0' : hyperharmonicEulerSum 0 (0 : ℂ) ((k : ℤ) + 1) (1 - 1 / 2) =
      (2 : ℂ) ^ (k + 1) := by
    convert eulerSum_zero_zero_half k using 3
    norm_num
  have hA : hyperharmonicEulerSum k (1 / 2 : ℂ) 1 0 =
      (2 ^ (k + 1) - 1) * riemannZeta ((k + 1 : ℕ) : ℂ) := by
    have h := hdual1.trans hval1'
    convert h using 3 <;> norm_num
  have hB : hyperharmonicEulerSum k (1 / 2 : ℂ) 1 1 = (2 : ℂ) ^ (k + 1) := by
    have h := hdual0.trans hval0'
    convert h using 3 <;> norm_num
  have hsumm0 : Summable (fun n : ℕ => generalizedHyperharmonic n k (1 / 2 : ℂ) /
      ((n : ℂ) + 0) ^ (1 : ℤ)) := by
    apply (summable_nat_add_iff k).mp
    refine hs1.congr fun n => ?_
    rw [show (1 - 1 : ℂ) = 0 by norm_num,
      show (((0 : ℕ) : ℤ) + 1) = 1 by norm_num]
  have hsumm1 : Summable (fun n : ℕ => generalizedHyperharmonic n k (1 / 2 : ℂ) /
      ((n : ℂ) + 1) ^ (1 : ℤ)) := by
    apply (summable_nat_add_iff k).mp
    refine hs0.congr fun n => ?_
    rw [show (1 - 0 : ℂ) = 1 by norm_num,
      show (((0 : ℕ) : ℤ) + 1) = 1 by norm_num]
  exact ⟨hA, hB, hsumm0, hsumm1⟩

end catalan_oddMultipleHarmonic_div_tsum

/-- **Catalan–odd harmonic sum with denominator $4^n n$.** Let $k \ge 1$ be an integer, let $C_n$
denote the $n$-th Catalan number and $O_n(k)$ the depth-$k$ odd harmonic number. Then
$$\sum_{n \ge 1} \frac{C_n O_n(k)}{4^n n} = (2^{k+1} - 1) \zeta(k + 1) - 2^{k+1}.$$

Since $O_n(k) = 0$ for $n < k$, the sum can equally be taken over $n \ge k$.

Source: the denominator $4^n n$ is read from the record's two-row layout ($C_n O_n(k)$ over
$4^n n$).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 5 (`integers-2026-A81-cor-5`). -/
theorem catalan_oddMultipleHarmonic_div_tsum (k : ℕ) (hk : 0 < k) :
    ((∑' n : ℕ, (catalan n : ℝ) * oddMultipleHarmonic k n / (4 ^ n * n) : ℝ) : ℂ) =
      (2 ^ (k + 1) - 1) * riemannZeta (k + 1) - 2 ^ (k + 1) := by
  obtain ⟨hA, hB, hsumm0, hsumm1⟩ :=
    catalan_oddMultipleHarmonic_div_tsum.dual_values k hk
  have htsum0 : (∑' n : ℕ, generalizedHyperharmonic n k (1 / 2 : ℂ) / ((n : ℂ) + 0) ^ (1 : ℤ)) =
      hyperharmonicEulerSum k (1 / 2 : ℂ) 1 0 :=
    (hyperharmonicEulerSum_eq_tsum k (1 / 2 : ℂ) 1 0).symm
  have htsum1 : (∑' n : ℕ, generalizedHyperharmonic n k (1 / 2 : ℂ) / ((n : ℂ) + 1) ^ (1 : ℤ)) =
      hyperharmonicEulerSum k (1 / 2 : ℂ) 1 1 :=
    (hyperharmonicEulerSum_eq_tsum k (1 / 2 : ℂ) 1 1).symm
  have hcast_arg : (((k + 1 : ℕ)) : ℂ) = (k : ℂ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [Complex.ofReal_tsum]
  rw [tsum_congr (fun n => catalan_oddMultipleHarmonic_div_tsum.term_eq k n hk),
    hsumm0.tsum_sub hsumm1, htsum0, htsum1, hA, hB, hcast_arg]

end

end MetaMathlibExt
