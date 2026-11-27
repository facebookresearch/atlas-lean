/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.KFull
public import MathlibExt.NumberTheory.PowerFree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import MathlibExt.NumberTheory.PrimeCounting.AverageOmegaHFree
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Set.Card

/-!
# Odd and even power-free numbers

The ratio of odd to even `l`-free integers tends to `2 ^ l / (2 ^ l - 2)` for `2 ≤ l`.
-/

namespace MetaMathlibExt

open Filter Topology

namespace PowerFreeParity

private def free (l : ℕ) : Set ℕ := {n | n.IsPowerFree l}

private def odds (l : ℕ) : Set ℕ := free l ∩ {n | Odd n}

private def evens (l : ℕ) : Set ℕ := free l ∩ {n | Even n}

private noncomputable def count (s : Set ℕ) (x : ℝ) : ℝ :=
  (Set.Iic ⌊x⌋₊ ∩ s).ncard

private lemma count_union {s t : Set ℕ} (h : Disjoint s t) (x : ℝ) :
    count (s ∪ t) x = count s x + count t x := by
  simp only [count, Set.inter_union_distrib_left,
    Set.ncard_union_eq (h.mono Set.inter_subset_right Set.inter_subset_right)
      ((Set.finite_Iic ⌊x⌋₊).inter_of_left _) ((Set.finite_Iic ⌊x⌋₊).inter_of_left _),
    Nat.cast_add]

private lemma count_image (s : Set ℕ) {d : ℕ} (hd : 0 < d) {x : ℝ} (hx : 0 ≤ x) :
    count ((d * ·) '' s) x = count s (x / d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have heq : Set.Iic ⌊x⌋₊ ∩ ((d * ·) '' s) =
      (d * ·) '' (Set.Iic ⌊x / d⌋₊ ∩ s) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_image, Nat.le_floor_iff hx,
      Nat.le_floor_iff (div_nonneg hx hd'.le), le_div_iff₀ hd']
    constructor
    · rintro ⟨hle, m, hm, rfl⟩
      exact ⟨m, ⟨by simpa [Nat.cast_mul, mul_comm] using hle, hm⟩, rfl⟩
    · rintro ⟨m, ⟨hle, hm⟩, rfl⟩
      exact ⟨by simpa [Nat.cast_mul, mul_comm] using hle, m, hm, rfl⟩
  simp only [count, heq, Set.ncard_image_of_injective _ (mul_right_injective₀ hd.ne')]

private lemma count_split (l : ℕ) (x : ℝ) :
    count (free l) x = count (odds l) x + count (evens l) x := by
  have heq : free l = odds l ∪ evens l := by
    ext n
    change n.IsPowerFree l ↔ (_ ∧ Odd n) ∨ (_ ∧ Even n)
    rw [← and_or_left]
    simp [← Nat.not_odd_iff_even, free, or_not]
  rw [heq, count_union]
  exact Set.disjoint_left.mpr fun n ho he => Nat.not_odd_iff_even.mpr he.2 ho.2

-- Doubling preserves power-freeness unless it introduces the forbidden power of two.
private lemma double_free_iff {l m : ℕ} (hm : m.IsPowerFree l) :
    (2 * m).IsPowerFree l ↔ ¬ 2 ^ l ∣ 2 * m := by
  refine ⟨fun h => h.not_dvd Nat.prime_two, fun h => ⟨hm.two_le, by grind [hm.pos], ?_⟩⟩
  intro p hp hd
  rcases eq_or_ne p 2 with rfl | hne
  · exact h hd
  · have hc := ((Nat.coprime_primes hp Nat.prime_two).mpr hne).pow_left l
    exact hm.not_dvd hp (hc.dvd_of_dvd_mul_left hd)

private lemma free_mul_pow_two {k m : ℕ} (hm : m.IsPowerFree (k + 1)) (ho : Odd m) :
    (2 ^ k * m).IsPowerFree (k + 1) := by
  refine ⟨hm.two_le, Nat.mul_pos (by positivity) hm.pos, fun p hp hd => ?_⟩
  rcases eq_or_ne p 2 with rfl | hne
  · rw [pow_succ, Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ k)] at hd
    exact Nat.not_even_iff_odd.mpr ho (even_iff_two_dvd.mpr hd)
  · have hc := ((Nat.coprime_primes hp Nat.prime_two).mpr hne).pow (k + 1) k
    exact hm.not_dvd hp (hc.dvd_of_dvd_mul_left hd)

private lemma double_image (k : ℕ) :
    (2 * ·) '' free (k + 1) =
      evens (k + 1) ∪ (2 ^ (k + 1) * ·) '' odds (k + 1) := by
  ext n
  constructor
  · rintro ⟨m, hm, rfl⟩
    change m.IsPowerFree (k + 1) at hm
    by_cases hd : 2 ^ (k + 1) ∣ 2 * m
    · right
      obtain ⟨u, hu⟩ := hd
      have hm' : m = 2 ^ k * u := by
        simpa [pow_succ', Nat.mul_assoc] using hu
      refine ⟨u, ⟨hm.of_dvd ⟨2 ^ k, hm'.trans (mul_comm ..)⟩, ?_⟩, hu.symm⟩
      apply Nat.not_even_iff_odd.mp
      intro he
      apply hm.not_dvd Nat.prime_two
      rw [hm', pow_succ]
      exact Nat.mul_dvd_mul_left _ (even_iff_two_dvd.mp he)
    · exact Or.inl ⟨(double_free_iff hm).mpr hd, even_iff_two_dvd.mpr (dvd_mul_right ..)⟩
  · rintro (⟨hn, he⟩ | ⟨u, ⟨hu, ho⟩, rfl⟩)
    · obtain ⟨m, rfl⟩ := even_iff_two_dvd.mp he
      exact ⟨m, hn.of_dvd (dvd_mul_left ..), rfl⟩
    · exact ⟨2 ^ k * u, free_mul_pow_two hu ho, by simp [pow_succ', Nat.mul_assoc]⟩

private lemma odd_recurrence {l : ℕ} (hl : 2 ≤ l) {x : ℝ} (hx : 0 ≤ x) :
    count (odds l) x = count (free l) x - count (free l) (x / 2) +
      count (odds l) (x / 2 ^ l) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  have hd : Disjoint (evens (k + 1)) ((2 ^ (k + 1) * ·) '' odds (k + 1)) := by
    apply Set.disjoint_left.mpr
    rintro n hn ⟨u, _, rfl⟩
    exact hn.1.not_dvd Nat.prime_two (dvd_mul_right ..)
  have h := congrArg (fun s => count s x) (double_image k)
  rw [count_image _ (by decide) hx, count_union hd, count_image _ (by positivity) hx] at h
  push_cast at h
  linarith [count_split (k + 1) x]

private lemma total_error {l : ℕ} (hl : 2 ≤ l) {x : ℝ} (hx : 0 ≤ x) :
    |count (free l) x - (riemannZeta (l : ℂ)).re⁻¹ * x| ≤ 4 * √x := by
  classical
  have heq : Set.Iic ⌊x⌋₊ ∩ free l = ↑((Finset.Icc 1 ⌊x⌋₊).filter
      (fun n : ℕ => ∀ p ∈ n.primeFactors, n.factorization p < l)) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_Iic, free, Set.mem_ofPred_eq, Nat.isPowerFree_iff,
      Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hle, _, hn, h⟩
      refine ⟨⟨hn, hle⟩, fun p hp => ?_⟩
      have hp' := Nat.prime_of_mem_primeFactors hp
      exact lt_of_not_ge fun hd => h p hp' ((hp'.pow_dvd_iff_le_factorization hn.ne').mpr hd)
    · rintro ⟨⟨hn, hle⟩, h⟩
      refine ⟨hle, hl, hn, fun p hp hd => ?_⟩
      have hpn : p ∣ n := (dvd_pow_self p (by omega : l ≠ 0)).trans hd
      exact (h p (Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩)).not_ge
        ((hp.pow_dvd_iff_le_factorization (by omega)).mp hd)
  simpa only [count, heq, Set.ncard_coe_finset, div_eq_inv_mul] using
    (abs_card_hfree_sub_le l hl x hx)

-- The error at x / 2^l contributes at most half the square-root error budget at x.
private lemma odd_error {l : ℕ} (hl : 2 ≤ l) {c a : ℝ} (ha : 0 ≤ a)
    (hmain : a = c / 2 + a / 2 ^ l)
    (ht : ∀ x : ℝ, 0 ≤ x → |count (free l) x - c * x| ≤ 4 * √x)
    (x : ℝ) (hx : 0 ≤ x) :
    |count (odds l) x - a * x| ≤ (16 + a) * √x := by
  have hq : (4 : ℝ) ≤ 2 ^ l := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
         _ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl
  generalize hN : ⌊x⌋₊ = N
  induction N using Nat.strong_induction_on generalizing x with
  | ind N ih =>
    by_cases hsmall : x < 1
    · have hf := Nat.floor_eq_zero.mpr hsmall
      have hempty : Set.Iic ⌊x⌋₊ ∩ odds l = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro n ⟨hn, hfree, _⟩
        have hpos := hfree.pos
        change n ≤ ⌊x⌋₊ at hn
        omega
      have hxs : x ≤ √x := by
        calc x = √(x ^ 2) := (Real.sqrt_sq hx).symm
             _ ≤ √x := Real.sqrt_le_sqrt (by nlinarith [mul_nonneg hx (sub_nonneg.mpr hsmall.le)])
      simp only [count, hempty, Set.ncard_empty, Nat.cast_zero, zero_sub, abs_neg,
        abs_of_nonneg (mul_nonneg ha hx)]
      linarith [mul_le_mul_of_nonneg_left hxs ha, Real.sqrt_nonneg x]
    · have hN1 : 1 ≤ (N : ℝ) := by
        exact_mod_cast (show 0 < N by rwa [← hN, Nat.floor_pos, ← not_lt])
      have hlt : ⌊x / 2 ^ l⌋₊ < N := by
        rw [Nat.floor_lt (by positivity), div_lt_iff₀ (by positivity)]
        have hupper := Nat.lt_floor_add_one x
        rw [hN] at hupper
        nlinarith [mul_nonneg (by linarith : 0 ≤ (N : ℝ)) (sub_nonneg.mpr hq)]
      have hr := ih _ hlt (x / 2 ^ l) (by positivity) rfl
      have hhalf : √(x / 2) ≤ √x := Real.sqrt_le_sqrt (by linarith)
      have hscale : √(x / 2 ^ l) ≤ √x / 2 := by
        calc √(x / 2 ^ l) ≤ √(x / 4) := by gcongr
             _ = √x / 2 := by
               rw [Real.sqrt_div hx, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hid : a * x = c * x - c * (x / 2) + a * (x / 2 ^ l) := by
        linear_combination x * hmain
      rw [odd_recurrence hl hx, hid]
      have h₁ := ht x hx
      have h₂ := ht (x / 2) (by positivity)
      rw [abs_le] at hr h₁ h₂ ⊢
      have h₃ := mul_le_mul_of_nonneg_left hscale (by linarith : 0 ≤ 16 + a)
      constructor <;> linarith [mul_nonneg ha (Real.sqrt_nonneg x)]

private lemma density_of_error (s : Set ℕ) {c C : ℝ}
    (h : ∀ x : ℝ, 0 ≤ x → |count s x - c * x| ≤ C * √x) :
    Tendsto (fun N : ℕ => count s N / N) atTop (𝓝 c) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (g := fun N : ℕ => C / √(N : ℝ))
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hs := Real.sqrt_pos.mpr hn
    rw [Real.norm_eq_abs, div_sub' hn.ne', mul_comm (N : ℝ) c, abs_div, abs_of_pos hn]
    rw [div_le_div_iff₀ hn hs]
    calc |count s N - c * N| * √(N : ℝ) ≤ C * √(N : ℝ) * √(N : ℝ) := by
           gcongr
           exact h N hn.le
         _ = C * N := by rw [mul_assoc, Real.mul_self_sqrt hn.le]
  · exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

private lemma count_parity (l N : ℕ) (P : ℕ → Prop) :
    count (free l ∩ {n | P n}) N =
      ({n : ℕ | n ≤ N ∧ Nat.IsKFull 1 n ∧ n.IsPowerFree l ∧ P n}.ncard : ℝ) := by
  simp only [count, Nat.floor_natCast]
  congr 2
  ext n
  change (n ≤ N ∧ n.IsPowerFree l ∧ P n) ↔ _
  simp only [Set.mem_ofPred_eq, Nat.isKFull_k_eq_one]
  exact ⟨fun ⟨hn, hf, hp⟩ => ⟨hn, hf.pos.ne', hf, hp⟩, fun ⟨hn, _, hf, hp⟩ => ⟨hn, hf, hp⟩⟩

end PowerFreeParity

open PowerFreeParity

/-- **Odd-to-even ratio of $l$-free numbers.** Let $l \ge 2$. For a natural number $N$ let $O(N)$
and $E(N)$ be the numbers of odd and of even $l$-free positive integers $n \le N$. Then
$O(N)/E(N) \to 2^l/(2^l - 2)$ as $N \to \infty$.

This is the case $k = 1$ of the odd-to-even ratio for $k$-full, $l$-free numbers, since every
positive integer is $1$-full.

Source: Sunanta Srisopha and Teerapat Srichan, *The Odd/Even Dichotomy for the Set of
Numbers That Are Both k-Full and l-Free*, INTEGERS 24 (2024), Article A106, Corollary 1
(`integers-2024-A106-cor-1`). -/
public theorem tendsto_card_odd_lFree_div_card_even_lFree {l : ℕ} (hl : 2 ≤ l) :
    Tendsto (fun N : ℕ =>
        ({n : ℕ | n ≤ N ∧ Nat.IsKFull 1 n ∧ n.IsPowerFree l ∧
            Odd n}.ncard : ℝ) /
          {n : ℕ | n ≤ N ∧ Nat.IsKFull 1 n ∧ n.IsPowerFree l ∧
            Even n}.ncard)
      atTop (𝓝 ((2 : ℝ) ^ l / ((2 : ℝ) ^ l - 2))) := by
  let c := (riemannZeta (l : ℂ)).re⁻¹
  let q := (2 : ℝ) ^ l
  let a := c * q / (2 * (q - 1))
  have hc : 0 < c := by
    apply inv_pos.mpr
    have hl' : 1 < (l : ℝ) := by exact_mod_cast (show 1 < l by omega)
    simpa using riemannZeta_re_pos_of_one_lt hl'
  have hq : 4 ≤ q := by
    exact (by norm_num : (4 : ℝ) ≤ 2 ^ 2).trans (pow_le_pow_right₀ (by norm_num) hl)
  have hq₀ : q ≠ 0 := by linarith
  have hq₁ : 0 < q - 1 := by linarith
  have ha : 0 < a := div_pos (mul_pos hc (by linarith)) (by positivity)
  have hea : 0 < c - a := by
    apply sub_pos.mpr
    change c * q / (2 * (q - 1)) < c
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hc (by linarith : 0 < q - 2)]
  have hmain : a = c / 2 + a / q := by
    dsimp only [a]
    field_simp
    ring
  have ht := density_of_error (free l) (c := c) (fun _ hx => total_error hl hx)
  have ho := density_of_error (odds l) (fun x hx =>
    odd_error hl ha.le hmain (fun _ hy => total_error hl hy) x hx)
  have he : Tendsto (fun N : ℕ => count (evens l) N / N) atTop (𝓝 (c - a)) :=
    (ht.sub ho).congr fun N => by
      rw [count_split l (N : ℝ)]
      simp only [add_div, add_sub_cancel_left]
  have hratio : a / (c - a) = q / (q - 2) := by
    dsimp only [a]
    field_simp
    ring
  rw [← hratio]
  apply (ho.div he hea.ne').congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hn, odds, evens, count_parity, count_parity]

end MetaMathlibExt
