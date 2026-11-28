/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Ring.GeomSum

/-!
# The dominant root of the generalized Pell–Lucas polynomial

We bound the errors of the golden-ratio approximations to the dominant-root term and its
coefficient in the generalized Pell–Lucas formula.

## References

* Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to a Power
  of 2*, INTEGERS 25 (2025), Article A67, pp. 1–14, Lemmas 2 and 3.
* Z. Şiar and R. Keskin, *On Perfect Powers in k-Generalized Pell–Lucas Sequence*, Mathematical
  Notes 114 (2023), pp. 936–948, equation (30) and Lemma 13, cited for the two bounds in Lemma 2.
-/

namespace MetaMathlibExt

open Real
open scoped goldenRatio

private theorem kPellLucas_dominantRoot_main_term.root_residual {k : ℕ} (hk : 2 ≤ k)
    {α : ℝ} (hα : 0 < α)
    (hroot : α ^ k = 2 * α ^ (k - 1) + ∑ i ∈ Finset.range (k - 1), α ^ i) :
    2 < α ∧ α ^ 2 - 3 * α + 1 = -(1 / α ^ (k - 1)) := by
  have hpow : α ^ k = α ^ (k - 1) * α := by
    conv_lhs => rw [show k = k - 1 + 1 by omega, pow_succ]
  have hsum : (α - 2) * α ^ (k - 1) = ∑ i ∈ Finset.range (k - 1), α ^ i := by
    rw [hpow] at hroot
    linarith
  have hpos : 0 < (α - 2) * α ^ (k - 1) := by
    rw [hsum]
    exact Finset.sum_pos (fun _ _ ↦ pow_pos hα _) ⟨0, Finset.mem_range.mpr (by omega)⟩
  refine ⟨sub_pos.mp (pos_of_mul_pos_left hpos (by positivity)), ?_⟩
  rw [← neg_div, eq_div_iff (pow_ne_zero _ hα.ne')]
  calc
    (α ^ 2 - 3 * α + 1) * α ^ (k - 1) =
        ((α - 2) * α ^ (k - 1)) * (α - 1) - α ^ (k - 1) := by ring
    _ = -1 := by rw [hsum, geom_sum_mul]; ring

private theorem goldenRatio_half_pow_sq (k : ℕ) : (φ ^ ((k : ℝ) / 2)) ^ 2 = φ ^ k := by
  rw [← Real.rpow_natCast (φ ^ ((k : ℝ) / 2)), ← Real.rpow_mul goldenRatio_pos.le]
  norm_num

private theorem kPellLucas_dominantRoot_main_term.scale_bounds {k : ℕ} (hk : 50 ≤ k)
    {α : ℝ} (hα : 2 < α) :
    (k : ℝ) ≤ 5 * φ ^ ((k : ℝ) / 2) ∧
      (1 / α ^ (k - 1)) * (φ ^ ((k : ℝ) / 2)) ^ 2 ≤ 1 / 16 := by
  have hlower : (3 : ℝ) / 2 < φ := by
    have hs : (2 : ℝ) < √5 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
    change (3 : ℝ) / 2 < (1 + √5) / 2
    linarith
  have hupper : φ ≤ (7 : ℝ) / 4 := by
    have hs : √(5 : ℝ) < 5 / 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    change (1 + √(5 : ℝ)) / 2 ≤ 7 / 4
    linarith
  constructor
  · have hs : (6 : ℝ) / 5 ≤ √φ := Real.le_sqrt_of_sq_le (by nlinarith only [hlower])
    have hp : (6 / 5 : ℝ) ^ k ≤ φ ^ ((k : ℝ) / 2) := by
      rw [show (k : ℝ) / 2 = (1 / 2) * k by ring,
        Real.rpow_mul_natCast goldenRatio_pos.le, ← Real.sqrt_eq_rpow]
      exact pow_le_pow_left₀ (by norm_num) hs k
    have hb := one_add_mul_sub_le_pow (a := (6 : ℝ) / 5) (by norm_num) k
    linarith only [hp, hb]
  · rw [goldenRatio_half_pow_sq, one_div_mul_eq_div]
    calc
      φ ^ k / α ^ (k - 1) ≤ φ ^ k / (2 : ℝ) ^ (k - 1) := by gcongr
      _ = 2 * (φ / 2) ^ k := by
        have hpow : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
          conv_lhs => rw [show k = k - 1 + 1 by omega, pow_succ']
        rw [show (φ / 2) ^ k = φ ^ k / (2 : ℝ) ^ k from div_pow _ _ _, hpow,
          ← mul_div_assoc, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
      _ ≤ 2 * (7 / 8 : ℝ) ^ 50 := by
        gcongr
        exact (pow_le_pow_left₀ (by positivity : 0 ≤ φ / 2)
          (by linarith only [hupper] : φ / 2 ≤ 7 / 8) k).trans
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk)
      _ ≤ 1 / 16 := by norm_num

private theorem dominantRoot_gap {α E : ℝ} (hα₂ : 2 < α) (hE : 0 < E)
    (hres : α ^ 2 - 3 * α + 1 = -E) :
    0 < φ + 1 - α ∧ φ + 1 - α ≤ E := by
  have hfactor : 1 ≤ α + φ - 2 := by linarith only [hα₂, one_lt_goldenRatio]
  have hprod : (φ + 1 - α) * (α + φ - 2) = E := by
    linear_combination goldenRatio_sq - hres
  have hgap := pos_of_mul_pos_left (hprod ▸ hE) (by linarith : 0 ≤ α + φ - 2)
  exact ⟨hgap, hprod ▸ le_mul_of_one_le_right hgap.le hfactor⟩

private theorem dominantRoot_denominator {k : ℕ} {α E T : ℝ} (hα₂ : 2 < α) (hE : 0 < E)
    (hres : α ^ 2 - 3 * α + 1 = -E) (hT : 1 ≤ T) (hkT : (k : ℝ) ≤ 5 * T)
    (hET : E * T ^ 2 ≤ 1 / 16) :
    let D : ℝ := (k + 1) * α ^ 2 - 3 * k * α + k - 1
    D = α ^ 2 - 1 - (k : ℝ) * E ∧ 1 < D := by
  dsimp only
  have hD_eq : (k + 1) * α ^ 2 - 3 * k * α + k - 1 = α ^ 2 - 1 - (k : ℝ) * E := by
    linear_combination (k : ℝ) * hres
  refine ⟨hD_eq, ?_⟩
  have hT_sq : T ≤ T ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hT) (by positivity : 0 ≤ T)]
  have hkE : (k : ℝ) * E ≤ 5 / 16 := calc
    (k : ℝ) * E ≤ (5 * T ^ 2) * E := by
      gcongr
      exact hkT.trans (by gcongr)
    _ ≤ 5 / 16 := by nlinarith only [hET]
  rw [hD_eq]
  nlinarith only [hkE, hα₂, sq_nonneg (α - 2)]

/-- **Main term of the dominant root (Lemma 3).** Let $\varphi$ be the golden ratio, let $k$ and
$n$ be natural numbers with $k \ge 50$ and $n < \varphi^{k/2}$, and let $\alpha > 0$ be a real
number with $\alpha^k = 2\alpha^{k-1} + \sum_{i=0}^{k-2} \alpha^i$. Write
$g_k(z) = (z - 1) / ((k + 1) z^2 - 3kz + k - 1)$. Then there is a real number $\xi$ with
$|\xi| < 1.25 / \varphi^{k/2}$ such that
$(2\alpha - 2) \, g_k(\alpha) \, \alpha^n = \frac{2\varphi^{2n+1}}{\varphi + 2} (1 + \xi)$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 3 (`integers-2025-A67-lem-3`). -/
public theorem kPellLucas_dominantRoot_main_term (k n : ℕ) (hk : 50 ≤ k)
    (hnk : (n : ℝ) < goldenRatio ^ ((k : ℝ) / 2)) (α : ℝ) (hα : 0 < α)
    (hroot : α ^ k = 2 * α ^ (k - 1) + ∑ i ∈ Finset.range (k - 1), α ^ i) :
    ∃ ξ : ℝ, (2 * α - 2) * ((α - 1) / ((k + 1) * α ^ 2 - 3 * k * α + k - 1)) * α ^ n =
        2 * goldenRatio ^ (2 * n + 1) / (goldenRatio + 2) * (1 + ξ) ∧
      |ξ| < 1.25 / goldenRatio ^ ((k : ℝ) / 2) := by
  obtain ⟨hα₂, hres⟩ := kPellLucas_dominantRoot_main_term.root_residual (by omega) hα hroot
  let T : ℝ := φ ^ ((k : ℝ) / 2)
  let E : ℝ := 1 / α ^ (k - 1)
  let δ : ℝ := φ + 1 - α
  change (n : ℝ) < T at hnk
  have hT : 1 ≤ T := Real.one_le_rpow one_lt_goldenRatio.le (by positivity)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hE : 0 < E := by dsimp [E]; positivity
  obtain ⟨hkT, hET⟩ := kPellLucas_dominantRoot_main_term.scale_bounds hk hα₂
  change (k : ℝ) ≤ 5 * T at hkT
  change E * T ^ 2 ≤ 1 / 16 at hET
  have hres' : α ^ 2 - 3 * α + 1 = -E := hres
  obtain ⟨hδ, hδE⟩ : 0 < δ ∧ δ ≤ E := dominantRoot_gap hα₂ hE hres'
  let D : ℝ := (k + 1) * α ^ 2 - 3 * k * α + k - 1
  obtain ⟨hD_eq, hD⟩ : D = α ^ 2 - 1 - (k : ℝ) * E ∧ 1 < D :=
    dominantRoot_denominator hα₂ hE hres' hT hkT hET
  have hDpos : 0 < D := zero_lt_one.trans hD
  -- Normalize the coefficient and the power separately.
  let C : ℝ := (α - 1) ^ 2 * (φ + 2) / (φ * D)
  let q : ℝ := α / (φ + 1)
  have hA : 0 < φ + 1 := by positivity
  have hq₀ : 0 ≤ q := div_nonneg hα.le hA.le
  have hq₁ : q ≤ 1 := (div_le_one hA).2 (sub_nonneg.mp hδ.le)
  have hqerr : 1 - q ≤ E := calc
    1 - q = δ / (φ + 1) := by dsimp [q, δ]; field_simp
    _ ≤ δ := (div_le_iff₀ hA).2 (by
      nlinarith only [mul_nonneg hδ.le goldenRatio_pos.le])
    _ ≤ E := hδE
  have hqpow : |q ^ n - 1| ≤ (n : ℝ) * E := by
    rw [abs_of_nonpos (sub_nonpos.mpr (pow_le_one₀ hq₀ hq₁))]
    have hb := one_add_mul_sub_le_pow (a := q) (by linarith only [hq₀]) n
    have hm := mul_le_mul_of_nonneg_left hqerr (Nat.cast_nonneg n)
    linarith only [hb, hm]
  have hC_eq : C - 1 = ((k : ℝ) * E - 2 * (α - 1) / φ * δ) / D := by
    dsimp [C]
    field_simp [goldenRatio_ne_zero, hDpos.ne']
    rw [hD_eq]
    dsimp [δ]
    ring
  have hC : |C - 1| ≤ ((k : ℝ) + 2) * E := by
    have hφ : 0 < φ := goldenRatio_pos
    have hcoeff₀ : 0 ≤ 2 * (α - 1) / φ :=
      div_nonneg (by linarith only [hα₂]) hφ.le
    have hcoeff₂ : 2 * (α - 1) / φ ≤ 2 := by
      apply (div_le_iff₀ hφ).2
      change 0 < φ + 1 - α at hδ
      linarith only [hδ]
    have hmul := mul_le_mul hcoeff₂ hδE hδ.le (by norm_num : (0 : ℝ) ≤ 2)
    have hmul₀ := mul_nonneg hcoeff₀ hδ.le
    have hkE₀ : 0 ≤ (k : ℝ) * E := by positivity
    have hnum : |(k : ℝ) * E - 2 * (α - 1) / φ * δ| ≤ ((k : ℝ) + 2) * E := by
      rw [abs_le]
      constructor <;> linarith only [hmul, hmul₀, hkE₀, hE]
    rw [hC_eq, abs_div, abs_of_pos hDpos]
    exact (div_le_iff₀ hDpos).2
      (hnum.trans (le_mul_of_one_le_right (by positivity) hD.le))
  refine ⟨C * q ^ n - 1, ?_, ?_⟩
  · change (2 * α - 2) * ((α - 1) / D) * α ^ n = _
    rw [pow_succ, pow_mul, goldenRatio_sq]
    dsimp [C, q]
    rw [div_pow]
    have hφ₂ : 0 < φ + 2 := by positivity
    field_simp [hA.ne', hφ₂.ne', hDpos.ne', goldenRatio_ne_zero]
    ring
  · change |C * q ^ n - 1| < 1.25 / T
    calc
      |C * q ^ n - 1| = |(C - 1) * q ^ n + (q ^ n - 1)| := by
        congr 1
        ring
      _ ≤ |(C - 1) * q ^ n| + |q ^ n - 1| := abs_add_le ..
      _ ≤ ((k : ℝ) + 2) * E + (n : ℝ) * E := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hq₀ n)]
        exact add_le_add ((mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ hq₀ hq₁)).trans hC)
          hqpow
      _ = ((k : ℝ) + 2 + n) * E := by ring
      _ ≤ (8 * T) * E := mul_le_mul_of_nonneg_right (by linarith only [hkT, hnk, hT]) hE.le
      _ < 1.25 / T := (lt_div_iff₀ hTpos).2 (by nlinarith only [hET])

/-- **Golden-ratio approximations at the dominant root (Lemma 2).** Let $\varphi$ be the golden
ratio, let $k$ and $n$ be natural numbers with $k \ge 50$ and $1 < n < \varphi^{k/2}$, and let
$\alpha > 0$ be a real number with $\alpha^k = 2\alpha^{k-1} + \sum_{i=0}^{k-2} \alpha^i$. Write
$g_k(z) = (z - 1) / ((k + 1) z^2 - 3kz + k - 1)$. Then
(i) $|(2\alpha - 2)\alpha^n - 2\varphi^{2n+1}| < 4\varphi^{2n} / \varphi^{k/2}$ and
(ii) $|g_k(\alpha) - g_k(\varphi^2)| < 4k / \varphi^k$.

Source: Mohamadou Bachabi, Bakary Kourouma, and Alain Togbé, *On k-Pell-Lucas Numbers Close to
a Power of 2*, INTEGERS 25 (2025), Article A67, Lemma 2 (`integers-2025-A67-lem-2`). -/
public theorem kPellLucas_dominantRoot_golden_approx (k n : ℕ) (hk : 50 ≤ k) (hn : 1 < n)
    (hnk : (n : ℝ) < goldenRatio ^ ((k : ℝ) / 2)) (α : ℝ) (hα : 0 < α)
    (hroot : α ^ k = 2 * α ^ (k - 1) + ∑ i ∈ Finset.range (k - 1), α ^ i) :
    |(2 * α - 2) * α ^ n - 2 * goldenRatio ^ (2 * n + 1)| <
        4 * goldenRatio ^ (2 * n) / goldenRatio ^ ((k : ℝ) / 2) ∧
      |(α - 1) / ((k + 1) * α ^ 2 - 3 * k * α + k - 1) -
          (goldenRatio ^ 2 - 1) /
            ((k + 1) * (goldenRatio ^ 2) ^ 2 - 3 * k * goldenRatio ^ 2 + k - 1)| <
        4 * k / goldenRatio ^ k := by
  obtain ⟨hα₂, hres⟩ := kPellLucas_dominantRoot_main_term.root_residual (by omega) hα hroot
  let β : ℝ := φ + 1
  let T : ℝ := φ ^ ((k : ℝ) / 2)
  let E : ℝ := 1 / α ^ (k - 1)
  let δ : ℝ := β - α
  change (n : ℝ) < T at hnk
  change α ^ 2 - 3 * α + 1 = -E at hres
  have hT : 1 ≤ T := Real.one_le_rpow one_lt_goldenRatio.le (by positivity)
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hE : 0 < E := by dsimp [E]; positivity
  obtain ⟨hkT, hET⟩ : (k : ℝ) ≤ 5 * T ∧ E * T ^ 2 ≤ 1 / 16 :=
    kPellLucas_dominantRoot_main_term.scale_bounds hk hα₂
  obtain ⟨hδ, hδE⟩ : 0 < δ ∧ δ ≤ E := dominantRoot_gap hα₂ hE hres
  have hαβ : α < β := sub_pos.mp hδ
  have hβ₂ : 2 < β := hα₂.trans hαβ
  have hβ : 0 < β := by linarith only [hβ₂]
  constructor
  · -- Each term in the divided difference of the two powers is at most β^(n - 1).
    have hpow_gap : β ^ n - α ^ n ≤ (n : ℝ) * β ^ (n - 1) * δ := by
      rw [← geom_sum₂_mul]
      apply mul_le_mul_of_nonneg_right _ hδ.le
      calc
        ∑ i ∈ Finset.range n, β ^ i * α ^ (n - 1 - i) ≤
            ∑ _i ∈ Finset.range n, β ^ (n - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i ≤ n - 1 := by
            have := Finset.mem_range.mp hi
            omega
          calc
            β ^ i * α ^ (n - 1 - i) ≤ β ^ i * β ^ (n - 1 - i) := by gcongr
            _ = β ^ (n - 1) := by rw [← pow_add, Nat.add_sub_of_le hi']
        _ = (n : ℝ) * β ^ (n - 1) := by simp [nsmul_eq_mul]
    have hfactor : 0 ≤ 2 * α - 2 := by linarith only [hα₂]
    have hpow_nonneg : 0 ≤ β ^ n - α ^ n := sub_nonneg.mpr (by gcongr)
    have hdiff : 0 ≤ (2 * β - 2) * β ^ n - (2 * α - 2) * α ^ n := by
      apply sub_nonneg.mpr
      gcongr
      linarith only [hβ₂]
    have hpow_step : β ^ (n - 1) * β = β ^ n := by
      rw [← pow_succ, show n - 1 + 1 = n by omega]
    rw [pow_succ, pow_mul, goldenRatio_sq]
    change |(2 * α - 2) * α ^ n - 2 * (β ^ n * φ)| < 4 * β ^ n / T
    have hmain : 2 * (β ^ n * φ) = (2 * β - 2) * β ^ n := by dsimp [β]; ring
    rw [hmain, abs_sub_comm, abs_of_nonneg hdiff]
    calc
      (2 * β - 2) * β ^ n - (2 * α - 2) * α ^ n =
          2 * δ * β ^ n + (2 * α - 2) * (β ^ n - α ^ n) := by dsimp [δ]; ring
      _ ≤ 2 * E * β ^ n + (2 * β) * ((n : ℝ) * β ^ (n - 1) * E) := by
        gcongr
        · linarith only [hαβ]
        · exact hpow_gap.trans (by gcongr)
      _ = 2 * ((n : ℝ) + 1) * E * β ^ n := by
        rw [show (2 * β) * ((n : ℝ) * β ^ (n - 1) * E) =
            (2 * n * E) * (β ^ (n - 1) * β) by ring, hpow_step]
        ring
      _ ≤ (4 * T) * E * β ^ n := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hβ.le n)
        exact mul_le_mul_of_nonneg_right (by linarith only [hnk, hT]) hE.le
      _ < 4 * β ^ n / T := by
        apply (lt_div_iff₀ hTpos).2
        calc
          (4 * T) * E * β ^ n * T = (4 * (E * T ^ 2)) * β ^ n := by ring
          _ < 4 * β ^ n := by gcongr; linarith only [hET]
  · let D : ℝ := (k + 1) * α ^ 2 - 3 * k * α + k - 1
    obtain ⟨hD_eq, hD⟩ : D = α ^ 2 - 1 - (k : ℝ) * E ∧ 1 < D :=
      dominantRoot_denominator hα₂ hE hres hT hkT hET
    have hDpos : 0 < D := zero_lt_one.trans hD
    have hβplus : 0 < β + 1 := by positivity
    have hgβ : (β - 1) / ((k + 1) * β ^ 2 - 3 * k * β + k - 1) = 1 / (β + 1) := by
      have hβres : β ^ 2 - 3 * β + 1 = 0 := by dsimp [β]; linear_combination goldenRatio_sq
      have hden : (k + 1) * β ^ 2 - 3 * k * β + k - 1 = β ^ 2 - 1 := by
        linear_combination (k : ℝ) * hβres
      rw [hden, show β ^ 2 - 1 = (β - 1) * (β + 1) by ring, div_mul_eq_div_div,
        div_self (by linarith only [hβ₂] : β - 1 ≠ 0)]
    -- After cancellation at β, both contributions to the difference are nonnegative.
    have hdiff : (α - 1) / D - 1 / (β + 1) =
        ((α - 1) * δ + (k : ℝ) * E) / (D * (β + 1)) := by
      field_simp [hDpos.ne', hβplus.ne']
      rw [hD_eq]
      dsimp [δ]
      ring
    have hα₁ : 0 ≤ α - 1 := by linarith only [hα₂]
    have hnum : (α - 1) * δ + (k : ℝ) * E ≤ ((k : ℝ) + 2) * E := by
      have hα₃ : α - 1 ≤ 2 := by dsimp [β] at hαβ; linarith only [hαβ, goldenRatio_lt_two]
      have hm := mul_le_mul hα₃ hδE hδ.le (by norm_num : (0 : ℝ) ≤ 2)
      linarith only [hm]
    have hden : 1 ≤ D * (β + 1) := one_le_mul_of_one_le_of_one_le hD.le (by linarith)
    have hEφ : E * φ ^ k ≤ 1 / 16 := by
      rw [← goldenRatio_half_pow_sq]
      exact hET
    have hk₅₀ : (50 : ℝ) ≤ k := by exact_mod_cast hk
    rw [goldenRatio_sq]
    change |(α - 1) / D - (β - 1) / ((k + 1) * β ^ 2 - 3 * k * β + k - 1)| < 4 * k / φ ^ k
    rw [hgβ, hdiff, abs_of_nonneg (by positivity)]
    calc
      ((α - 1) * δ + (k : ℝ) * E) / (D * (β + 1)) ≤ ((k : ℝ) + 2) * E :=
        (div_le_iff₀ (mul_pos hDpos hβplus)).2
          (hnum.trans (le_mul_of_one_le_right (by positivity) hden))
      _ < 4 * k / φ ^ k := by
        apply (lt_div_iff₀ (pow_pos goldenRatio_pos k)).2
        calc
          ((k : ℝ) + 2) * E * φ ^ k = ((k : ℝ) + 2) * (E * φ ^ k) := by ring
          _ ≤ ((k : ℝ) + 2) * (1 / 16) := by gcongr
          _ < 4 * k := by linarith only [hk₅₀]

end MetaMathlibExt
