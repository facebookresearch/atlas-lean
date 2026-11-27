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

We bound the relative error of the golden-ratio approximation to the dominant-root term
in the generalized Pell–Lucas formula.
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
  · have hs : (φ ^ ((k : ℝ) / 2)) ^ 2 = φ ^ k := by
      rw [← Real.rpow_natCast (φ ^ ((k : ℝ) / 2)), ← Real.rpow_mul goldenRatio_pos.le]
      norm_num
    rw [hs, one_div_mul_eq_div]
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
  have hδ_factor : δ * (α + φ - 2) = E := by
    change (φ + 1 - α) * (α + φ - 2) = 1 / α ^ (k - 1)
    linear_combination goldenRatio_sq - hres
  have hfactor : 1 ≤ α + φ - 2 := by linarith only [hα₂, one_lt_goldenRatio]
  have hδ : 0 < δ := pos_of_mul_pos_left (hδ_factor ▸ hE) (by linarith)
  have hδE : δ ≤ E := hδ_factor ▸ le_mul_of_one_le_right hδ.le hfactor
  let D : ℝ := (k + 1) * α ^ 2 - 3 * k * α + k - 1
  have hD_eq : D = α ^ 2 - 1 - (k : ℝ) * E := by
    dsimp [D, E]
    linear_combination (k : ℝ) * hres
  have hD : 1 < D := by
    have hkE : (k : ℝ) * E ≤ 5 / 16 := calc
      (k : ℝ) * E ≤ (5 * T) * E := mul_le_mul_of_nonneg_right hkT hE.le
      _ ≤ (5 * T ^ 2) * E := by
        gcongr
        nlinarith only [mul_nonneg (sub_nonneg.mpr hT) hTpos.le]
      _ ≤ 5 / 16 := by nlinarith only [hET]
    rw [hD_eq]
    nlinarith only [hkE, hα₂, sq_nonneg (α - 2)]
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

end MetaMathlibExt
