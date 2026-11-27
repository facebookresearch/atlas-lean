/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Riemann-sum bound for Farey partitions

The difference between the sum of the Farey interval weights and the integral of $2/t$
is bounded by the mesh times the total interval length times the inverse square of the
left endpoint.
-/

namespace MetaMathlibExt

private theorem intervalIntegrable_two_div_of_pos {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    IntervalIntegrable (fun t : ℝ => 2 / t) MeasureTheory.volume x y := by
  apply ContinuousOn.intervalIntegrable_of_Icc hxy
  exact continuousOn_const.div continuousOn_id fun _ ht => (hx.trans_le ht.1).ne'

private theorem abs_trapezoid_two_div_sub_integral_le {l x y : ℝ}
    (hl : 0 < l) (hlx : l ≤ x) (hxy : x ≤ y) :
    |(y - x) * (1 / x + 1 / y) - ∫ t in x..y, 2 / t| ≤ (y - x) * (y - x) / l ^ 2 := by
  have hx := hl.trans_le hlx
  have hy := hx.trans_le hxy
  have hint := intervalIntegrable_two_div_of_pos hx hxy
  -- Bound the integral between the right and left endpoint rectangles.
  have hlower : (y - x) * (2 / y) ≤ ∫ t in x..y, 2 / t := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using
      intervalIntegral.integral_mono_on hxy intervalIntegrable_const hint fun t ht =>
        div_le_div_of_nonneg_left zero_le_two (hx.trans_le ht.1) ht.2
  have hupper : (∫ t in x..y, 2 / t) ≤ (y - x) * (2 / x) := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using
      intervalIntegral.integral_mono_on hxy hint intervalIntegrable_const fun t ht =>
        div_le_div_of_nonneg_left zero_le_two hx ht.1
  have hgap : (y - x) * (1 / x - 1 / y) ≤ (y - x) * (y - x) / l ^ 2 := by
    rw [div_sub_div _ _ hx.ne' hy.ne', one_mul, mul_one, ← mul_div_assoc]
    exact div_le_div_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hxy))
      (by positivity) (by rw [sq]; exact mul_le_mul hlx (hlx.trans hxy) hl.le hx.le)
  refine abs_le.mpr ⟨(neg_le_neg hgap).trans ?_, ?_⟩
  · calc
      -((y - x) * (1 / x - 1 / y)) = (y - x) * (1 / x + 1 / y) - (y - x) * (2 / x) := by ring
      _ ≤ _ := sub_le_sub_left hupper _
  · calc
      _ ≤ (y - x) * (1 / x + 1 / y) - (y - x) * (2 / y) := sub_le_sub_left hlower _
      _ = (y - x) * (1 / x - 1 / y) := by ring
      _ ≤ _ := hgap

/-- **Riemann-sum bound for Farey partitions.** Let $a, b, c, d, m$ be natural numbers with
$a > 0$, $bc = ad + 1$, $c \le d$ and $m \ge 2$. Let $A, B : \mathbb{N} \to \mathbb{N}$ satisfy
$A(1) = a$, $B(1) = b$, $A(m) = c$, $B(m) = d$ and $B(k) A(k+1) = A(k) B(k+1) + 1$ for
$1 \le k \le m - 1$, and let $\delta$ be a real number with $1/(B(k) B(k+1)) \le \delta$ for
$1 \le k \le m - 1$. Then
$$
\left| \sum_{k=1}^{m-1} \frac{A(k) B(k+1) + B(k) A(k+1)}{A(k) B(k) A(k+1) B(k+1)} -
\int_{a/b}^{c/d} \frac{2}{t} \, dt \right| \le
\left( \frac{c}{d} - \frac{a}{b} \right) \frac{b^2}{a^2} \, \delta.
$$

In words: the fractions $A(k)/B(k)$ cut the Farey interval $[a/b, c/d]$ into consecutive Farey
intervals, the $k$-th summand is $f([A(k)/B(k), A(k+1)/B(k+1)])$ with
$f([x/y, z/w]) = (xw + yz)/(xyzw)$, and $\delta$ stands for any upper bound of
$\max_k 1/(B(k) B(k+1))$.

Source: Nikita Kalinin, *A Short Telescoping Proof of Hata's Formula for the
Euler-Mascheroni Constant*, INTEGERS 25 (2025), Article A90, Lemma 2, inequality (2). -/
public theorem abs_sum_farey_partition_sub_integral_le {a b c d m : ℕ} {A B : ℕ → ℕ}
    {δ : ℝ} (ha : 0 < a) (hF : b * c = a * d + 1) (hcd : c ≤ d) (hm : 2 ≤ m)
    (hA1 : A 1 = a) (hB1 : B 1 = b) (hAm : A m = c) (hBm : B m = d)
    (hpart : ∀ k ∈ Finset.Icc 1 (m - 1), B k * A (k + 1) = A k * B (k + 1) + 1)
    (hδ : ∀ k ∈ Finset.Icc 1 (m - 1), (1 : ℝ) / (B k * B (k + 1)) ≤ δ) :
    |∑ k ∈ Finset.Icc 1 (m - 1),
        ((A k * B (k + 1) + B k * A (k + 1) : ℝ) / (A k * B k * A (k + 1) * B (k + 1))) -
      ∫ t in (a / b : ℝ)..(c / d : ℝ), 2 / t| ≤
      ((c : ℝ) / d - a / b) * ((b : ℝ) ^ 2 / a ^ 2) * δ := by
  have hm₁ : 1 ≤ m := by omega
  have hindex : Finset.Ico 1 m = Finset.Icc 1 (m - 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Nat.sub_add_cancel hm₁]
  rw [← hindex] at hpart hδ ⊢
  let x (k : ℕ) : ℝ := A k / B k
  let f (k : ℕ) : ℝ :=
    (A k * B (k + 1) + B k * A (k + 1)) / (A k * B k * A (k + 1) * B (k + 1))
  have hx1 : x 1 = (a : ℝ) / b := by simp only [x, hA1, hB1]
  have hxm : x m = (c : ℝ) / d := by simp only [x, hAm, hBm]
  have hpart_pos (k : ℕ) (hk : k ∈ Finset.Ico 1 m) : 0 < B k * A (k + 1) :=
    hpart k hk ▸ Nat.succ_pos _
  have hB (k : ℕ) (hk : k ∈ Set.Icc 1 m) : (0 : ℝ) < B k := by
    apply Nat.cast_pos.mpr
    rcases hk.2.eq_or_lt with rfl | hkm
    · have hbc : 0 < b * c := hF ▸ Nat.succ_pos _
      rw [hBm]
      exact (Nat.pos_of_mul_pos_left hbc).trans_le hcd
    · exact Nat.pos_of_mul_pos_right (hpart_pos k (Finset.mem_Ico.mpr ⟨hk.1, hkm⟩))
  have hA (k : ℕ) (hk : k ∈ Set.Icc 1 m) : (0 : ℝ) < A k := by
    apply Nat.cast_pos.mpr
    rcases hk.1.eq_or_lt with h | h
    · rwa [← h, hA1]
    · have hkm : k ≤ m := hk.2
      have hpred : k - 1 ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      simpa only [Nat.sub_add_cancel (show 1 ≤ k from hk.1)] using
        Nat.pos_of_mul_pos_left (hpart_pos (k - 1) hpred)
  have hverts (k : ℕ) (hk : k ∈ Finset.Ico 1 m) :
      k ∈ Set.Icc 1 m ∧ k + 1 ∈ Set.Icc 1 m := by
    obtain ⟨hk1, hkm⟩ := Finset.mem_Ico.mp hk
    exact ⟨⟨hk1, hkm.le⟩, ⟨by omega, hkm⟩⟩
  have hwidth (k : ℕ) (hk : k ∈ Finset.Ico 1 m) :
      x (k + 1) - x k = (1 : ℝ) / (B k * B (k + 1)) := by
    obtain ⟨hleft, hright⟩ := hverts k hk
    have hdet : (B k * A (k + 1) : ℝ) = A k * B (k + 1) + 1 := by
      exact_mod_cast hpart k hk
    dsimp only [x]
    rw [div_sub_div _ _ (hB _ hright).ne' (hB _ hleft).ne', mul_comm (A (k + 1) : ℝ),
      mul_comm (B (k + 1) : ℝ) (A k : ℝ), hdet, add_sub_cancel_left, mul_comm (B (k + 1) : ℝ)]
  have hmono : MonotoneOn x (Set.Icc 1 m) := by
    apply monotoneOn_of_le_succ (by infer_instance)
    intro k _ hk hk'
    have hki : k ∈ Finset.Ico 1 m := Finset.mem_Ico.mpr ⟨hk.1, hk'.2⟩
    apply sub_nonneg.mp
    rw [show Order.succ k = k + 1 from rfl, hwidth k hki]
    exact div_nonneg zero_le_one (mul_nonneg (hB _ hk).le (hB _ hk').le)
  have hfirst : 1 ∈ Set.Icc 1 m := ⟨le_rfl, hm₁⟩
  have hxpos : 0 < x 1 := div_pos (hA _ hfirst) (hB _ hfirst)
  have hleft_le (k : ℕ) (hk : k ∈ Set.Icc 1 m) : x 1 ≤ x k := hmono hfirst hk hk.1
  have hscale : 1 / (x 1) ^ 2 = (b : ℝ) ^ 2 / a ^ 2 := by
    rw [hx1, div_pow, one_div, inv_div]
  have hlocal (k : ℕ) (hk : k ∈ Finset.Ico 1 m) :
      |f k - ∫ t in x k..x (k + 1), 2 / t| ≤
        (x (k + 1) - x k) * ((b : ℝ) ^ 2 / a ^ 2) * δ := by
    obtain ⟨hleft, hright⟩ := hverts k hk
    have hle := hmono hleft hright (Nat.le_succ k)
    have hweight : f k = (x (k + 1) - x k) * (1 / x k + 1 / x (k + 1)) := by
      have hAk := hA k hleft
      have hAk' := hA (k + 1) hright
      have hBk := hB k hleft
      have hBk' := hB (k + 1) hright
      rw [hwidth k hk]
      dsimp only [f, x]
      field_simp
      ring
    calc
      _ ≤ (x (k + 1) - x k) * (x (k + 1) - x k) / (x 1) ^ 2 := by
        rw [hweight]
        exact abs_trapezoid_two_div_sub_integral_le hxpos (hleft_le k hleft) hle
      _ = (x (k + 1) - x k) * ((b : ℝ) ^ 2 / a ^ 2) * (x (k + 1) - x k) := by
        rw [← hscale]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by rw [hwidth k hk]; exact hδ k hk)
        (mul_nonneg (sub_nonneg.mpr hle) (by positivity))
  have hintegral : (∑ k ∈ Finset.Ico 1 m, ∫ t in x k..x (k + 1), 2 / t) =
      ∫ t in x 1..x m, 2 / t := by
    apply intervalIntegral.sum_integral_adjacent_intervals_Ico hm₁
    intro k hk
    obtain ⟨hleft, hright⟩ := hverts k (Finset.mem_Ico.mpr hk)
    exact intervalIntegrable_two_div_of_pos (hxpos.trans_le (hleft_le k hleft))
      (hmono hleft hright (Nat.le_succ k))
  change |(∑ k ∈ Finset.Ico 1 m, f k) - ∫ t in (a / b : ℝ)..(c / d : ℝ), 2 / t| ≤ _
  rw [← hx1, ← hxm, ← hintegral, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.Ico 1 m, |f k - ∫ t in x k..x (k + 1), 2 / t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico 1 m, (x (k + 1) - x k) * ((b : ℝ) ^ 2 / a ^ 2) * δ :=
      Finset.sum_le_sum hlocal
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_Ico_sub x hm₁]

end MetaMathlibExt
