/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanSummability
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Difference of products of Ramanujan theta functions

For parameters with a common product, `ramanujanTheta_mul_sub_mul_neg` factors the
difference of the two theta products by reindexing the terms with odd index sum.
-/

namespace MetaMathlibExt

namespace RamanujanThetaProduct

private def triangular (n : ℤ) : ℤ := n * (n - 1) / 2

private lemma twice_triangular (n : ℤ) : 2 * triangular n = n * (n - 1) :=
  Int.mul_ediv_cancel' (Int.even_mul_pred_self n).two_dvd

private lemma triangular_nonneg (n : ℤ) : 0 ≤ triangular n := by
  apply Int.ediv_nonneg _ (by decide)
  rcases le_or_gt n 0 with h | h
  · exact mul_nonneg_of_nonpos_of_nonpos h (by omega)
  · exact mul_nonneg h.le (by omega)

-- Using the common product as a base leaves only one quadratic exponent per term.
private lemma term_eq {a b : ℂ} (ha : a ≠ 0) (n : ℤ) :
    ramanujanThetaTerm a b n = a ^ n * (a * b) ^ triangular n := by
  have hplus : n * (n + 1) / 2 = triangular (n + 1) := by
    simp [triangular, mul_comm]
  have hsucc : triangular (n + 1) = n + triangular n := by
    linarith [twice_triangular (n + 1), twice_triangular n]
  unfold ramanujanThetaTerm
  rw [hplus]
  change a ^ (triangular (n + 1)).toNat * b ^ (triangular n).toNat = _
  rw [← zpow_natCast, ← zpow_natCast b, Int.toNat_of_nonneg (triangular_nonneg _),
    Int.toNat_of_nonneg (triangular_nonneg _), hsucc, zpow_add₀ ha, mul_zpow, mul_assoc]

private lemma neg_term {a b : ℂ} (ha : a ≠ 0) (n : ℤ) :
    ramanujanThetaTerm (-a) (-b) n = (-1 : ℂ) ^ n * ramanujanThetaTerm a b n := by
  rw [term_eq (neg_ne_zero.mpr ha), term_eq ha, neg_mul_neg, ← mul_assoc, ← mul_zpow]
  simp

-- The odd pairs of indices are (1 - r - s, s - r), for unique integers r, s.
private def oddPair (p : ℤ × ℤ) : ℤ × ℤ := (1 - p.1 - p.2, p.2 - p.1)

private lemma oddPair_injective : Function.Injective oddPair := by
  rintro ⟨r, s⟩ ⟨t, u⟩ h
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  dsimp at h₁ h₂
  exact Prod.ext (by omega) (by omega)

private lemma mem_range_oddPair {m n : ℤ} (h : ¬ Even (m + n)) :
    (m, n) ∈ Set.range oddPair := by
  rw [Int.even_iff] at h
  exact ⟨((1 - m - n) / 2, (1 - m + n) / 2), Prod.ext (by dsimp [oddPair]; omega)
    (by dsimp [oddPair]; omega)⟩

private lemma triangular_oddPair (r s : ℤ) :
    triangular (1 - r - s) + triangular (s - r) =
      r + 2 * triangular r + 2 * triangular s := by
  linarith [twice_triangular (1 - r - s), twice_triangular (s - r),
    twice_triangular r, twice_triangular s]

private lemma parameter_products {a b c d : ℂ} (h : a * b = c * d) (hc : c ≠ 0)
    (hd : d ≠ 0) :
    b / c * (a * c ^ 2 * d) = (a * b) ^ 2 ∧ b / d * (a * c * d ^ 2) = (a * b) ^ 2 := by
  rw [pow_two (a * b), h]
  constructor <;> field_simp <;> linear_combination h

private lemma reindexed_term {a b c d : ℂ} (h : a * b = c * d) (ha : a ≠ 0)
    (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (r s : ℤ) :
    ramanujanThetaTerm a b (1 - r - s) * ramanujanThetaTerm c d (s - r) =
      a * (ramanujanThetaTerm (b / c) (a * c ^ 2 * d) r *
        ramanujanThetaTerm (b / d) (a * c * d ^ 2) s) := by
  let q := a * b
  have hq : q ≠ 0 := mul_ne_zero ha hb
  have h₁ : b / c = q / (a * c) := by dsimp [q]; field_simp
  have h₂ : b / d = c / a := by
    field_simp
    linear_combination h
  have ⟨hp₁, hp₂⟩ := parameter_products h hc hd
  rw [term_eq ha, term_eq hc, term_eq (div_ne_zero hb hc), term_eq (div_ne_zero hb hd),
    ← h, hp₁, hp₂, h₁, h₂, show a * b = q from rfl]
  calc
    _ = a ^ (1 - r - s) * c ^ (s - r) *
        q ^ (triangular (1 - r - s) + triangular (s - r)) := by rw [zpow_add₀ hq]; ring
    _ = _ := by
      rw [triangular_oddPair]
      simp only [zpow_sub₀ ha, zpow_sub₀ hc, zpow_add₀ hq, zpow_mul,
        div_zpow, mul_zpow, zpow_ofNat]
      ring

private noncomputable def difference (a b c d : ℂ) (p : ℤ × ℤ) : ℂ :=
  ramanujanThetaTerm a b p.1 * ramanujanThetaTerm c d p.2 -
    ramanujanThetaTerm (-a) (-b) p.1 * ramanujanThetaTerm (-c) (-d) p.2

private lemma difference_eq {a b c d : ℂ} (ha : a ≠ 0) (hc : c ≠ 0) (m n : ℤ) :
    difference a b c d (m, n) = (1 - (-1 : ℂ) ^ (m + n)) *
      (ramanujanThetaTerm a b m * ramanujanThetaTerm c d n) := by
  simp only [difference, neg_term ha, neg_term hc, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  ring

end RamanujanThetaProduct

open RamanujanThetaProduct

/-- **Ramanujan's theta function: difference of products when $ab = cd$.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function. For
complex numbers $a, b, c, d$ with $ab = cd$, $|ab| < 1$, $c \ne 0$ and $d \ne 0$,
$f(a,b) f(c,d) - f(-a,-b) f(-c,-d) = 2a \, f(b/c, ac^2 d) \, f(b/d, acd^2)$.

This is Entry 29(ii) of Berndt's *Ramanujan's Notebooks*, where the second arguments are written
$(c/b)abcd = ac^2 d$ and $(d/b)abcd = acd^2$.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 2, Equation (7) (`integers-2024-A103-lem-2`). -/
public theorem ramanujanTheta_mul_sub_mul_neg {a b c d : ℂ} (habcd : a * b = c * d)
    (hab : ‖a * b‖ < 1) (hc : c ≠ 0) (hd : d ≠ 0) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d -
        ramanujanThetaRaw (-a) (-b) * ramanujanThetaRaw (-c) (-d) =
      2 * a * ramanujanThetaRaw (b / c) (a * c ^ 2 * d) *
        ramanujanThetaRaw (b / d) (a * c * d ^ 2) := by
  have hne : a * b ≠ 0 := habcd ▸ mul_ne_zero hc hd
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.mp hne
  have habs := ramanujanTheta_summable a b hab
  have hcds := ramanujanTheta_summable c d (habcd ▸ hab)
  have hnabs := ramanujanTheta_summable (-a) (-b) (by simpa only [neg_mul_neg] using hab)
  have hncds := ramanujanTheta_summable (-c) (-d) (by simpa only [neg_mul_neg, ← habcd] using hab)
  have ⟨hp₁, hp₂⟩ := parameter_products habcd hc hd
  have hsq : ‖(a * b) ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hab (by decide)
  have hs₁ := ramanujanTheta_summable _ _ (hp₁ ▸ hsq)
  have hs₂ := ramanujanTheta_summable _ _ (hp₂ ▸ hsq)
  have hreindex : (∑' p, difference a b c d (oddPair p)) = ∑' p, difference a b c d p := by
    apply oddPair_injective.tsum_eq
    rintro ⟨m, n⟩ h
    apply mem_range_oddPair
    intro heven
    apply h
    rw [difference_eq ha hc, heven.neg_one_zpow, sub_self, zero_mul]
  unfold ramanujanThetaRaw
  rw [tsum_mul_tsum_of_summable_norm habs hcds, tsum_mul_tsum_of_summable_norm hnabs hncds,
    ← (summable_mul_of_summable_norm habs hcds).tsum_sub
      (summable_mul_of_summable_norm hnabs hncds),
    mul_assoc (2 * a), tsum_mul_tsum_of_summable_norm hs₁ hs₂, ← tsum_mul_left]
  change (∑' p, difference a b c d p) = _
  rw [← hreindex]
  apply tsum_congr
  rintro ⟨r, s⟩
  have hodd : Odd (1 - r - s + (s - r)) := ⟨-r, by ring⟩
  rw [oddPair, difference_eq ha hc, hodd.neg_one_zpow, reindexed_term habcd ha hb hc hd]
  ring

end MetaMathlibExt
