/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith

/-!
# Single-set sum-difference exponent

The constant `C₃d` is the least real exponent that bounds the normalized
sumset cardinality by the corresponding normalized difference-set cardinality.
The frozen source states that its exact value is `2`.

We prove this value using the Plünnecke–Ruzsa inequality and an integer digit construction
based on the six digits of Lin and Li. Four translates of their digit set cover all base-84
digits by sums and give only 83 differences. Iterating gives a set in an interval of length
`n = 84 ^ d` whose sums cover the interval and whose differences occupy at most `83 ^ d` values.

To obtain sharpness, take one full interval and put copies of the digit set at multiples of
`n` indexed by a small additive basis of `[0, k²)`. Sums of these copies cover `k² * n` values.
Differences involving the full interval occupy at most `O(k * n)` values, and the other
differences satisfy the same bound once the digit depth is large enough.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SingleSetSumDifferenceExponentWanted

open scoped Pointwise

/-! Source record `C3d`, file SHA-256
`115fbd7c1cb17caa8e865a1dd2850589c09e102659247ffece53ad3824ec01cb`. -/

/-- **Admissible exponents for sums and differences.** A real number $\theta$ is an admissible
exponent when every nonempty finite set $A$ of integers satisfies
$|A+A|/|A| \le (|A-A|/|A|)^{\theta}$, where $A+A$ and $A-A$ are the sumset and the difference
set of $A$. -/
def IsAdmissibleExponent (θ : ℝ) : Prop :=
  ∀ A : Finset ℤ, A.Nonempty →
    ((A + A).card : ℝ) / (A.card : ℝ) ≤
      Real.rpow (((A - A).card : ℝ) / (A.card : ℝ)) θ

/-- **The single-set sum-difference exponent.** The single-set sum-difference exponent $C_{3d}$ is
the infimum of the admissible exponents, that is, of the set of real numbers $\theta$ such that
$|A+A|/|A| \le (|A-A|/|A|)^{\theta}$ for every nonempty finite set $A$ of integers, where $A+A$
and $A-A$ are the sumset and the difference set of $A$.

This is the source's equivalent formulation of $C_{3d}$ as a least admissible exponent, over
finite sets of integers. -/
noncomputable def singleSetSumDifferenceExponent : ℝ :=
  sInf {θ : ℝ | IsAdmissibleExponent θ}

/-- **The proposition that the single-set sum-difference exponent equals 2.** This is the
statement that the single-set sum-difference exponent $C_{3d}$ is equal to $2$. -/
def singleSetSumDifferenceExponent_eq_two : Prop :=
  singleSetSumDifferenceExponent = 2

open Finset

private def interval (n : ℕ) : Finset ℤ := Ico 0 n

private lemma card_interval (n : ℕ) : (interval n).card = n := by
  simp [interval, Int.card_Ico]

private def scale (n : ℕ) (S : Finset ℤ) : Finset ℤ :=
  S.image (AddMonoidHom.mulLeft (n : ℤ))

private lemma scale_add (n : ℕ) (S T : Finset ℤ) :
    scale n (S + T) = scale n S + scale n T := image_add _

private lemma scale_sub (n : ℕ) (S T : Finset ℤ) :
    scale n (S - T) = scale n S - scale n T := image_image₂_distrib (map_sub _)

private lemma interval_product {m : ℕ} (hm : 0 < m) (n : ℕ) :
    interval (m * n) ⊆ interval m + scale m (interval n) := by
  intro z hz
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  obtain ⟨hz₀, hz₁⟩ := mem_Ico.mp hz
  refine mem_add.mpr ⟨z % m, mem_Ico.mpr ⟨Int.emod_nonneg _ hm'.ne', Int.emod_lt_of_pos _ hm'⟩,
    (m : ℤ) * (z / m), ?_, Int.emod_add_mul_ediv ..⟩
  apply mem_image.mpr
  refine ⟨z / m, mem_Ico.mpr ⟨Int.ediv_nonneg hz₀ hm'.le, ?_⟩, rfl⟩
  apply (Int.ediv_lt_iff_lt_mul hm').mpr
  simpa [mul_comm] using hz₁

-- Four translates, spaced by 12, of the digit set of Lin and Li.
private def seed : Finset ℤ :=
  {0, 1, 2, 4, 5, 9, 12, 13, 14, 16, 17, 21, 24, 25, 26, 28, 29, 33, 36, 37, 38, 40, 41, 45}

private lemma seed_subset : seed ⊆ interval 84 := by decide

private lemma seed_sums : interval 84 ⊆ seed + seed := by decide +kernel

private lemma seed_differences : (seed - seed).card = 83 := by decide +kernel

private def digits : ℕ → Finset ℤ
  | 0 => {0}
  | d + 1 => seed + scale 84 (digits d)

private lemma digits_subset (d : ℕ) : digits d ⊆ interval (84 ^ d) := by
  induction d with
  | zero => simp [digits, interval]
  | succ d ih =>
    intro z hz
    obtain ⟨a, ha, _, hb, rfl⟩ := mem_add.mp hz
    obtain ⟨b, hbmem, rfl⟩ := mem_image.mp hb
    obtain ⟨ha₀, ha₁⟩ := mem_Ico.mp (seed_subset ha)
    obtain ⟨hb₀, hb₁⟩ := mem_Ico.mp (ih hbmem)
    apply mem_Ico.mpr
    change 0 ≤ a + 84 * b ∧ a + 84 * b < ((84 ^ (d + 1) : ℕ) : ℤ)
    push_cast at *
    rw [pow_succ]
    omega

private lemma digits_sums (d : ℕ) : interval (84 ^ d) ⊆ digits d + digits d := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [pow_succ', digits, add_add_add_comm, ← scale_add]
    exact (interval_product (by decide : 0 < 84) _).trans
      (add_subset_add seed_sums (image_subset_image ih))

private lemma differences_add (S T : Finset ℤ) :
    (S + T) - (S + T) = (S - S) + (T - T) := by
  simp only [sub_eq_add_neg, neg_add_rev]
  ac_rfl

private lemma digits_differences (d : ℕ) : (digits d - digits d).card ≤ 83 ^ d := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [digits, differences_add, ← scale_sub, pow_succ']
    exact card_add_le.trans (Nat.mul_le_mul seed_differences.le (card_image_le.trans ih))

private lemma exists_depth (k : ℕ) : ∃ d : ℕ, 2 * k * 83 ^ d ≤ 84 ^ d := by
  have h (d : ℕ) : (d + 83) * 83 ^ d ≤ 83 * 84 ^ d := by
    induction d with
    | zero => decide
    | succ d ih =>
      calc
        _ ≤ 84 * ((d + 83) * 83 ^ d) := by rw [pow_succ]; nlinarith [Nat.zero_le (d * 83 ^ d)]
        _ ≤ 84 * (83 * 84 ^ d) := Nat.mul_le_mul_left _ ih
        _ = _ := by ring
  refine ⟨166 * k, ?_⟩
  nlinarith [h (166 * k), Nat.zero_le (83 ^ (166 * k))]

private lemma card_interval_sub (n : ℕ) :
    (interval n - interval n).card ≤ 2 * n := by
  have h : interval n - interval n ⊆ Ico (-(n : ℤ)) n := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sub.mp hz
    obtain ⟨_, _⟩ := mem_Ico.mp ha
    obtain ⟨_, _⟩ := mem_Ico.mp hb
    exact mem_Ico.mpr (by omega)
  refine (card_le_card h).trans_eq ?_
  rw [Int.card_Ico]
  omega

-- The low digits and the multiples of k together form a small basis of [0,k²).
private def outer (k : ℕ) : Finset ℤ := interval k ∪ scale k (interval k)

private lemma outer_sums {k : ℕ} (hk : 0 < k) : interval (k * k) ⊆ outer k + outer k :=
  (interval_product hk k).trans (add_subset_add subset_union_left subset_union_right)

private lemma card_outer (k : ℕ) : (outer k).card ≤ 2 * k := by
  calc
    _ ≤ (interval k).card + (scale k (interval k)).card := card_union_le ..
    _ ≤ (interval k).card + (interval k).card := Nat.add_le_add_left card_image_le _
    _ = _ := by rw [card_interval]; omega

-- Use a full interval in row zero and a sparse copy of Y in each of the outer rows.
private lemma exists_example {k : ℕ} (hk : 0 < k) :
    ∃ (A : Finset ℤ) (n : ℕ), 0 < n ∧ n ≤ A.card ∧ A.card ≤ 2 * n ∧
      k ^ 2 * n ≤ (A + A).card ∧ (A - A).card ≤ 12 * k * n := by
  obtain ⟨d, hd⟩ := exists_depth k
  let n := 84 ^ d
  let D := interval n
  let Y := digits d
  let O := scale n (outer k)
  let X := O + Y
  let A := D ∪ X
  have hn : 0 < n := pow_pos (by decide) _
  have hD : D.card = n := card_interval n
  have hO : O.card ≤ 2 * k := card_image_le.trans (card_outer k)
  have hY : Y.card ≤ 83 ^ d := by
    obtain he | hne := Y.eq_empty_or_nonempty
    · simp [he]
    exact (card_le_card_sub_right hne).trans (digits_differences d)
  have hX : X.card ≤ n :=
    card_add_le.trans ((Nat.mul_le_mul hO hY).trans hd)
  refine ⟨A, n, hn, hD ▸ card_le_card subset_union_left,
    (card_union_le ..).trans (by omega), ?_, ?_⟩
  · have hrows : scale n (interval (k * k)) ⊆ O + O := by
      rw [← scale_add]
      exact image_subset_image (outer_sums hk)
    have hs : interval (n * (k * k)) ⊆ X + X := by
      change _ ⊆ (O + Y) + (O + Y)
      rw [add_add_add_comm, add_comm (O + O)]
      exact (interval_product hn _).trans (add_subset_add (digits_sums d) hrows)
    simpa [card_interval, pow_two, Nat.mul_comm, Nat.mul_left_comm] using
      card_le_card (hs.trans (add_subset_add subset_union_right subset_union_right :
        X + X ⊆ A + A))
  · have hDD := card_interval_sub n
    have hDY : (D - Y).card ≤ 2 * n :=
      (card_le_card (sub_subset_sub (Subset.rfl) (digits_subset d))).trans hDD
    have hYD : (Y - D).card ≤ 2 * n :=
      (card_le_card (sub_subset_sub (digits_subset d) (Subset.rfl))).trans hDD
    have hDX : (D - X).card ≤ (2 * n) * (2 * k) := by
      have he : D - X = (D - Y) - O := by simp only [X, sub_eq_add_neg, neg_add_rev, add_assoc]
      rw [he]
      exact card_sub_le.trans (Nat.mul_le_mul hDY hO)
    have hXD : (X - D).card ≤ (2 * k) * (2 * n) := by
      change ((O + Y) - D).card ≤ _
      rw [sub_eq_add_neg, add_assoc, ← sub_eq_add_neg]
      exact card_add_le.trans (Nat.mul_le_mul hO hYD)
    have hXX : (X - X).card ≤ (2 * k) * n := by
      change ((O + Y) - (O + Y)).card ≤ _
      rw [differences_add]
      calc
        _ ≤ (O - O).card * (Y - Y).card := card_add_le
        _ ≤ ((2 * k) * (2 * k)) * 83 ^ d :=
          Nat.mul_le_mul (card_sub_le.trans (Nat.mul_le_mul hO hO)) (digits_differences d)
        _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hd
    change ((D ∪ X) - (D ∪ X)).card ≤ _
    rw [union_sub, sub_union, sub_union]
    refine (card_union_le ..).trans
      ((Nat.add_le_add (card_union_le ..) (card_union_le ..)).trans ?_)
    change (D - D).card ≤ _ at hDD
    nlinarith only [hDD, hDX, hXD, hXX, Nat.mul_le_mul_right n (show 1 ≤ k from hk)]

private lemma two_admissible : IsAdmissibleExponent 2 := by
  intro A hA
  have h := pluennecke_ruzsa_inequality_nsmul_sub hA A 2
  rw [two_nsmul] at h
  rw [Real.rpow_eq_pow, Real.rpow_two, div_le_iff₀ (Nat.cast_pos.mpr hA.card_pos)]
  simpa using NNRat.cast_mono (K := ℝ) h

private lemma admissible_nonneg {θ : ℝ} (hθ : IsAdmissibleExponent θ) : 0 ≤ θ := by
  by_contra! hn
  have h := hθ (interval 2) (by decide)
  have hs : (interval 2 + interval 2).card = 3 := by decide
  have hd : (interval 2 - interval 2).card = 3 := by decide
  rw [hs, hd, card_interval, Real.rpow_eq_pow] at h
  have := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : 1 ≤ (3 : ℝ) / 2) hn.le
  norm_num at h
  linarith

private lemma two_le_admissible {θ : ℝ} (hθ : IsAdmissibleExponent θ) : 2 ≤ θ := by
  by_contra! hlt
  have he : 0 < 2 - θ := sub_pos.mpr hlt
  have hθ₀ := admissible_nonneg hθ
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ((2 * (12 : ℝ) ^ θ) ^ (2 - θ)⁻¹))
  have hk₀ : 0 < (k : ℝ) := lt_trans zero_lt_one ((le_max_left ..).trans_lt hk)
  have hp := Real.rpow_lt_rpow (by positivity) ((le_max_right ..).trans_lt hk) he
  rw [Real.rpow_inv_rpow (by positivity) he.ne', Real.rpow_sub hk₀,
    Real.rpow_two, lt_div_iff₀ (Real.rpow_pos_of_pos hk₀ θ)] at hp
  obtain ⟨A, n, hn, hA₀, hA₁, hS, hD⟩ := exists_example (Nat.cast_pos.mp hk₀)
  have hA : A.Nonempty := card_pos.mp (hn.trans_le hA₀)
  have hAc : 0 < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hAc₀ : (n : ℝ) ≤ A.card := by exact_mod_cast hA₀
  have hAc₁ : (A.card : ℝ) ≤ 2 * n := by exact_mod_cast hA₁
  have hSc : (k : ℝ) ^ 2 * n ≤ (A + A).card := by exact_mod_cast hS
  have hDc : ((A - A).card : ℝ) ≤ 12 * k * n := by exact_mod_cast hD
  have hsum : (k : ℝ) ^ 2 / 2 ≤ (A + A).card / (A.card : ℝ) := by
    apply (le_div_iff₀ hAc).mpr
    nlinarith [mul_le_mul_of_nonneg_left hAc₁ (sq_nonneg (k : ℝ))]
  have hdiff : (A - A).card / (A.card : ℝ) ≤ 12 * k := by
    apply (div_le_iff₀ hAc).mpr
    exact hDc.trans (by gcongr)
  have h := hsum.trans ((hθ A hA).trans (Real.rpow_le_rpow (by positivity) hdiff hθ₀))
  rw [Real.mul_rpow (by norm_num) hk₀.le] at h
  linarith

/-- **The single-set sum-difference exponent equals 2.** The single-set sum-difference exponent
$C_{3d}$ is equal to $2$.

Known constructions approach this value but do not attain it.

Source: Haowei Lin and Shanda Li, Settling the optimal
exponent relating sumsets and difference sets, arXiv:2607.27199v1 (2026),
https://arxiv.org/abs/2607.27199v1. Moved from
`OpenConjectures/Combinatorics/SingleSetSumDifferenceExponent`.
-/
public theorem singleSetSumDifferenceExponent_eq_two_holds :
    singleSetSumDifferenceExponent_eq_two := by
  change sInf {θ : ℝ | IsAdmissibleExponent θ} = 2
  exact (show IsLeast {θ : ℝ | IsAdmissibleExponent θ} 2 from
    ⟨two_admissible, fun _ h => two_le_admissible h⟩).csInf_eq

end MathlibExt.Combinatorics.SingleSetSumDifferenceExponentWanted
