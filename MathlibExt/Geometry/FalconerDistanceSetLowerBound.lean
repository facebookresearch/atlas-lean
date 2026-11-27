/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Geometry.FalconerDistanceSet
import Mathlib.Analysis.Real.OfDigits

/-!
# Falconer's lower bound for the planar distance threshold

The planar distance threshold is at least one. We embed deleted-digit sets in a line and
read their digits in a smaller base to bound their Hausdorff dimensions from below. Their
difference sets have too few first-digit translations to have positive measure.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace FalconerDistanceSetWanted

/-- Encode a base-`m` digit stream using the even digits below `2 * m` in base `4 * m`. -/
private def evenDigit {m : ℕ} (i : Fin m) : Fin (4 * m) :=
  ⟨2 * i.val, by omega⟩

private noncomputable def code {m : ℕ} (a : ℕ → Fin m) : ℝ :=
  Real.ofDigits (fun i ↦ evenDigit (a i))

private theorem continuous_code (m : ℕ) : Continuous (@code m) :=
  Real.continuous_ofDigits.comp (continuous_pi fun i ↦
    (continuous_of_discreteTopology (f := @evenDigit m)).comp (continuous_apply i))

private theorem code_head {m : ℕ} (a : ℕ → Fin m) :
    (4 * m : ℝ) * code a = 2 * (a 0 : ℝ) + code (fun i ↦ a (i + 1)) := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos (a 0)).ne'
  unfold code
  rw [Real.ofDigits_eq_sum_add_ofDigits (fun i ↦ evenDigit (a i)) 1]
  simp [Real.ofDigitsTerm, evenDigit, Nat.cast_mul]
  field_simp

/-- At the first differing digit, the even digits are at least two apart and the tails
can compensate for at most one unit. -/
private theorem separation {m : ℕ} (a b : ℕ → Fin m) {n : ℕ}
    (hp : ∀ i < n, a i = b i) (hn : a n ≠ b n) :
    ((4 * m : ℝ) ^ (n + 1))⁻¹ ≤ |code a - code b| := by
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr (Fin.pos (a 0))
  let tail (c : ℕ → Fin m) := fun i ↦ c (i + n)
  have split : code a - code b =
      ((4 * m : ℝ) ^ n)⁻¹ * (code (tail a) - code (tail b)) := by
    unfold code
    rw [Real.ofDigits_eq_sum_add_ofDigits (fun i ↦ evenDigit (a i)) n,
      Real.ofDigits_eq_sum_add_ofDigits (fun i ↦ evenDigit (b i)) n]
    have heq : ∀ i ∈ Finset.range n, Real.ofDigitsTerm (fun j ↦ evenDigit (a j)) i =
        Real.ofDigitsTerm (fun j ↦ evenDigit (b j)) i := by
      intro i hi
      simp only [Real.ofDigitsTerm, hp i (Finset.mem_range.mp hi)]
    rw [Finset.sum_congr rfl heq, add_sub_add_left_eq_sub, ← mul_sub]
    simp [tail]
  have gap (c d : ℕ → Fin m) (h : c n < d n) :
      1 ≤ (4 * m : ℝ) * (code (tail d) - code (tail c)) := by
    rw [mul_sub, code_head, code_head]
    have hd : (c n : ℝ) + 1 ≤ (d n : ℝ) := by
      exact_mod_cast (show (c n).val + 1 ≤ (d n).val from h)
    simp only [tail, zero_add]
    unfold code
    linarith [Real.ofDigits_nonneg (fun i ↦ evenDigit (d (i + 1 + n))),
      Real.ofDigits_le_one (fun i ↦ evenDigit (c (i + 1 + n)))]
  rw [split, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((4 * m : ℝ) ^ n)⁻¹),
    pow_succ, mul_inv]
  gcongr
  rw [inv_le_iff_one_le_mul₀ (by positivity), mul_comm]
  rcases lt_or_gt_of_ne hn with h | h
  · rw [abs_sub_comm]
    exact (gap a b h).trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  · exact (gap b a h).trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))

/-- Reading the same digit stream in base `m` is Hölder on the encoded set. -/
private theorem decode_bound {m : ℕ} (hm : 1 < m) {r : ℝ≥0}
    (hr : (4 * m : ℝ) ^ (r : ℝ) = m) (a b : ℕ → Fin m) :
    |Real.ofDigits a - Real.ofDigits b| ≤ m * |code a - code b| ^ (r : ℝ) := by
  classical
  by_cases hab : a = b
  · subst b
    simp only [sub_self, abs_zero]
    positivity
  have hex : ∃ n, a n ≠ b n := Function.ne_iff.mp hab
  let n := Nat.find hex
  have hp (i : ℕ) (hi : i < n) : a i = b i := not_not.mp (Nat.find_min hex hi)
  have hm' : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  calc
    |Real.ofDigits a - Real.ofDigits b| ≤ ((m : ℝ) ^ n)⁻¹ := Real.abs_ofDigits_sub_ofDigits_le hp
    _ = m * (((4 * m : ℝ) ^ (n + 1))⁻¹) ^ (r : ℝ) := by
      rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast_mul (by positivity),
        mul_comm ((n + 1 : ℕ) : ℝ), Real.rpow_mul (by positivity), hr, Real.rpow_natCast, pow_succ]
      field_simp
    _ ≤ _ := by
      gcongr
      exact separation a b hp (Nat.find_spec hex)

private theorem dimH_code {m : ℕ} (hm : 1 < m) {r : ℝ≥0} (hr₀ : 0 < r)
    (hr : (4 * m : ℝ) ^ (r : ℝ) = m) : (r : ℝ≥0∞) ≤ dimH (range (@code m)) := by
  classical
  let : NeZero m := ⟨by omega⟩
  let f : ℝ → ℝ := Real.ofDigits ∘ Function.invFun (@code m)
  have hinj : Function.Injective (@code m) := by
    intro a b he
    by_contra hab
    have hex := Function.ne_iff.mp hab
    have h := separation a b (fun i hi ↦ not_not.mp (Nat.find_min hex hi)) (Nat.find_spec hex)
    rw [he, sub_self, abs_zero] at h
    have hm' : 0 < (m : ℝ) := by positivity
    exact (not_le_of_gt (by positivity)) h
  have hf (a : ℕ → Fin m) : f (code a) = Real.ofDigits a := by
    simp [f, Function.leftInverse_invFun hinj a]
  have holder : HolderOnWith m r f (range (@code m)) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [hf, hf, edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) r.coe_nonneg]
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast, ENNReal.coe_natCast]
      using ENNReal.ofReal_le_ofReal (decode_bound hm hr a b)
  have image : Icc (0 : ℝ) 1 ⊆ f '' range (@code m) := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Real.ofDigits_SurjOn hm hx
    exact ⟨code a, mem_range_self a, hf a⟩
  have dimI : dimH (Icc (0 : ℝ) 1) = 1 := by
    simpa using Real.dimH_of_mem_nhds
      (Icc_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  have h := (dimH_mono image).trans (holder.dimH_image_le hr₀)
  rw [dimI, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hr₀.ne'))
    (Or.inl ENNReal.coe_ne_top), one_mul] at h
  exact h

private noncomputable def differences (m : ℕ) : Set ℝ :=
  range (fun p : (ℕ → Fin m) × (ℕ → Fin m) ↦ code p.1 - code p.2)

/-- Removing the first digit covers the difference set by at most `2 * m` translates of
a copy scaled by `1 / (4 * m)`, so its finite measure must vanish. -/
private theorem volume_differences {m : ℕ} (hm : 1 < m) : volume (differences m) = 0 := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  let piece (j : Fin (2 * m)) :=
    (fun x : ℝ ↦ (4 * m) * x) ⁻¹' ((fun x : ℝ ↦ x + 2 * (m - (j : ℝ))) ⁻¹' differences m)
  have cover : differences m ⊆ ⋃ j, piece j := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    let j : Fin (2 * m) := ⟨m + (a 0).val - (b 0).val, by have := (a 0).isLt; omega⟩
    apply mem_iUnion.mpr
    refine ⟨j, ⟨(fun i ↦ a (i + 1), fun i ↦ b (i + 1)), ?_⟩⟩
    change _ = (4 * m : ℝ) * (code a - code b) + 2 * (m - (j : ℝ))
    rw [mul_sub, code_head, code_head]
    have hj : (j : ℝ) = m + (a 0 : ℝ) - (b 0 : ℝ) := by
      simp [j, Nat.cast_sub (by have := (b 0).isLt; omega : (b 0).val ≤ m + (a 0).val)]
    rw [hj]
    ring
  have meas (j) : volume (piece j) =
      ENNReal.ofReal (4 * m : ℝ)⁻¹ * volume (differences m) := by
    dsimp [piece]
    rw [Real.volume_preimage_mul_left (by positivity), measure_preimage_add_right,
      abs_of_pos (by positivity)]
  have h := (measure_mono cover).trans (measure_iUnion_fintype_le volume piece)
  simp only [meas, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hfin : volume (differences m) ≠ ⊤ :=
    (isCompact_range (((continuous_code m).comp continuous_fst).sub
      ((continuous_code m).comp continuous_snd))).measure_lt_top.ne
  have hR := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_mul,
    Nat.cast_ofNat, ENNReal.toReal_ofReal (by positivity : 0 ≤ (4 * m : ℝ)⁻¹)] at hR
  have hhalf : (2 * m : ℝ) * (4 * m : ℝ)⁻¹ = 1 / 2 := by field_simp; ring
  rw [← mul_assoc, hhalf] at hR
  have hzero : (volume (differences m)).toReal = 0 :=
    le_antisymm (by linarith) ENNReal.toReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right hfin

/-- Isometrically embed the digit set in a coordinate axis of the Euclidean plane. -/
private theorem exponent_le_threshold {m : ℕ} (hm : 1 < m) {r : ℝ≥0} (hr₀ : 0 < r)
    (hr : (4 * m : ℝ) ^ (r : ℝ) = m) :
    (r : ℝ≥0∞) ≤ FalconerDistanceSet.planarDistanceThreshold := by
  let axis : ℝ → EuclideanSpace ℝ (Fin 2) := PiLp.single (β := fun _ : Fin 2 ↦ ℝ) 2 0
  have hi : Isometry axis := isometry_iff_dist_eq.mpr (fun x y ↦ PiLp.dist_single_same ..)
  apply FalconerDistanceSet.le_planarDistanceThreshold_of_zeroMeasureWitness
    ((isCompact_range (continuous_code m)).image hi.continuous)
  · rw [hi.dimH_image]
    exact dimH_code hm hr₀ hr
  · apply measure_mono_null _ (volume_differences hm)
    rintro _ ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, _, ⟨_, ⟨b, rfl⟩, rfl⟩, rfl⟩
    rw [hi.dist_eq, Real.dist_eq]
    rcases le_total (code b) (code a) with h | h
    · exact ⟨(a, b), (abs_of_nonneg (sub_nonneg.mpr h)).symm⟩
    · exact ⟨(b, a), by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]⟩

private theorem ratio_le_threshold {k : ℕ} (hk : 0 < k) :
    (k : ℝ) / (k + 1) ≤ FalconerDistanceSet.planarDistanceThreshold.toReal := by
  let r : ℝ≥0 := k / (k + 1)
  have hr₀ : 0 < r := by dsimp [r]; positivity
  have hr : (4 * (4 ^ k : ℕ) : ℝ) ^ (r : ℝ) = (4 ^ k : ℕ) := by
    push_cast
    rw [← pow_succ', ← Real.rpow_natCast_mul (by norm_num), Nat.cast_add_one]
    have he : (k + 1 : ℝ) * (r : ℝ) = k := by simp [r]; field_simp
    rw [he, Real.rpow_natCast]
  have hm : 1 < 4 ^ k := one_lt_pow₀ (by decide) hk.ne'
  have h := exponent_le_threshold hm hr₀ hr
  simpa only [ENNReal.coe_toReal, r, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_add,
    NNReal.coe_one] using ENNReal.toReal_mono FalconerDistanceSet.planarDistanceThreshold_ne_top h

/-- **Statement of the lower bound $1$ for the planar distance threshold.** This is the
proposition that the planar distance threshold, the infimum of all $s \in [0, 2]$ such that
every compact set $E \subseteq \mathbb{R}^2$ of Hausdorff dimension strictly greater than $s$
has a distance set $\{\|x - y\| : x, y \in E\}$ of positive one-dimensional Lebesgue measure,
is at least $1$.

Source: optimization catalogue C34a and GIOW's endpoint lattice examples, line 76. -/
def lowerBound_Falconer1985 : Prop :=
  (1 : ℝ≥0∞) ≤ FalconerDistanceSet.planarDistanceThreshold

/-- **Falconer's lower bound for the planar distance threshold.** The planar distance
threshold, the infimum of all $s \in [0, 2]$ such that every compact set
$E \subseteq \mathbb{R}^2$ of Hausdorff dimension strictly greater than $s$ has a distance set
$\{\|x - y\| : x, y \in E\}$ of positive one-dimensional Lebesgue measure, is at least $1$.

Source: optimization catalogue C34a and GIOW, arXiv:1808.09346v1, line 76. -/
theorem lowerBound_Falconer1985_holds : lowerBound_Falconer1985 := by
  apply (ENNReal.toReal_le_toReal (by simp) FalconerDistanceSet.planarDistanceThreshold_ne_top).mp
  rw [ENNReal.toReal_one]
  exact le_of_tendsto (tendsto_natCast_div_add_atTop (1 : ℝ))
    ((Filter.eventually_gt_atTop (0 : ℕ)).mono fun _ hk ↦ ratio_le_threshold hk)

end FalconerDistanceSetWanted
