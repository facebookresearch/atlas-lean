/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.DepthSeparationConstruction
public import CSLibExt.MachineLearning.DepthSeparationPieces
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
Depth-separation oscillation lower bound: the `L ^ 2 + 2`-fold tent iterate
needs `2 ^ (L ^ 2)` affine pieces to approximate in `L1` on `[0, 1]`.
Follows the counting-triangles proof of Theorem 5.1 in Telgarsky's
deep learning theory notes (Section 5.2).
-/

@[expose] public section

open Cslib.MachineLearning.DepthSeparationPieces Cslib.MachineLearning.Backpropagation

namespace Cslib.MachineLearning.DepthSeparation

/-- The ReLU is continuous. -/
private theorem continuous_relu : Continuous relu := by
  unfold relu
  exact continuous_id'.max continuous_const

/-- The tent map is continuous. -/
private theorem continuous_tent : Continuous tent := by
  unfold tent
  exact (((continuous_const.mul continuous_relu).sub
    (continuous_const.mul (continuous_relu.comp
      (continuous_id.sub continuous_const)))).add
    (continuous_const.mul (continuous_relu.comp
      (continuous_id.sub continuous_const))))

/-- Iterated tent maps are continuous. -/
private theorem continuous_tentIter (k : ℕ) :
    Continuous (tentIter k) := by
  induction k with
  | zero =>
    have h0 : tentIter 0 = fun x : ℝ => x := funext tentIter_zero
    rw [h0]
    exact continuous_id'
  | succ k ih =>
    have hs : tentIter (k + 1) = (tentIter k) ∘ tent :=
      funext (tentIter_succ k)
    rw [hs]
    exact ih.comp continuous_tent

/-- A function with finitely many affine pieces is continuous: around any
point, it is affine on each side of the nearest breakpoints. -/
private theorem piecesLE_continuous {g : ℝ → ℝ} {n : ℕ}
    (hP : PiecesLE n g) : Continuous g := by
  obtain ⟨s, -, hsec⟩ := hP
  rw [continuous_iff_continuousAt]
  intro c
  classical
  obtain ⟨x, hxc, hx⟩ : ∃ x, x < c ∧ ∀ p ∈ s, p < c → p ≤ x := by
    by_cases hL : (s.filter (· < c)).Nonempty
    · refine ⟨(s.filter (· < c)).max' hL, ?_, ?_⟩
      · exact (Finset.mem_filter.mp (Finset.max'_mem _ hL)).2
      · intro p hp hpc
        exact Finset.le_max' _ p (Finset.mem_filter.mpr ⟨hp, hpc⟩)
    · refine ⟨c - 1, by linarith, ?_⟩
      intro p hp hpc
      exact absurd ⟨p, Finset.mem_filter.mpr ⟨hp, hpc⟩⟩ hL
  obtain ⟨z, hcz, hz⟩ : ∃ z, c < z ∧ ∀ p ∈ s, c < p → z ≤ p := by
    by_cases hR : (s.filter (c < ·)).Nonempty
    · refine ⟨(s.filter (c < ·)).min' hR, ?_, ?_⟩
      · exact (Finset.mem_filter.mp (Finset.min'_mem _ hR)).2
      · intro p hp hcp
        exact Finset.min'_le _ p (Finset.mem_filter.mpr ⟨hp, hcp⟩)
    · refine ⟨c + 1, by linarith, ?_⟩
      intro p hp hcp
      exact absurd ⟨p, Finset.mem_filter.mpr ⟨hp, hcp⟩⟩ hR
  have he1 : ∀ p ∈ s, ¬(x < p ∧ p < c) := by
    intro p hp h
    exact (not_le_of_gt h.1) (hx p hp h.2)
  have he2 : ∀ p ∈ s, ¬(c < p ∧ p < z) := by
    intro p hp h
    exact (not_le_of_gt h.2) (hz p hp h.1)
  have hne1 : c - x ≠ 0 := ne_of_gt (sub_pos.mpr hxc)
  have hne2 : z - c ≠ 0 := ne_of_gt (sub_pos.mpr hcz)
  have hg1 : ∀ y ∈ Set.Icc x c,
      g y = g x + ((g c - g x) / (c - x)) * (y - x) := by
    intro y hy
    have hsec_app := hsec x y c hy.1 hy.2 he1
    have h2 : ((g c - g x) / (c - x)) * (c - x) = (g c - g x) :=
      div_mul_cancel₀ _ hne1
    have hmul : (g y - g x) * (c - x)
        = (((g c - g x) / (c - x)) * (y - x)) * (c - x) := by
      linear_combination hsec_app - (y - x) * h2
    have hcancel := mul_right_cancel₀ hne1 hmul
    linarith [hcancel]
  have hg2 : ∀ y ∈ Set.Icc c z,
      g y = g c + ((g z - g c) / (z - c)) * (y - c) := by
    intro y hy
    have hsec_app := hsec c y z hy.1 hy.2 he2
    have h2 : ((g z - g c) / (z - c)) * (z - c) = (g z - g c) :=
      div_mul_cancel₀ _ hne2
    have hmul : (g y - g c) * (z - c)
        = (((g z - g c) / (z - c)) * (y - c)) * (z - c) := by
      linear_combination hsec_app - (y - c) * h2
    have hcancel := mul_right_cancel₀ hne2 hmul
    linarith [hcancel]
  have hcont1 : ContinuousOn g (Set.Icc x c) := by
    have hA : Continuous fun y : ℝ =>
        g x + ((g c - g x) / (c - x)) * (y - x) :=
      continuous_const.add
        (continuous_const.mul (continuous_id.sub continuous_const))
    exact hA.continuousOn.congr hg1
  have hcont2 : ContinuousOn g (Set.Icc c z) := by
    have hA : Continuous fun y : ℝ =>
        g c + ((g z - g c) / (z - c)) * (y - c) :=
      continuous_const.add
        (continuous_const.mul (continuous_id.sub continuous_const))
    exact hA.continuousOn.congr hg2
  have hcont : ContinuousOn g (Set.Icc x z) := by
    have hunion : Set.Icc x c ∪ Set.Icc c z = Set.Icc x z :=
      Set.Icc_union_Icc_eq_Icc hxc.le hcz.le
    rw [← hunion]
    exact hcont1.union_of_isClosed hcont2 isClosed_Icc isClosed_Icc
  exact hcont.continuousAt (Icc_mem_nhds hxc hcz)

/-- Absolute value of an interval integral is bounded by the integral of the
absolute value. -/
private theorem abs_intervalIntegral_le (f : ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) :
    |∫ t in a..b, f t| ≤ ∫ t in a..b, |f t| := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have h := MeasureTheory.norm_integral_le_integral_norm f
    (μ := MeasureTheory.volume.restrict (Set.Ioc a b))
  simpa only [Real.norm_eq_abs] using h

/-- Integral of `t - p` over `[p, q]` via the fundamental theorem. -/
private theorem integral_sub_self (p q : ℝ) (hpq : p ≤ q) :
    ∫ t in p..q, (t - p) = (q - p) ^ 2 / 2 := by
  have hderiv : ∀ x ∈ Set.Ioo p q,
      HasDerivAt ((fun t : ℝ => t - p) ^ 2) (2 * (x - p)) x := by
    intro x _
    have hsub : HasDerivAt (fun t : ℝ => t - p) 1 x :=
      (hasDerivAt_id' x).sub_const p
    simpa using hsub.pow 2
  have hcont : ContinuousOn ((fun t : ℝ => t - p) ^ 2) (Set.Icc p q) := by
    have hc : Continuous (fun t : ℝ => t - p) :=
      continuous_id.sub continuous_const
    exact (hc.pow 2).continuousOn
  have hint : IntervalIntegrable (fun t : ℝ => 2 * (t - p))
      MeasureTheory.volume p q := by
    have hc : Continuous (fun t : ℝ => 2 * (t - p)) :=
      continuous_const.mul (continuous_id.sub continuous_const)
    exact ContinuousOn.intervalIntegrable_of_Icc hpq hc.continuousOn
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hpq hcont
    hderiv hint
  have hFq : ((fun t : ℝ => t - p) ^ 2) q = (q - p) ^ 2 := rfl
  have hFp : ((fun t : ℝ => t - p) ^ 2) p = 0 := by
    change (p - p) ^ 2 = 0
    ring
  rw [hFq, hFp, sub_zero] at hFTC
  have hFTC' : 2 * (∫ t in p..q, (t - p)) = (q - p) ^ 2 := by
    simpa only [intervalIntegral.integral_const_mul] using hFTC
  linarith [hFTC']

/-- Integral of an affine function is length times the average of the endpoint
values. -/
private theorem integral_affine_eq (h : ℝ → ℝ) (p q c s : ℝ)
    (hpq : p ≤ q)
    (heq : ∀ t ∈ Set.Icc p q, h t = c + s * (t - p)) :
    ∫ t in p..q, h t = (q - p) * (h p + h q) / 2 := by
  have hp_eq : h p = c := by
    rw [heq p ⟨le_rfl, hpq⟩]
    ring
  have hq_eq : h q = c + s * (q - p) := heq q ⟨hpq, le_rfl⟩
  have hcongr : ∫ t in p..q, h t = ∫ t in p..q, (c + s * (t - p)) := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le hpq] at ht
    show h t = c + s * (t - p)
    exact heq t (Set.Ioc_subset_Icc_self ht)
  have hconst : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume p q :=
    ContinuousOn.intervalIntegrable_of_Icc hpq continuous_const.continuousOn
  have hlin : IntervalIntegrable (fun t : ℝ => s * (t - p))
      MeasureTheory.volume p q := by
    have hc : Continuous (fun t : ℝ => s * (t - p)) :=
      continuous_const.mul (continuous_id.sub continuous_const)
    exact ContinuousOn.intervalIntegrable_of_Icc hpq hc.continuousOn
  have hsum : ∫ t in p..q, (c + s * (t - p))
      = (q - p) * c + s * ((q - p) ^ 2 / 2) := by
    have hadd := intervalIntegral.integral_add hconst hlin
    simp only [intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_const_mul] at hadd
    rw [integral_sub_self p q hpq] at hadd
    exact hadd
  rw [hcongr, hsum, hp_eq, hq_eq]
  ring

/-- Key estimate combining the two halves of an affine piece. -/
private theorem abs_three_add_ge (A B : ℝ) :
    2 * (|A| + |B|) ≤ |3 * A + B| + |A + 3 * B| := by
  rcases le_total 0 A with hA | hA <;> rcases le_total 0 B with hB | hB
  · rw [abs_of_nonneg hA, abs_of_nonneg hB,
      abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonneg hA, abs_of_nonpos hB]
    rcases le_total 0 (3 * A + B) with h1 | h1 <;>
      rcases le_total 0 (A + 3 * B) with h2 | h2
    · rw [abs_of_nonneg h1, abs_of_nonneg h2]; linarith
    · rw [abs_of_nonneg h1, abs_of_nonpos h2]; linarith
    · rw [abs_of_nonpos h1, abs_of_nonneg h2]; linarith
    · rw [abs_of_nonpos h1, abs_of_nonpos h2]; linarith
  · rw [abs_of_nonpos hA, abs_of_nonneg hB]
    rcases le_total 0 (3 * A + B) with h1 | h1 <;>
      rcases le_total 0 (A + 3 * B) with h2 | h2
    · rw [abs_of_nonneg h1, abs_of_nonneg h2]; linarith
    · rw [abs_of_nonneg h1, abs_of_nonpos h2]; linarith
    · rw [abs_of_nonpos h1, abs_of_nonneg h2]; linarith
    · rw [abs_of_nonpos h1, abs_of_nonpos h2]; linarith
  · rw [abs_of_nonpos hA, abs_of_nonpos hB,
      abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- On an interval where `h` is affine, the integral of `|h|` is at least the
quarter-length times the endpoint absolute-value sum. -/
private theorem integral_abs_affine_half (h : ℝ → ℝ) (u v c s : ℝ)
    (huv : u ≤ v)
    (heq : ∀ t ∈ Set.Icc u v, h t = c + s * (t - u))
    (hcont : ContinuousOn h (Set.Icc u v)) :
    (v - u) * (|h u| + |h v|) / 4 ≤ ∫ t in u..v, |h t| := by
  set m : ℝ := (u + v) / 2 with hmdef
  have hum : u ≤ m := by rw [hmdef]; linarith [huv]
  have hmv : m ≤ v := by rw [hmdef]; linarith [huv]
  have hm_mem : m ∈ Set.Icc u v := ⟨hum, hmv⟩
  have hcont_abs : ContinuousOn (fun t => |h t|) (Set.Icc u v) := hcont.abs
  have hI1 : IntervalIntegrable (fun t => |h t|) MeasureTheory.volume u m :=
    ContinuousOn.intervalIntegrable_of_Icc hum
      (hcont_abs.mono (fun t ht => ⟨ht.1, ht.2.trans hmv⟩))
  have hI2 : IntervalIntegrable (fun t => |h t|) MeasureTheory.volume m v :=
    ContinuousOn.intervalIntegrable_of_Icc hmv
      (hcont_abs.mono (fun t ht => ⟨hum.trans ht.1, ht.2⟩))
  have hadj : (∫ t in u..m, |h t|) + (∫ t in m..v, |h t|)
      = ∫ t in u..v, |h t| :=
    intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have heq1 : ∀ t ∈ Set.Icc u m, h t = c + s * (t - u) :=
    fun t ht => heq t ⟨ht.1, ht.2.trans hmv⟩
  have heq2 : ∀ t ∈ Set.Icc m v, h t = (c + s * (m - u)) + s * (t - m) := by
    intro t ht
    have h1 := heq t ⟨hum.trans ht.1, ht.2⟩
    linarith [h1]
  have hmid : h m = (h u + h v) / 2 := by
    have e1 := heq u ⟨le_rfl, huv⟩
    have e2 := heq v ⟨huv, le_rfl⟩
    have e3 := heq m hm_mem
    rw [hmdef] at e3 ⊢
    rw [e1, e2, e3]
    ring
  have haff1 : ∫ t in u..m, h t = (m - u) * (h u + h m) / 2 :=
    integral_affine_eq h u m c s hum heq1
  have haff2 : ∫ t in m..v, h t = (v - m) * (h m + h v) / 2 :=
    integral_affine_eq h m v (c + s * (m - u)) s hmv heq2
  have hlen : m - u = (v - u) / 2 ∧ v - m = (v - u) / 2 := by
    rw [hmdef]
    constructor <;> ring
  have hb1 := abs_intervalIntegral_le h hum
  have hb2 := abs_intervalIntegral_le h hmv
  have e1 : h u + h m = (3 * (h u) + (h v)) / 2 := by rw [hmid]; ring
  have e2 : h m + h v = ((h u) + 3 * (h v)) / 2 := by rw [hmid]; ring
  have halg := abs_three_add_ge (h u) (h v)
  have hK : (0 : ℝ) ≤ (v - u) / 2 := by linarith [huv]
  have eabs1 : |((v - u) / 2) * ((3 * (h u) + (h v)) / 2) / 2|
      = ((v - u) / 2) * (|3 * (h u) + (h v)| / 4) := by
    rw [abs_div, abs_mul, abs_of_nonneg hK, abs_div]
    norm_num
    ring
  have eabs2 : |((v - u) / 2) * (((h u) + 3 * (h v)) / 2) / 2|
      = ((v - u) / 2) * (|(h u) + 3 * (h v)| / 4) := by
    rw [abs_div, abs_mul, abs_of_nonneg hK, abs_div]
    norm_num
    ring
  rw [haff1, hlen.1, e1, eabs1] at hb1
  rw [haff2, hlen.2, e2, eabs2] at hb2
  have hsum := add_le_add hb1 hb2
  have hmul := mul_le_mul_of_nonneg_left halg
    (show (0 : ℝ) ≤ (v - u) / 8 by linarith [huv])
  linear_combination hsum + hmul + hadj

/-- Dyadic grid points are strictly monotone in the numerator. -/
private theorem dyad_strictMono (k m n : ℕ) (h : m < n) :
    (m : ℝ) / (2 : ℝ) ^ k < (n : ℝ) / (2 : ℝ) ^ k := by
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hlt : (m : ℝ) < (n : ℝ) := by exact_mod_cast h
  exact (div_lt_div_iff_of_pos_right h2k).mpr hlt

/-- Scaling a dyadic grid point by `2 ^ k` recovers the numerator. -/
private theorem dyad_mul (k j : ℕ) :
    (2 : ℝ) ^ k * ((j : ℝ) / (2 : ℝ) ^ k) = (j : ℝ) := by
  have hne : (2 : ℝ) ^ k ≠ 0 := ne_of_gt (by positivity)
  rw [mul_comm ((2 : ℝ) ^ k) _]
  exact div_mul_cancel₀ _ hne

/-- Dyadic grid points at or below the top stay in `[0, 1]`. -/
private theorem dyad_le_one (k j : ℕ) (hj : j ≤ 2 ^ k) :
    (j : ℝ) / (2 : ℝ) ^ k ≤ 1 := by
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by norm_cast
  rw [div_le_iff₀ h2k, ← hcast, one_mul]
  exact_mod_cast hj

/-- The iterate vanishes where `2 ^ k * y` is an integer. -/
private theorem fract_zero_of_dyad (k j : ℕ) (y : ℝ)
    (hy : (2 : ℝ) ^ k * y = (j : ℝ)) (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    tentIter (k + 1) y = 0 := by
  have hfl : ⌊(2 : ℝ) ^ k * y⌋ = ((j : ℕ) : ℤ) := by
    rw [hy]
    exact Int.floor_natCast j
  have hfr : Int.fract ((2 : ℝ) ^ k * y) = 0 := by
    have h := Int.fract_add_floor ((2 : ℝ) ^ k * y)
    rw [hfl] at h
    push_cast at h
    linarith [hy]
  rw [tentIter_succ_eq_tent_fract k y h0 h1, hfr,
    tent_eq_two_mul _ (by norm_num) (by norm_num)]
  norm_num

/-- The iterate peaks where `2 ^ k * y` is a half-integer. -/
private theorem fract_one_of_dyad (k j : ℕ) (y : ℝ)
    (hy : (2 : ℝ) ^ k * y = (j : ℝ) + 1 / 2) (h0 : 0 ≤ y)
    (h1 : y ≤ 1) : tentIter (k + 1) y = 1 := by
  have hfl : ⌊(2 : ℝ) ^ k * y⌋ = ((j : ℕ) : ℤ) := by
    rw [hy, Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hfr : Int.fract ((2 : ℝ) ^ k * y) = 1 / 2 := by
    have h := Int.fract_add_floor ((2 : ℝ) ^ k * y)
    rw [hfl] at h
    push_cast at h
    linarith [hy]
  rw [tentIter_succ_eq_tent_fract k y h0 h1, hfr,
    tent_eq_two_mul _ (by norm_num) (by norm_num)]
  norm_num

/-- Difference of two affine functions over a half-tooth. -/
private theorem tooth_half_ge (f g : ℝ → ℝ) (u v : ℝ)
    (cf cg sf sg : ℝ) (huv : u ≤ v) (w : ℝ) (hw : v - u = w)
    (hf : ∀ t ∈ Set.Icc u v, f t = cf + sf * (t - u))
    (hg : ∀ t ∈ Set.Icc u v, g t = cg + sg * (t - u))
    (hcont : ContinuousOn (fun x => f x - g x) (Set.Icc u v)) :
    w * (|f u - g u| + |f v - g v|) / 4 ≤
      ∫ t in u..v, |f t - g t| := by
  have heq : ∀ t ∈ Set.Icc u v,
      (fun x => f x - g x) t = (cf - cg) + (sf - sg) * (t - u) := by
    intro t ht
    change f t - g t = (cf - cg) + (sf - sg) * (t - u)
    rw [hf t ht, hg t ht]
    ring
  have hmain := integral_abs_affine_half (fun x => f x - g x) u v
    (cf - cg) (sf - sg) huv heq hcont
  simpa only [hw] using hmain

/-- The iterate is affine on the rising half of each tooth. -/
private theorem tooth_left_affine (k j : ℕ) (aj mid : ℝ)
    (haj : (2 : ℝ) ^ k * aj = (j : ℝ))
    (hmid : (2 : ℝ) ^ k * mid = (j : ℝ) + 1 / 2)
    (_hlo : aj ≤ mid) (ha0 : 0 ≤ aj) (hm1 : mid ≤ 1) :
    ∀ t ∈ Set.Icc aj mid,
      tentIter (k + 1) t = 0 + ((2 : ℝ) ^ k * 2) * (t - aj) := by
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  intro t ht
  have ht0 : 0 ≤ t := le_trans ha0 ht.1
  have ht1 : t ≤ 1 := le_trans ht.2 hm1
  have hlo' : (j : ℝ) ≤ (2 : ℝ) ^ k * t := by
    have h := mul_le_mul_of_nonneg_left ht.1 (le_of_lt h2k)
    rw [haj] at h
    exact h
  have hhi' : (2 : ℝ) ^ k * t ≤ (j : ℝ) + 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left ht.2 (le_of_lt h2k)
    rw [hmid] at h
    exact h
  have hfl : ⌊(2 : ℝ) ^ k * t⌋ = ((j : ℕ) : ℤ) := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith [hlo', hhi']
  have hfr : Int.fract ((2 : ℝ) ^ k * t)
      = (2 : ℝ) ^ k * t - (j : ℝ) := by
    have h := Int.fract_add_floor ((2 : ℝ) ^ k * t)
    rw [hfl] at h
    push_cast at h
    linarith
  have hf0 : 0 ≤ (2 : ℝ) ^ k * t - (j : ℝ) := by linarith [hlo']
  have hf1 : (2 : ℝ) ^ k * t - (j : ℝ) ≤ 1 / 2 := by
    linarith [hhi']
  rw [tentIter_succ_eq_tent_fract k t ht0 ht1, hfr,
    tent_eq_two_mul _ hf0 hf1]
  linear_combination 2 * haj

/-- The iterate is affine on the falling half of each tooth. -/
private theorem tooth_right_affine (k j : ℕ) (aj bj mid : ℝ)
    (haj : (2 : ℝ) ^ k * aj = (j : ℝ))
    (hbj : (2 : ℝ) ^ k * bj = ((j + 1 : ℕ) : ℝ))
    (hmid : (2 : ℝ) ^ k * mid = (j : ℝ) + 1 / 2)
    (hm : mid = (aj + bj) / 2)
    (ha0 : 0 ≤ aj) (hb1 : bj ≤ 1) (hlt : aj < bj)
    (hfbj : tentIter (k + 1) bj = 0) :
    ∀ t ∈ Set.Icc mid bj,
      tentIter (k + 1) t
        = 1 + (-((2 : ℝ) ^ k * 2)) * (t - mid) := by
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hbj2 : (2 : ℝ) ^ k * bj = (j : ℝ) + 1 := by
    have h := hbj
    rw [Nat.cast_add, Nat.cast_one] at h
    exact h
  have hwidth : (2 : ℝ) ^ k * (bj - aj) = 1 := by
    linear_combination hbj2 - haj
  have hmid0 : 0 ≤ mid := by rw [hm]; linarith [ha0, hlt]
  have hmid_hi : mid ≤ bj := by rw [hm]; linarith [hlt]
  intro t ht
  have ht0 : 0 ≤ t := le_trans hmid0 ht.1
  have ht1 : t ≤ 1 := le_trans ht.2 hb1
  by_cases htb : t = bj
  · rw [htb, hfbj]
    have e : bj - mid = (bj - aj) / 2 := by rw [hm]; ring
    have hneg : (-((2 : ℝ) ^ k * 2)) * (bj - mid) = -1 := by
      rw [e]
      linear_combination -hwidth
    rw [hneg]
    norm_num
  · have hltb : t < bj := lt_of_le_of_ne ht.2 htb
    have hlo'' : (j : ℝ) + 1 / 2 ≤ (2 : ℝ) ^ k * t := by
      have h := mul_le_mul_of_nonneg_left ht.1 (le_of_lt h2k)
      rw [hmid] at h
      exact h
    have htb'' : (2 : ℝ) ^ k * t < (j : ℝ) + 1 := by
      have h := mul_lt_mul_of_pos_left hltb h2k
      rw [hbj2] at h
      exact h
    have hfl : ⌊(2 : ℝ) ^ k * t⌋ = ((j : ℕ) : ℤ) := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith [hlo'', htb'']
    have hfr : Int.fract ((2 : ℝ) ^ k * t)
        = (2 : ℝ) ^ k * t - (j : ℝ) := by
      have h := Int.fract_add_floor ((2 : ℝ) ^ k * t)
      rw [hfl] at h
      push_cast at h
      linarith
    have hf0 : 1 / 2 ≤ (2 : ℝ) ^ k * t - (j : ℝ) := by
      linarith [hlo'']
    have hf1 : (2 : ℝ) ^ k * t - (j : ℝ) ≤ 1 := by
      linarith [htb'']
    rw [tentIter_succ_eq_tent_fract k t ht0 ht1, hfr,
      tent_eq_two_sub _ hf0 hf1]
    linear_combination -2 * hmid

/-- Each tooth free of breakpoints contributes `1 / (4 * 2 ^ k)`. -/
private theorem tooth_integral_ge (k j : ℕ) (g : ℝ → ℝ)
    (s : Finset ℝ)
    (hsec : ∀ x y z : ℝ, x ≤ y → y ≤ z →
      (∀ p ∈ s, ¬(x < p ∧ p < z)) →
      (g y - g x) * (z - x) = (g z - g x) * (y - x))
    (hcont : Continuous (fun x => tentIter (k + 1) x - g x))
    (aj bj mid : ℝ)
    (haj : (2 : ℝ) ^ k * aj = (j : ℝ))
    (hbj : (2 : ℝ) ^ k * bj = ((j + 1 : ℕ) : ℝ))
    (hmid : (2 : ℝ) ^ k * mid = (j : ℝ) + 1 / 2)
    (hm : mid = (aj + bj) / 2)
    (hlt : aj < bj) (ha0 : 0 ≤ aj) (hb1 : bj ≤ 1)
    (hgood : ∀ p ∈ s, ¬(aj < p ∧ p < bj)) :
    1 / (4 * (2 : ℝ) ^ k) ≤
      ∫ x in aj..bj, |tentIter (k + 1) x - g x| := by
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hne : bj - aj ≠ 0 := ne_of_gt (sub_pos.mpr hlt)
  have hmid_lo : aj ≤ mid := by rw [hm]; linarith [hlt]
  have hmid_hi : mid ≤ bj := by rw [hm]; linarith [hlt]
  have hmid0 : 0 ≤ mid := le_trans ha0 hmid_lo
  have hmid1 : mid ≤ 1 := le_trans hmid_hi hb1
  have haj1 : aj ≤ 1 := le_trans hlt.le hb1
  have hbj0 : 0 ≤ bj := le_trans ha0 hlt.le
  have hfaj : tentIter (k + 1) aj = 0 :=
    fract_zero_of_dyad k j aj haj ha0 haj1
  have hfbj : tentIter (k + 1) bj = 0 :=
    fract_zero_of_dyad k (j + 1) bj hbj hbj0 hb1
  have hfmid : tentIter (k + 1) mid = 1 :=
    fract_one_of_dyad k j mid hmid hmid0 hmid1
  have hsdiv : ((g bj - g aj) / (bj - aj)) * (bj - aj)
      = g bj - g aj := div_mul_cancel₀ _ hne
  have heq : ∀ t ∈ Set.Icc aj bj,
      g t = g aj + ((g bj - g aj) / (bj - aj)) * (t - aj) := by
    intro t ht
    have hsec_app := hsec aj t bj ht.1 ht.2 hgood
    have hmul : (g t - g aj) * (bj - aj)
        = (((g bj - g aj) / (bj - aj)) * (t - aj)) * (bj - aj) := by
      linear_combination hsec_app - (t - aj) * hsdiv
    have hcancel := mul_right_cancel₀ hne hmul
    linarith [hcancel]
  have hgl : ∀ t ∈ Set.Icc aj mid,
      g t = g aj + ((g bj - g aj) / (bj - aj)) * (t - aj) :=
    fun t ht => heq t ⟨ht.1, ht.2.trans hmid_hi⟩
  have hgr : ∀ t ∈ Set.Icc mid bj,
      g t = g mid + ((g bj - g aj) / (bj - aj)) * (t - mid) := by
    intro t ht
    have e1 := heq t ⟨hmid_lo.trans ht.1, ht.2⟩
    have e2 := heq mid ⟨hmid_lo, hmid_hi⟩
    have hdist : ((g bj - g aj) / (bj - aj)) * (t - aj)
        = ((g bj - g aj) / (bj - aj)) * (t - mid)
          + ((g bj - g aj) / (bj - aj)) * (mid - aj) := by ring
    linarith [e1, e2, hdist]
  have hhalfm : mid - aj = (bj - aj) / 2 := by rw [hm]; ring
  have hlen2 : bj - mid = (bj - aj) / 2 := by rw [hm]; ring
  have hgm : g mid = (g aj + g bj) / 2 := by
    have e := heq mid ⟨hmid_lo, hmid_hi⟩
    have hs2 : ((g bj - g aj) / (bj - aj)) * ((bj - aj) / 2)
        = (g bj - g aj) / 2 := by
      rw [show ((g bj - g aj) / (bj - aj)) * ((bj - aj) / 2)
        = (((g bj - g aj) / (bj - aj)) * (bj - aj)) / 2 from by ring,
        hsdiv]
    rw [hhalfm] at e
    rw [hs2] at e
    linarith [e]
  have hfl := tooth_left_affine k j aj mid haj hmid hmid_lo ha0 hmid1
  have hfr := tooth_right_affine k j aj bj mid haj hbj hmid hm
    ha0 hb1 hlt hfbj
  have hcontG : ContinuousOn (fun x => tentIter (k + 1) x - g x)
      (Set.Icc aj bj) := hcont.continuousOn
  have hH1 := tooth_half_ge (tentIter (k + 1)) g aj mid 0 (g aj)
    ((2 : ℝ) ^ k * 2) ((g bj - g aj) / (bj - aj)) hmid_lo
    ((bj - aj) / 2) hhalfm hfl hgl
    (hcontG.mono (fun t ht => ⟨ht.1, ht.2.trans hmid_hi⟩))
  have hH2 := tooth_half_ge (tentIter (k + 1)) g mid bj 1 (g mid)
    (-((2 : ℝ) ^ k * 2)) ((g bj - g aj) / (bj - aj)) hmid_hi
    ((bj - aj) / 2) hlen2 hfr hgr
    (hcontG.mono (fun t ht => ⟨hmid_lo.trans ht.1, ht.2⟩))
  have hI1 : IntervalIntegrable (fun t => |tentIter (k + 1) t - g t|)
      MeasureTheory.volume aj mid :=
    ContinuousOn.intervalIntegrable_of_Icc hmid_lo
      hcont.abs.continuousOn
  have hI2 : IntervalIntegrable (fun t => |tentIter (k + 1) t - g t|)
      MeasureTheory.volume mid bj :=
    ContinuousOn.intervalIntegrable_of_Icc hmid_hi
      hcont.abs.continuousOn
  have hadj : (∫ t in aj..mid, |tentIter (k + 1) t - g t|)
      + (∫ t in mid..bj, |tentIter (k + 1) t - g t|)
      = ∫ t in aj..bj, |tentIter (k + 1) t - g t| :=
    intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hsum := add_le_add hH1 hH2
  rw [hadj] at hsum
  have ehl : tentIter (k + 1) aj - g aj = -(g aj) := by
    rw [hfaj]; ring
  have ehr : tentIter (k + 1) bj - g bj = -(g bj) := by
    rw [hfbj]; ring
  have ehm : tentIter (k + 1) mid - g mid
      = 1 - (g aj + g bj) / 2 := by rw [hfmid, hgm]
  have h2hm : 2 * |1 - (g aj + g bj) / 2|
      = |2 - g aj - g bj| := by
    rw [show (2 : ℝ) - g aj - g bj
      = 2 * (1 - (g aj + g bj) / 2) from by ring,
      abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have htri : (2 : ℝ) ≤ |g aj| + |2 - g aj - g bj| + |g bj| := by
    have t1 : |g aj + g bj| ≤ |g aj| + |g bj| := abs_add_le _ _
    have t2 : |(g aj + g bj) + (2 - (g aj + g bj))|
        ≤ |g aj + g bj| + |2 - (g aj + g bj)| := abs_add_le _ _
    have e : (g aj + g bj) + (2 - (g aj + g bj)) = 2 := by ring
    rw [e, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] at t2
    have e3 : (2 : ℝ) - g aj - g bj = 2 - (g aj + g bj) := by ring
    rw [e3]
    linarith [t1, t2]
  have hS : (2 : ℝ) ≤ |tentIter (k + 1) aj - g aj|
      + 2 * |tentIter (k + 1) mid - g mid|
      + |tentIter (k + 1) bj - g bj| := by
    rw [ehl, ehr, ehm, abs_neg, abs_neg, h2hm]
    exact htri
  have hnn : (0 : ℝ) ≤ (bj - aj) / 2 := by linarith [hlt]
  have hmul := mul_le_mul_of_nonneg_left hS hnn
  have eL : ((bj - aj) / 2)
        * (|tentIter (k + 1) aj - g aj|
          + |tentIter (k + 1) mid - g mid|) / 4
      + ((bj - aj) / 2)
        * (|tentIter (k + 1) mid - g mid|
          + |tentIter (k + 1) bj - g bj|) / 4
      = ((bj - aj) / 2)
        * (|tentIter (k + 1) aj - g aj|
          + 2 * |tentIter (k + 1) mid - g mid|
          + |tentIter (k + 1) bj - g bj|) / 4 := by ring
  have eR : ((bj - aj) / 2) * 2 / 4 = (bj - aj) / 4 := by ring
  have hle : ((bj - aj) / 2) * 2 / 4
      ≤ ((bj - aj) / 2)
        * (|tentIter (k + 1) aj - g aj|
          + 2 * |tentIter (k + 1) mid - g mid|
          + |tentIter (k + 1) bj - g bj|) / 4 := by
    linarith [hmul]
  rw [eR, ← eL] at hle
  have hfin : (bj - aj) / 4 ≤
      ∫ x in aj..bj, |tentIter (k + 1) x - g x| :=
    hle.trans hsum
  have hbj2 : (2 : ℝ) ^ k * bj = (j : ℝ) + 1 := by
    have h := hbj
    rw [Nat.cast_add, Nat.cast_one] at h
    exact h
  have hwidth : (2 : ℝ) ^ k * (bj - aj) = 1 := by
    linear_combination hbj2 - haj
  have hfin2 : (bj - aj) / 4 = 1 / (4 * (2 : ℝ) ^ k) := by
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    have hW : 4 * (2 : ℝ) ^ k ≠ 0 := by positivity
    rw [div_eq_div_iff h4 hW]
    linear_combination 4 * hwidth
  rw [hfin2] at hfin
  exact hfin

/-- The integral over `[0, m / 2 ^ k]` splits over dyadic teeth. -/
private theorem integral_split_dyadic (f g : ℝ → ℝ) (k : ℕ)
    (hcont : Continuous (fun x => |f x - g x|)) (m : ℕ) :
    ∫ x in (0 : ℝ)..((m : ℝ) / (2 : ℝ) ^ k), |f x - g x|
      = ∑ j ∈ Finset.range m,
        ∫ x in ((j : ℝ) / (2 : ℝ) ^ k)..
          (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k), |f x - g x| := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_div,
      intervalIntegral.integral_same, Finset.sum_range_zero]
  | succ m ih =>
    show ∫ x in (0 : ℝ)..(((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k),
          |f x - g x|
        = ∑ j ∈ Finset.range (m + 1),
          ∫ x in ((j : ℝ) / (2 : ℝ) ^ k)..
            (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k), |f x - g x|
    have h0m : (0 : ℝ) ≤ (m : ℝ) / (2 : ℝ) ^ k := by positivity
    have hmm : (m : ℝ) / (2 : ℝ) ^ k
        ≤ (((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k) :=
      (dyad_strictMono k m (m + 1) (by omega)).le
    have hI1 : IntervalIntegrable (fun x => |f x - g x|)
        MeasureTheory.volume 0 ((m : ℝ) / (2 : ℝ) ^ k) :=
      ContinuousOn.intervalIntegrable_of_Icc h0m
        hcont.continuousOn
    have hI2 : IntervalIntegrable (fun x => |f x - g x|)
        MeasureTheory.volume ((m : ℝ) / (2 : ℝ) ^ k)
        (((m + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k) :=
      ContinuousOn.intervalIntegrable_of_Icc hmm
        hcont.continuousOn
    have hadj := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
    simp only [Finset.sum_range_succ, ← hadj, ih]

/-- Oscillation lower bound: any function with at most `2 ^ (L ^ 2)`
affine pieces stays `1 / 32` away in `L1` from the deep tent iterate. -/
theorem tentIter_l1_ge_of_piecesLE (L : ℕ) (_hL : 2 ≤ L) (g : ℝ → ℝ)
    {n : ℕ} (hP : PiecesLE n g) (hn : (n : ℝ) ≤ (2 : ℝ) ^ (L ^ 2)) :
    (1 / 32 : ℝ) ≤ ∫ x in (0 : ℝ)..1, |tentIter (L ^ 2 + 2) x - g x| := by
  classical
  have hk2 : L ^ 2 + 2 = (L ^ 2 + 1) + 1 := by omega
  rw [hk2]
  have hcont : Continuous
      (fun x => tentIter ((L ^ 2 + 1) + 1) x - g x) :=
    (continuous_tentIter _).sub (piecesLE_continuous hP)
  obtain ⟨s, hcard, hsec⟩ := hP
  have hcontAbs : Continuous
      (fun x => |tentIter ((L ^ 2 + 1) + 1) x - g x|) := hcont.abs
  have hper : ∀ j ∈ (Finset.range (2 ^ (L ^ 2 + 1))).filter
      (fun (j : ℕ) => ∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
        p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)))),
      1 / (4 * (2 : ℝ) ^ (L ^ 2 + 1)) ≤ ∫ x in
        ((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))..
        (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)),
        |tentIter ((L ^ 2 + 1) + 1) x - g x| := by
    intro j hj
    have hgood : ∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
        p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))) :=
      (Finset.mem_filter.mp hj).2
    have hjlt : j < 2 ^ (L ^ 2 + 1) :=
      Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hj1 : j + 1 ≤ 2 ^ (L ^ 2 + 1) := by omega
    have ha0 : (0 : ℝ) ≤ (j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) := by
      positivity
    have hb1 : ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) ≤ 1 :=
      dyad_le_one _ _ hj1
    have hlt : (j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)
        < ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) :=
      dyad_strictMono _ _ _ (by omega)
    have haj := dyad_mul (L ^ 2 + 1) j
    have hbj := dyad_mul (L ^ 2 + 1) (j + 1)
    have hmeq : (2 : ℝ) ^ (L ^ 2 + 1)
        * ((((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))
          + (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))) / 2)
        = (j : ℝ) + 1 / 2 := by
      have hr : (2 : ℝ) ^ (L ^ 2 + 1)
          * ((((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))
            + (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))) / 2)
          = (((2 : ℝ) ^ (L ^ 2 + 1)
            * ((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)))
            + (2 : ℝ) ^ (L ^ 2 + 1)
              * (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))) / 2 := by
        ring
      rw [hr, haj, hbj, Nat.cast_add, Nat.cast_one]
      ring
    exact tooth_integral_ge (L ^ 2 + 1) j g s hsec hcont
      ((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))
      (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))
      ((((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))
        + (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))) / 2)
      haj hbj hmeq rfl hlt ha0 hb1 hgood
  have hex : ∀ j ∈ (Finset.range (2 ^ (L ^ 2 + 1))).filter
        (fun (j : ℕ) => ¬∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
          p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)))),
        ∃ p ∈ s, (j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
          p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)) := by
    intro j hj
    have hne : ¬∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
        p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))) :=
      (Finset.mem_filter.mp hj).2
    by_contra hcon
    push Not at hcon
    exact hne (fun p hps h => (not_le_of_gt h.2) (hcon p hps h.1))
  have hne : ∀ j ∈ (Finset.range (2 ^ (L ^ 2 + 1))).filter
        (fun (j : ℕ) => ¬∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
          p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)))),
        (s.filter (fun p => (j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
          p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)))).Nonempty := by
    intro j hj
    obtain ⟨p, hps, hpb⟩ := hex j hj
    exact ⟨p, Finset.mem_filter.mpr ⟨hps, hpb⟩⟩
  have hinj : Function.Injective
      (fun a : ↥((Finset.range (2 ^ (L ^ 2 + 1))).filter
          (fun (j : ℕ) => ¬∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
            p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))) =>
        (⟨Finset.min' (s.filter (fun p => (a.1 : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
            p < (((a.1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))
            (hne a.1 a.2),
          (Finset.mem_filter.mp
            (Finset.min'_mem _ _)).1⟩ : ↥s)) := by
    intro a b hab
    have hval : Finset.min' (s.filter (fun p => (a.1 : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)
          < p ∧ p < (((a.1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))
          (hne a.1 a.2)
        = Finset.min' (s.filter (fun p => (b.1 : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)
          < p ∧ p < (((b.1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))
          (hne b.1 b.2) :=
      Subtype.ext_iff.mp hab
    have hqa : (a.1 : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)
          < Finset.min' (s.filter (fun p => (a.1 : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)
            < p ∧ p < (((a.1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))
            (hne a.1 a.2) ∧
        Finset.min' (s.filter (fun p => (a.1 : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)
          < p ∧ p < (((a.1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))
          (hne a.1 a.2)
          < (((a.1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ (hne a.1 a.2))).2
    have hqb : (b.1 : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)
          < Finset.min' (s.filter (fun p => (b.1 : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)
            < p ∧ p < (((b.1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))
            (hne b.1 b.2) ∧
        Finset.min' (s.filter (fun p => (b.1 : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)
          < p ∧ p < (((b.1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))
          (hne b.1 b.2)
          < (((b.1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)) :=
      (Finset.mem_filter.mp (Finset.min'_mem _ (hne b.1 b.2))).2
    rw [← hval] at hqb
    have hab_eq : a.1 = b.1 := by
      by_contra hne_ab
      rcases lt_or_gt_of_ne hne_ab with hlt_ab | hgt_ab
      · have hle : a.1 + 1 ≤ b.1 := by omega
        rcases lt_or_eq_of_le hle with hlt2 | heq
        · have hmo := dyad_strictMono (L ^ 2 + 1) (a.1 + 1) b.1 hlt2
          linarith [hqa.2, hqb.1, hmo]
        · have heqR : ((((a.1 + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)))
              = ((b.1 : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)) := by
            rw [heq]
          linarith [hqa.2, hqb.1, heqR]
      · have hgt_ab' : b.1 < a.1 := hgt_ab
        have hle : b.1 + 1 ≤ a.1 := by omega
        rcases lt_or_eq_of_le hle with hlt2 | heq
        · have hmo := dyad_strictMono (L ^ 2 + 1) (b.1 + 1) a.1 hlt2
          linarith [hqb.2, hqa.1, hmo]
        · rw [heq] at hqb
          linarith [hqb.2, hqa.1]
    exact Subtype.ext hab_eq
  have hBs : ((Finset.range (2 ^ (L ^ 2 + 1))).filter
        (fun (j : ℕ) => ¬∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
          p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))).card
      ≤ s.card := by
    have hcard2 := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_coe, Fintype.card_coe] at hcard2
    exact hcard2
  have hGB : ((Finset.range (2 ^ (L ^ 2 + 1))).filter
          (fun (j : ℕ) => ∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
            p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))).card
        + ((Finset.range (2 ^ (L ^ 2 + 1))).filter
          (fun (j : ℕ) => ¬∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
            p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))).card
        = 2 ^ (L ^ 2 + 1) := by
    have h := Finset.sum_filter_add_sum_filter_not
      (Finset.range (2 ^ (L ^ 2 + 1)))
      (fun (j : ℕ) => ∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
        p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))
      (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, mul_one,
      Finset.card_range] at h
    exact h
  have hGN : ((Finset.range (2 ^ (L ^ 2 + 1))).filter
          (fun (j : ℕ) => ∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
            p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))).card
        + n ≥ 2 ^ (L ^ 2 + 1) + 1 := by omega
  have hGNcast : ((((Finset.range (2 ^ (L ^ 2 + 1))).filter
          (fun (j : ℕ) => ∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
            p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))).card : ℕ) : ℝ)
        + (n : ℝ) ≥ ((2 ^ (L ^ 2 + 1) : ℕ) : ℝ) + 1 := by
    exact_mod_cast hGN
  have hNcast : ((2 ^ (L ^ 2 + 1) : ℕ) : ℝ)
      = (2 : ℝ) ^ (L ^ 2 + 1) := by norm_cast
  have hPs : (2 : ℝ) ^ (L ^ 2 + 1) = (2 : ℝ) ^ (L ^ 2) * 2 :=
    pow_succ _ _
  have hPpos : (0 : ℝ) < (2 : ℝ) ^ (L ^ 2) := by positivity
  have hgP : ((((Finset.range (2 ^ (L ^ 2 + 1))).filter
          (fun (j : ℕ) => ∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
            p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))).card : ℕ) : ℝ)
      ≥ (2 : ℝ) ^ (L ^ 2) + 1 := by
    linarith [hGNcast, hNcast, hPs, hn]
  have hsplit := integral_split_dyadic (tentIter ((L ^ 2 + 1) + 1)) g
    (L ^ 2 + 1) hcontAbs (2 ^ (L ^ 2 + 1))
  have haN : (((2 ^ (L ^ 2 + 1) : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))
      = 1 := by
    have hne : (2 : ℝ) ^ (L ^ 2 + 1) ≠ 0 := by positivity
    rw [hNcast]
    exact div_self hne
  rw [haN] at hsplit
  have hdrop : (∑ j ∈ (Finset.range (2 ^ (L ^ 2 + 1))).filter
        (fun (j : ℕ) => ∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
          p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)))),
        ∫ x in ((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))..
          (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)),
        |tentIter ((L ^ 2 + 1) + 1) x - g x|)
      ≤ ∑ j ∈ Finset.range (2 ^ (L ^ 2 + 1)),
        ∫ x in ((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))..
          (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)),
        |tentIter ((L ^ 2 + 1) + 1) x - g x| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ (Finset.range (2 ^ (L ^ 2 + 1))))
      (fun j _ _ => intervalIntegral.integral_nonneg_of_forall
        (dyad_strictMono _ _ _ (by omega)).le (fun _ => abs_nonneg _))
  have hgood_ineq : ((((Finset.range (2 ^ (L ^ 2 + 1))).filter
        (fun (j : ℕ) => ∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
          p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))).card : ℕ) : ℝ)
      * (1 / (4 * (2 : ℝ) ^ (L ^ 2 + 1)))
      ≤ ∑ j ∈ (Finset.range (2 ^ (L ^ 2 + 1))).filter
        (fun (j : ℕ) => ∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
          p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)))),
        ∫ x in ((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))..
          (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1)),
        |tentIter ((L ^ 2 + 1) + 1) x - g x| := by
    have h := Finset.sum_le_sum (fun j hj => hper j hj)
    rw [Finset.sum_const, nsmul_eq_mul] at h
    exact h
  have hfin : (1 / 32 : ℝ)
      ≤ ((((Finset.range (2 ^ (L ^ 2 + 1))).filter
        (fun (j : ℕ) => ∀ p ∈ s, ¬((j : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1) < p ∧
          p < (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (L ^ 2 + 1))))).card : ℕ) : ℝ)
      * (1 / (4 * (2 : ℝ) ^ (L ^ 2 + 1))) := by
    have h4W : (0 : ℝ) < 4 * (2 : ℝ) ^ (L ^ 2 + 1) := by positivity
    have heq : ∀ G : ℝ, G * (1 / (4 * (2 : ℝ) ^ (L ^ 2 + 1)))
        = G / (4 * (2 : ℝ) ^ (L ^ 2 + 1)) := fun G => by ring
    rw [heq, le_div_iff₀ h4W]
    linarith [hgP, hPs, hPpos]
  rw [hsplit]
  exact hfin.trans (hgood_ineq.trans hdrop)

/-- Shallow-network corollary: a ReLU network with at most `L`
layers and total width at most `2 ^ L` misses the deep iterate by `1 / 32`. -/
theorem tentIter_l1_ge_of_reluNet (L : ℕ) (hL : 2 ≤ L) (d : ℕ → ℕ)
    (Nnet : Net d) (M : ℕ) (hM0 : 0 < M) (hM : M ≤ L)
    (hN : IsReluNetUpTo d Nnet M) (hd0 : d 0 = 1) (hdM : d M = 1)
    (hpos : ∀ j < M, 0 < d j)
    (hsum : ((∑ i ∈ Finset.Icc 1 M, d i) : ℝ) ≤ (2 : ℝ) ^ L) :
    (1 / 32 : ℝ) ≤ ∫ x in (0 : ℝ)..1,
      |tentIter (L ^ 2 + 2) x - (Nnet.forward M (inputVec d x)) ⟨0, by omega⟩| := by
  obtain ⟨n, hPn, hnb⟩ :=
    net_piecesLE d Nnet M hN hd0 hdM hM0 hpos
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have hSnn : (0 : ℝ) ≤ ((∑ i ∈ Finset.Icc 1 M, d i) : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hcase : (2 * ((∑ i ∈ Finset.Icc 1 M, d i) : ℝ) / (M : ℝ)) ^ M
      ≤ (2 : ℝ) ^ (L ^ 2) := by
    rcases lt_or_ge M 2 with hM1 | hM2
    · have hMeq : M = 1 := by omega
      subst hMeq
      rw [Nat.cast_one, div_one, pow_one]
      have h1 : (2 : ℝ) * ((∑ i ∈ Finset.Icc 1 1, d i) : ℝ)
          ≤ 2 * (2 : ℝ) ^ L :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
      have h2 : (2 : ℝ) * (2 : ℝ) ^ L = (2 : ℝ) ^ (L + 1) := by
        rw [pow_succ']
      have h3 : (2 : ℝ) ^ (L + 1) ≤ (2 : ℝ) ^ (L ^ 2) :=
        pow_le_pow_right₀ (by norm_num) (by nlinarith [hL])
      linarith [h1, h2, h3]
    · have h2M : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
      have hbase : (2 * ((∑ i ∈ Finset.Icc 1 M, d i) : ℝ) / (M : ℝ))
          ≤ (2 : ℝ) ^ L := by
        rw [div_le_iff₀ hMpos]
        have g1 : (2 : ℝ) * ((∑ i ∈ Finset.Icc 1 M, d i) : ℝ)
            ≤ 2 * (2 : ℝ) ^ L :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
        have g2 : (2 : ℝ) ^ L * 2 ≤ (2 : ℝ) ^ L * (M : ℝ) :=
          mul_le_mul_of_nonneg_left h2M (by positivity)
        linarith [g1, g2]
      have hnn : (0 : ℝ)
          ≤ (2 * ((∑ i ∈ Finset.Icc 1 M, d i) : ℝ) / (M : ℝ)) :=
        div_nonneg (mul_nonneg (by norm_num) hSnn) (le_of_lt hMpos)
      have hpow : ((2 * ((∑ i ∈ Finset.Icc 1 M, d i) : ℝ) / (M : ℝ))) ^ M
          ≤ ((2 : ℝ) ^ L) ^ M :=
        pow_le_pow_left₀ hnn hbase M
      have hpow2 : ((2 : ℝ) ^ L) ^ M = (2 : ℝ) ^ (L * M) := by
        rw [← pow_mul]
      have hLM : L * M ≤ L ^ 2 := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hM (Nat.zero_le L)
      have hpow3 : (2 : ℝ) ^ (L * M) ≤ (2 : ℝ) ^ (L ^ 2) :=
        pow_le_pow_right₀ (by norm_num) hLM
      linarith [hpow, hpow2, hpow3]
  exact tentIter_l1_ge_of_piecesLE L hL _ hPn (hnb.trans hcase)

/-- Depth separation (Theorem 5.1): the deep tent network computes the
`L ^ 2 + 2`-fold iterate (three ReLU nodes per block on the construction
counting convention, which counts the readout ReLU), while any shallow
ReLU network has `L1` error at least `1 / 32`. Only the displayed
identity and lower bound are claimed. -/
theorem depth_separation (L : ℕ) (hL : 2 ≤ L) (d : ℕ → ℕ) (Nnet : Net d)
    (M : ℕ) (hM0 : 0 < M) (hM : M ≤ L) (hN : IsReluNetUpTo d Nnet M)
    (hd0 : d 0 = 1) (hdM : d M = 1) (hpos : ∀ j < M, 0 < d j)
    (hsum : ((∑ i ∈ Finset.Icc 1 M, d i) : ℝ) ≤ (2 : ℝ) ^ L) :
    (∀ x : ℝ, (tentNet.forward (2 * (L ^ 2 + 2)) (single x)) 0
      = tentIter (L ^ 2 + 2) x) ∧
    (1 / 32 : ℝ) ≤ ∫ x in (0 : ℝ)..1,
      |tentIter (L ^ 2 + 2) x - (Nnet.forward M (inputVec d x)) ⟨0, by omega⟩| := by
  refine ⟨fun x => tentNet_forward _ x, ?_⟩
  exact tentIter_l1_ge_of_reluNet L hL d Nnet M hM0 hM hN hd0 hdM
    hpos hsum

end Cslib.MachineLearning.DepthSeparation
