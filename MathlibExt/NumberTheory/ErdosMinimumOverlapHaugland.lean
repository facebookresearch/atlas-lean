/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Haugland's upper bound for the minimum-overlap constant

We prove `upperBound_H1996_holds` using the 15-step example in Jan Kristian Haugland,
*The minimum overlap problem revisited* (2016), https://arxiv.org/abs/1609.08000.
The example and its complement form an admissible pair (`HauglandFifteenStep.admissible`), and
`HauglandFifteenStep.overlap_grid` computes their overlap at whole-cell translations.
Between consecutive grid translations the overlap interpolates linearly, so the bound
reduces to a finite calculation on the integer numerators of the step heights.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

-- The two propositions share the numeral instance for their denominator.
/-- **Statement of Haugland's unpublished 1993 upper bound for the minimum-overlap constant.**
The proposition that the continuous Erdős minimum-overlap constant $C_{1b}$ satisfies
$C_{1b} \le 0.385694$.

Source: Haugland, unpublished 1993; Optimization Problems, Constant 1b. -/
def upperBound_Haugland_unpublished_1993 : Prop := C₁ᵦ ≤ (385694 : ℝ) / 1000000

/-- **Statement of Haugland's 1996 upper bound for the minimum-overlap constant.** The
proposition that the continuous Erdős minimum-overlap constant $C_{1b}$ satisfies
$C_{1b} \le 0.382002$.

Source: Haugland 1996; Optimization Problems, Constant 1b. -/
def upperBound_H1996 : Prop := C₁ᵦ ≤ (382002 : ℝ) / 1000000

namespace HauglandFifteenStep

/-- **Heights of Haugland's 15-step function.** Cut $[-1, 1)$ into the fifteen cells
$[2i/15 - 1, 2(i + 1)/15 - 1)$ for $i < 15$. Haugland's 15-step function takes the value
`weight i / 10⁸` on cell $i$. The heights, given to eight decimal places, are symmetric
(`weight (14 - i) = weight i` for $i \le 14$) and vanish on cells $0$ and $14$, and
`weight i = 0` for $i \ge 15$.

Source: Jan Kristian Haugland, *The minimum overlap problem revisited* (2016),
arXiv:1609.08000, the step function with 15 steps, there on $[0, 2]$. -/
def weight : ℕ → ℕ
  | 1 | 13 => 9938602
  | 2 | 12 => 64299877
  | 3 | 11 => 36104582
  | 4 | 10 => 69536426
  | 5 | 9 => 59241335
  | 6 | 8 => 89573331
  | 7 => 92611694
  | _ => 0

private abbrev denom : ℕ := 100000000

private theorem weight_le (i : ℕ) : weight i ≤ denom := by
  unfold weight
  split <;> decide

/-- **Heights of the complement of Haugland's 15-step function.** `complement i` is
`10⁸ - weight i`, so `profile complement` is `1 - profile weight` on $[-1, 1]$.

Source: the factor $1 - f(x + k)$ of the integral (1) in Jan Kristian Haugland,
*The minimum overlap problem revisited* (2016), arXiv:1609.08000. -/
@[no_expose] def complement (i : ℕ) : ℕ := denom - weight i

private def extend (w : ℕ → ℕ) (i : ℤ) : ℕ :=
  if 0 ≤ i ∧ i < 15 then w i.toNat else 0

private def coeff (i : ℕ) (k : ℤ) : ℕ :=
  weight i * extend complement (i + k)

private def score (k : ℤ) : ℕ := ∑ i ∈ Finset.range 15, coeff i k

private theorem score_le (k : ℤ) (hk : -15 ≤ k) (hk' : k ≤ 16) :
    score k ≤ 28614866118568434 := by
  interval_cases k <;> decide

private noncomputable def edge (i : ℝ) : ℝ := 2 * i / 15 - 1

/-- **Fifteen-step functions on $[-1, 1]$.** For heights `w : ℕ → ℕ` in units of $10^{-8}$,
`profile w` vanishes outside $[-1, 1]$, takes the value `w i / 10⁸` on the cell
$[2i/15 - 1, 2(i + 1)/15 - 1)$ for $i < 15$, and takes the value `w 15 / 10⁸` at $1$.
Haugland's 15-step function is `profile weight`.

Source: the step functions with $n$ steps in Jan Kristian Haugland, *The minimum overlap problem
revisited* (2016), arXiv:1609.08000, moved from $[0, 2]$ to $[-1, 1]$. -/
@[no_expose] noncomputable def profile (w : ℕ → ℕ) : ℝ → ℝ :=
  continuousSupportInterval.indicator fun t => (w ⌊(t + 1) * 15 / 2⌋.toNat : ℝ) / denom

private theorem profile_measurable (w : ℕ → ℕ) : Measurable (profile w) := by
  apply Measurable.indicator _ measurableSet_Icc
  exact (measurable_of_countable (fun i : ℤ => (w i.toNat : ℝ) / denom)).comp
    (Int.measurable_floor.comp (by fun_prop))

private theorem profile_range {w : ℕ → ℕ} (hw : ∀ i, w i ≤ denom) (t : ℝ) :
    profile w t ∈ Icc (0 : ℝ) 1 := by
  by_cases ht : t ∈ continuousSupportInterval
  · simp only [profile, indicator_of_mem ht, mem_Icc]
    exact ⟨by positivity, (div_le_one (by norm_num)).2 (by exact_mod_cast hw _)⟩
  · simp [profile, ht]

private theorem profile_outside (w : ℕ → ℕ) (t : ℝ) (ht : t ∉ continuousSupportInterval) :
    profile w t = 0 := indicator_of_notMem ht _

private theorem profile_cell (w : ℕ → ℕ) {t : ℝ} {j : ℤ}
    (h₁ : edge j < t) (h₂ : t < edge (j + 1)) :
    profile w t = (extend w j : ℝ) / denom := by
  unfold edge at h₁ h₂
  have hj : ⌊(t + 1) * 15 / 2⌋ = j := Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
  by_cases h : 0 ≤ j ∧ j < 15
  · have hl : (0 : ℝ) ≤ j := by exact_mod_cast h.1
    have hu : (j : ℝ) ≤ 14 := by exact_mod_cast (show j ≤ 14 by omega)
    have ht : t ∈ continuousSupportInterval := ⟨by linarith, by linarith⟩
    simp [profile, ht, hj, extend, h]
  · have ht : t ∉ continuousSupportInterval := by
      rintro ⟨hl, hu⟩
      rcases le_or_gt 15 j with hj' | hj'
      · have : (15 : ℝ) ≤ j := by exact_mod_cast hj'
        linarith
      · have : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
        linarith
    simp [profile, ht, extend, h]

private theorem integral_grid {p : ℝ → ℝ} (hp : ∀ a b, IntervalIntegrable p volume a b) :
    (∫ t in continuousSupportInterval, p t) =
      ∑ i ∈ Finset.range 15, ∫ t in edge i..edge (i + 1), p t := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (n := 15)
    (a := fun i : ℕ => edge i) (fun i _ => hp _ _)
  rw [show continuousSupportInterval = Icc (-1 : ℝ) 1 from rfl, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num [edge] at h ⊢
  exact h.symm

private theorem integral_const_on {p : ℝ → ℝ} {a b v : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Ioo a b, p t = v) : (∫ t in a..b, p t) = (b - a) * v := by
  rw [intervalIntegral.integral_congr_Ioo_of_le hab (g := fun _ => v) h,
    intervalIntegral.integral_const, smul_eq_mul]

private theorem bounded_intervalIntegrable {p : ℝ → ℝ} (hm : Measurable p)
    (hr : ∀ t, p t ∈ Icc (0 : ℝ) 1) (a b : ℝ) : IntervalIntegrable p volume a b := by
  apply intervalIntegrable_iff.mpr
  apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne hm.aestronglyMeasurable
  filter_upwards with t
  simpa [Real.norm_eq_abs, abs_of_nonneg (hr t).1] using (hr t).2

private theorem weight_cell {i : ℕ} (hi : i < 15) {t : ℝ}
    (h₁ : edge i < t) (h₂ : t < edge (i + 1)) : profile weight t = (weight i : ℝ) / denom := by
  simpa [extend, hi] using profile_cell weight (j := (i : ℤ)) (t := t)
    (by simpa using h₁) (by simpa using h₂)

/-- **Haugland's 15-step pair is admissible.** Haugland's 15-step function `profile weight` and
its complement `profile complement` form an admissible pair for the continuous minimum-overlap
problem; in particular `profile weight` has integral $1$.

Source: Jan Kristian Haugland, *The minimum overlap problem revisited* (2016),
arXiv:1609.08000. -/
theorem admissible : ContinuousAdmissible (profile weight) (profile complement) := by
  have hr := profile_range weight_le
  refine ⟨(profile_measurable _).aemeasurable, (profile_measurable _).aemeasurable, hr,
    profile_range (fun i => Nat.sub_le denom (weight i)), profile_outside _, profile_outside _,
    ?_, ?_⟩
  · intro t ht
    simp only [profile, indicator_of_mem ht, complement, Nat.cast_sub (weight_le _)]
    norm_num [denom]
    ring
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (profile_outside weight),
      integral_grid (bounded_intervalIntegrable (profile_measurable _) hr)]
    have hmass : ∑ i ∈ Finset.range 15, weight i = 750000000 := by decide
    calc
      _ = ∑ i ∈ Finset.range 15, (2 / 15 / denom : ℝ) * weight i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [integral_const_on (v := (weight i : ℝ) / denom) (by dsimp [edge]; linarith)
          (fun t ht => weight_cell (Finset.mem_range.mp hi) ht.1 ht.2)]
        unfold edge
        ring
      _ = 1 := by rw [← Finset.mul_sum, ← Nat.cast_sum, hmass]; norm_num

private noncomputable abbrev integrand (x : ℝ) :=
  continuousOverlapIntegrand (profile weight) (profile complement) x

private theorem integrand_intervalIntegrable (x a b : ℝ) :
    IntervalIntegrable (integrand x) volume a b := by
  apply bounded_intervalIntegrable
  · exact (profile_measurable _).mul ((profile_measurable _).comp (measurable_const_add x))
  · intro t
    exact ⟨mul_nonneg (admissible.range_f t).1 (admissible.range_g (x + t)).1,
      (mul_le_mul_of_nonneg_right (admissible.range_f t).2
        (admissible.range_g (x + t)).1).trans (by simpa using (admissible.range_g (x + t)).2)⟩

private theorem integrand_on {i : ℕ} (hi : i < 15) {j : ℤ} {x t : ℝ}
    (ht : t ∈ Ioo (edge i) (edge (i + 1)))
    (hs : x + t ∈ Ioo (edge (i + j : ℤ)) (edge ((i + j : ℤ) + 1 : ℝ))) :
    integrand x t = (coeff i j : ℝ) / denom ^ 2 := by
  unfold integrand continuousOverlapIntegrand coeff
  rw [weight_cell hi ht.1 ht.2, profile_cell complement hs.1 hs.2, Nat.cast_mul]
  ring

-- A fractional grid displacement splits each cell into two constant pieces.
private theorem cell_integral (i : ℕ) (hi : i < 15) (k : ℤ) (q x : ℝ)
    (hq : 0 ≤ q) (hq' : q ≤ 1) (hx : x = 2 * (k + q) / 15) :
    (∫ t in edge i..edge (i + 1), integrand x t) =
      (2 / 15 / denom ^ 2) *
        ((1 - q) * (coeff i k : ℝ) + q * (coeff i (k + 1) : ℝ)) := by
  let b := edge (i + 1 - q)
  have h₁ : edge i ≤ b := by dsimp [b, edge]; linarith
  have h₂ : b ≤ edge (i + 1) := by dsimp [b, edge]; linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := b)
    (integrand_intervalIntegrable x _ _) (integrand_intervalIntegrable x _ _)]
  rw [integral_const_on (v := (coeff i k : ℝ) / denom ^ 2) h₁ ?_,
    integral_const_on (v := (coeff i (k + 1) : ℝ) / denom ^ 2) h₂ ?_]
  · dsimp [b, edge]
    ring
  · rintro t ⟨ht, ht'⟩
    apply integrand_on hi ⟨h₁.trans_lt ht, ht'⟩
    dsimp [b, edge] at ht ht' ⊢
    push_cast
    constructor <;> linarith
  · rintro t ⟨ht, ht'⟩
    apply integrand_on hi ⟨ht, ht'.trans_le h₂⟩
    dsimp [b, edge] at ht ht' ⊢
    push_cast
    constructor <;> linarith

-- At a whole-cell translation each cell contributes a single constant piece.
private theorem overlap_cells (k : ℤ) :
    continuousOverlap (profile weight) (profile complement) (2 * k / 15) =
      (2 / 15 / denom ^ 2) * (score k : ℝ) := by
  calc
    _ = ∑ i ∈ Finset.range 15, ∫ t in edge i..edge (i + 1), integrand (2 * k / 15) t :=
      integral_grid (integrand_intervalIntegrable _)
    _ = _ := by
      simp only [score, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [cell_integral i (Finset.mem_range.mp hi) k 0 _ le_rfl zero_le_one (by ring)]
      ring

-- For a nonnegative shift only the cells `i < 15 - k` meet the support of the complement.
private theorem score_natCast (k : ℕ) :
    score k = ∑ i ∈ Finset.range (15 - k), weight i * complement (i + k) := by
  rw [score, ← Finset.sum_range_add_sum_Ico _ (Nat.sub_le 15 k),
    Finset.sum_eq_zero (s := Finset.Ico (15 - k) 15), add_zero]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.mp hi
    rw [coeff, extend, ite_eq_left (by omega), ← Nat.cast_add, Int.toNat_natCast]
  · intro i hi
    have hi := Finset.mem_Ico.mp hi
    rw [coeff, extend, ite_eq_right (by omega), mul_zero]

/-- **Overlaps of Haugland's 15-step pair at whole-cell translations.** Write $h_i$ for
`weight i / 10⁸`. For a natural number $k$, the overlap of Haugland's 15-step function and its
complement at the translation $x = 2k/15$ by $k$ cells is
$\frac{2}{15} \sum_{i < 15 - k} h_i (1 - h_{i + k})$.

Source: the integral (1) in Jan Kristian Haugland, *The minimum overlap problem revisited*
(2016), arXiv:1609.08000, computed cell by cell. -/
theorem overlap_grid (k : ℕ) :
    continuousOverlap (profile weight) (profile complement) (2 * k / 15) =
      2 / 15 * ∑ i ∈ Finset.range (15 - k),
        (weight i : ℝ) / 10 ^ 8 * (1 - (weight (i + k) : ℝ) / 10 ^ 8) := by
  have h := overlap_cells k
  rw [Int.cast_natCast] at h
  rw [h, score_natCast, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_mul, complement, Nat.cast_sub (weight_le _)]
  simp only [denom, Nat.cast_ofNat]
  ring

private theorem overlap_le {x : ℝ} (hx : x ∈ continuousTranslationInterval) :
    continuousOverlap (profile weight) (profile complement) x ≤ (382002 : ℝ) / 1000000 := by
  let k := ⌊x * 15 / 2⌋
  let q := x * 15 / 2 - k
  have hfloor := Int.floor_le (x * 15 / 2)
  have hnext := Int.lt_floor_add_one (x * 15 / 2)
  change (k : ℝ) ≤ _ at hfloor
  change _ < (k : ℝ) + 1 at hnext
  have hq : 0 ≤ q := sub_nonneg.mpr hfloor
  have hq' : q ≤ 1 := by dsimp [q]; linarith
  obtain ⟨hl, hu⟩ := hx
  have hk : -15 ≤ k := Int.le_floor.mpr (by push_cast; linarith)
  have hk' : k ≤ 15 := by exact_mod_cast (show (k : ℝ) ≤ 15 by linarith)
  have bound (j : ℤ) (h₁ : -15 ≤ j) (h₂ : j ≤ 16) :
      (score j : ℝ) ≤ 28614866118568434 := by exact_mod_cast score_le j h₁ h₂
  have hc := add_le_add
    (mul_le_mul_of_nonneg_left (bound k hk (by omega)) (sub_nonneg.mpr hq'))
    (mul_le_mul_of_nonneg_left (bound (k + 1) (by omega) (by omega)) hq)
  calc
    _ = ∑ i ∈ Finset.range 15, ∫ t in edge i..edge (i + 1), integrand x t :=
      integral_grid (integrand_intervalIntegrable x)
    _ = (2 / 15 / denom ^ 2) * ((1 - q) * (score k : ℝ) + q * (score (k + 1) : ℝ)) := by
      simp only [score, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => cell_integral i (Finset.mem_range.mp hi) k q x
        hq hq' (by dsimp [q]; ring)
    _ ≤ (2 / 15 / denom ^ 2) * (28614866118568434 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ _ := hc
        _ = _ := by ring
    _ ≤ _ := by norm_num [denom]

end HauglandFifteenStep

/-- **Haugland's 1996 upper bound for the minimum-overlap constant.** The continuous Erdős
minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 0.382002$.

Source: Haugland 1996 and Optimization Problems 1b. -/
theorem upperBound_H1996_holds : upperBound_H1996 := by
  refine (continuousMinimumOverlapConstant_isUniversalLowerBound _ _
    HauglandFifteenStep.admissible).trans ?_
  apply csSup_le (continuousOverlapValues_nonempty _ _)
  rintro _ ⟨x, hx, rfl⟩
  exact HauglandFifteenStep.overlap_le hx

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
