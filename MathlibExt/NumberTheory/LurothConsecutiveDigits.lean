/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LurothBorelBernstein
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Set.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Upper bound for a Lüroth digit superlevel set

The theorem `MetaMathlibExt.volume_lurothDigits_ge_le` bounds the Lebesgue measure of
`{x ∈ (0, 1] : F (d₁ x, …, dₘ x) ≥ y}` by `3 ^ m` times the integral of `∏ xᵢ⁻²` over the
superlevel set of `F` on `[2, ∞)^m`, for `F` non-decreasing there for the coordinatewise
order.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MetaMathlibExt
namespace volume_lurothDigits_ge_le

private abbrev unitInterval := Set.Ioc (0 : ℝ) 1
private noncomputable abbrev μ : Measure ℝ := volume.restrict unitInterval

private theorem prob_univ : μ Set.univ = 1 := by
  simp [μ, unitInterval]

private theorem measurable_digit : Measurable lurothDigit := by
  unfold lurothDigit
  fun_prop

private theorem measurable_map : Measurable lurothMap := by
  unfold lurothMap
  have hd : Measurable fun x => (lurothDigit x : ℝ) :=
    (measurable_of_countable ((↑) : ℕ → ℝ)).comp measurable_digit
  fun_prop

private theorem measurable_seq (n : ℕ) : Measurable fun x => lurothDigitSeq x n :=
  measurable_digit.comp (measurable_map.iterate n)

private theorem digit_gt_one {y : ℝ} (hy : y ∈ Set.Ioc 0 1) : 1 < lurothDigit y :=
  Nat.lt_add_one_iff.mpr <| (Nat.one_le_floor_iff _).2 <|
    (le_div_iff₀ hy.1).2 (by simpa using hy.2)

private theorem mapsTo : Set.MapsTo lurothMap (Set.Ioc 0 1) (Set.Ioc 0 1) := by
  intro y hy
  let a : ℝ := ⌊1 / y⌋₊
  have ha : 0 < a := by
    exact Nat.cast_pos.mpr (Nat.succ_lt_succ_iff.mp (digit_gt_one hy))
  have hlo : a * y ≤ 1 := (le_div_iff₀ hy.1).1 (Nat.floor_le (one_div_nonneg.mpr hy.1.le))
  have hhi : 1 < (a + 1) * y := (div_lt_iff₀ hy.1).1 (Nat.lt_floor_add_one _)
  have hmap : lurothMap y = a * ((a + 1) * y - 1) := by
    simp [lurothMap, lurothDigit, a]
    ring
  rw [Set.mem_Ioc, hmap]
  refine ⟨mul_pos ha (sub_pos.mpr hhi), ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hlo (show 0 ≤ a + 1 by positivity)]

private theorem digit_ge_two {x : ℝ} (hx : x ∈ unitInterval) (k : ℕ) :
    2 ≤ lurothDigitSeq x k :=
  digit_gt_one (mapsTo.iterate k hx)

-- The branch with digit n + 2 is mapped affinely onto the entire unit interval.
private def slope (n : ℕ) : ℝ := (n + 2) * (n + 1)

private def affine (n : ℕ) (x : ℝ) : ℝ := slope n * x - (n + 1)

private theorem branch_iff (n : ℕ) (x : ℝ) :
    affine n x ∈ unitInterval ↔ x ∈ unitInterval ∧ lurothDigit x = n + 2 := by
  let q : ℝ := n + 1
  have hq : 1 ≤ q := by simp [q]
  have hpos : 0 < q := by linarith
  have hsucc : 0 < q + 1 := by positivity
  have hlo : 0 < affine n x ↔ 1 < (q + 1) * x := by
    have : affine n x = q * ((q + 1) * x - 1) := by unfold affine slope q; ring
    rw [this, mul_pos_iff_of_pos_left hpos, sub_pos]
  have hhi : affine n x ≤ 1 ↔ q * x ≤ 1 := by
    have : affine n x - 1 = (q + 1) * (q * x - 1) := by unfold affine slope q; ring
    rw [← sub_nonpos, this, ← mul_zero (q + 1), mul_le_mul_iff_right₀ hsucc, sub_nonpos]
  rw [Set.mem_Ioc, hlo, hhi]
  have hd (hx : 0 < x) : lurothDigit x = n + 2 ↔ q * x ≤ 1 ∧ 1 < (q + 1) * x := by
    simp only [lurothDigit, Nat.succ.injEq, Nat.floor_eq_iff (by positivity : 0 ≤ 1 / x),
      Nat.cast_add, Nat.cast_one, le_div_iff₀ hx, div_lt_iff₀ hx, q]
  constructor
  · rintro ⟨hl, hu⟩
    have hx : 0 < x := pos_of_mul_pos_right (by linarith : 0 < (q + 1) * x) hsucc.le
    exact ⟨⟨hx, le_trans (le_mul_of_one_le_left hx.le hq) hu⟩, (hd hx).2 ⟨hu, hl⟩⟩
  · rintro ⟨hx, h⟩
    exact ((hd hx.1).1 h).symm

private theorem affine_eq_map {n : ℕ} {x : ℝ} (h : lurothDigit x = n + 2) :
    affine n x = lurothMap x := by
  simp [affine, slope, lurothMap, h]
  ring

private theorem volume_affine (n : ℕ) (t : Set ℝ) :
    volume (affine n ⁻¹' t) = ENNReal.ofReal (slope n)⁻¹ * volume t := by
  have hp : 0 < slope n := by unfold slope; positivity
  change volume ((slope n * ·) ⁻¹' ((· + -((n : ℝ) + 1)) ⁻¹' t)) = _
  rw [Real.volume_preimage_mul_left hp.ne', abs_of_pos (inv_pos.mpr hp),
    measure_preimage_add_right]

-- Disintegrate over the first digit. The distribution of the remaining orbit on each
-- branch is a constant multiple of the same restricted Lebesgue measure.
private theorem branch_sum (D : Set ℕ) (t : Set ℝ) (ht : MeasurableSet t) :
    μ (lurothDigit ⁻¹' D ∩ lurothMap ⁻¹' t) =
      (∑' n : {n : ℕ // n + 2 ∈ D}, ENNReal.ofReal (slope n)⁻¹) * μ t := by
  let B (n : {n : ℕ // n + 2 ∈ D}) := affine n ⁻¹' (t ∩ unitInterval)
  have hB (n) (x : ℝ) : x ∈ B n ↔
      x ∈ unitInterval ∧ lurothDigit x = n.val + 2 ∧ lurothMap x ∈ t := by
    change (affine n x ∈ t ∧ affine n x ∈ unitInterval) ↔ _
    rw [branch_iff]
    constructor
    · rintro ⟨htx, hx, hd⟩
      exact ⟨hx, hd, affine_eq_map hd ▸ htx⟩
    · rintro ⟨hx, hd, htx⟩
      exact ⟨affine_eq_map hd ▸ htx, hx, hd⟩
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro x hi hj
    have hi_eq := ((hB i x).1 hi).2.1
    have hj_eq := ((hB j x).1 hj).2.1
    exact hij (Subtype.ext (Nat.add_right_cancel (hi_eq.symm.trans hj_eq)))
  have hm (n) : MeasurableSet (B n) := by
    apply (ht.inter measurableSet_Ioc).preimage
    unfold affine
    fun_prop
  rw [Measure.restrict_apply' measurableSet_Ioc]
  have heq : (lurothDigit ⁻¹' D ∩ lurothMap ⁻¹' t) ∩ unitInterval = ⋃ n, B n := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, hB]
    constructor
    · rintro ⟨⟨hd, htx⟩, hx⟩
      have h : 1 ≤ ⌊1 / x⌋₊ :=
        (Nat.one_le_floor_iff _).2 ((le_div_iff₀ hx.1).2 (by simpa using hx.2))
      have he : lurothDigit x = (lurothDigit x - 2) + 2 := by unfold lurothDigit; omega
      exact ⟨⟨_, he ▸ hd⟩, hx, he, htx⟩
    · rintro ⟨n, hx, hd, htx⟩
      exact ⟨⟨hd ▸ n.property, htx⟩, hx⟩
  rw [heq, measure_iUnion hdisj hm, ← ENNReal.tsum_mul_right]
  congr 1
  funext n
  exact (volume_affine n _).trans (by rw [Measure.restrict_apply' measurableSet_Ioc])

private theorem first_tail (D : Set ℕ) (t : Set ℝ) (ht : MeasurableSet t) :
    μ (lurothDigit ⁻¹' D ∩ lurothMap ⁻¹' t) = μ (lurothDigit ⁻¹' D) * μ t := by
  have h := branch_sum D Set.univ MeasurableSet.univ
  simp only [Set.preimage_univ, Set.inter_univ, prob_univ, mul_one] at h
  rw [branch_sum D t ht, h]

private theorem single_marginal (d : ℕ) :
    μ (lurothDigit ⁻¹' {d}) = ENNReal.ofReal (1 / ((d : ℝ) * ((d : ℝ) - 1))) := by
  have h := branch_sum {d} Set.univ MeasurableSet.univ
  simp only [Set.preimage_univ, Set.inter_univ, prob_univ, mul_one] at h
  rw [h]
  by_cases hd : 2 ≤ d
  · obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    rw [tsum_eq_single (⟨k, by simp⟩ : {n : ℕ // n + 2 ∈ ({k + 2} : Set ℕ)})
      (fun n hn => by
        have hprop := n.property
        simp only [Set.mem_singleton_iff] at hprop
        exact absurd (Subtype.ext (Nat.add_right_cancel hprop)) hn)]
    change ENNReal.ofReal (slope k)⁻¹ = _
    have hslope : slope k = ((k : ℝ) + 2) * ((k : ℝ) + 1) := by simp [slope]
    have e : (k : ℝ) + 2 - 1 = (k : ℝ) + 1 := by ring
    rw [hslope]
    congr 1
    push_cast
    rw [e, one_div]
  · have hd2 : d < 2 := by omega
    have : IsEmpty {n : ℕ // n + 2 ∈ ({d} : Set ℕ)} :=
      ⟨fun n => by
        have hprop := n.property
        simp only [Set.mem_singleton_iff] at hprop
        omega⟩
    rw [tsum_empty]
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;> simp

private theorem shift (x : ℝ) (k : ℕ) :
    lurothDigitSeq x (k + 1) = lurothDigitSeq (lurothMap x) k := by
  unfold lurothDigitSeq
  have hks : k + 1 = k.succ := rfl
  rw [hks, Function.iterate_succ_apply]

private theorem cylinder {n : ℕ} (c : Fin n → ℕ) :
    μ {x | ∀ j : Fin n, lurothDigitSeq x j = c j} =
      ∏ j, ENNReal.ofReal (1 / ((c j : ℝ) * ((c j : ℝ) - 1))) := by
  induction n with
  | zero =>
    have huniv : {x : ℝ | ∀ j : Fin 0, lurothDigitSeq x j = c j} = Set.univ :=
      Set.eq_univ_of_forall fun x j => Fin.elim0 j
    rw [huniv, prob_univ]
    exact (Fin.prod_univ_zero _).symm
  | succ n ih =>
    have ht : MeasurableSet {x : ℝ | ∀ j : Fin n, lurothDigitSeq x j = c j.succ} := by
      have hset : {x : ℝ | ∀ j : Fin n, lurothDigitSeq x j = c j.succ} =
          ⋂ (j : Fin n), (fun x => lurothDigitSeq x j) ⁻¹' {c j.succ} := by
        ext x
        simp
      rw [hset]
      exact MeasurableSet.iInter fun j => (measurable_seq j) (.of_discrete)
    have heq : {x : ℝ | ∀ j : Fin (n + 1), lurothDigitSeq x j = c j} =
        lurothDigit ⁻¹' {c 0} ∩
          lurothMap ⁻¹' {x | ∀ j : Fin n, lurothDigitSeq x j = c j.succ} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, Fin.forall_fin_succ]
      constructor
      · rintro ⟨h0, hs⟩
        refine ⟨h0, fun j => ?_⟩
        have hjs := hs j
        rw [Fin.val_succ] at hjs
        rwa [← shift x j.val]
      · rintro ⟨h0, hs⟩
        refine ⟨h0, fun j => ?_⟩
        have hjs := hs j
        rw [← shift x j.val] at hjs
        rwa [Fin.val_succ]
    rw [heq, first_tail _ _ ht, single_marginal]
    have ih' : μ {x : ℝ | ∀ j : Fin n, lurothDigitSeq x j = c j.succ} =
        ∏ (j : Fin n), ENNReal.ofReal (1 / ((c j.succ : ℝ) * ((c j.succ : ℝ) - 1))) :=
      ih _
    rw [ih', Fin.prod_univ_succ]
private theorem cylinder_volume {n : ℕ} (c : Fin n → ℕ) :
    volume {x ∈ unitInterval | ∀ j : Fin n, lurothDigitSeq x j = c j} =
      ∏ j, ENNReal.ofReal (1 / ((c j : ℝ) * ((c j : ℝ) - 1))) := by
  have heq : {x ∈ unitInterval | ∀ j : Fin n, lurothDigitSeq x j = c j} =
      {x : ℝ | ∀ j : Fin n, lurothDigitSeq x j = c j} ∩ unitInterval := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, unitInterval, Set.mem_Ioc]
    tauto
  rw [heq, ← Measure.restrict_apply' measurableSet_Ioc]
  exact cylinder c
private theorem cylinder_measurable {n : ℕ} (c : Fin n → ℕ) :
    MeasurableSet {x ∈ unitInterval | ∀ j : Fin n, lurothDigitSeq x j = c j} := by
  have hset : {x ∈ unitInterval | ∀ j : Fin n, lurothDigitSeq x j = c j} =
      (⋂ j : Fin n, (fun x => lurothDigitSeq x j) ⁻¹' {c j}) ∩ unitInterval := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff, unitInterval, Set.mem_Ioc]
    tauto
  rw [hset]
  exact (MeasurableSet.iInter fun j : Fin n => (measurable_seq _) (.of_discrete)).inter
    measurableSet_Ioc
private theorem oneD_integral (a : ℕ) (ha : 2 ≤ a) :
    ∫ x in Set.Ioc (a : ℝ) ((a : ℝ) + 1), (1 : ℝ) / x ^ 2 =
      1 / ((a : ℝ) * ((a : ℝ) + 1)) := by
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hle : (a : ℝ) ≤ (a : ℝ) + 1 := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc (a : ℝ) ((a : ℝ) + 1) := by
    rw [Set.uIcc_of_le hle]
    simp only [Set.mem_Icc, not_and]
    intro h1 h2
    linarith
  have hz := integral_zpow (a := (a : ℝ)) (b := (a : ℝ) + 1) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, h0⟩)
  simp only [show (-2 : ℤ) + 1 = -1 by rfl] at hz
  have hfun : (fun x : ℝ => (1 : ℝ) / x ^ 2) = (fun x : ℝ => x ^ (-2 : ℤ)) := by
    funext x
    rw [zpow_neg, zpow_ofNat]
    simp [one_div]
  rw [hfun, ← intervalIntegral.integral_of_le hle, hz]
  have hpos : (0 : ℝ) < (a : ℝ) := by linarith
  have hpos1 : (0 : ℝ) < (a : ℝ) + 1 := by linarith
  field_simp
  ring
private theorem oneD_integrable (a : ℕ) (ha : 2 ≤ a) :
    IntegrableOn (fun x : ℝ => (1 : ℝ) / x ^ 2) (Set.Ioc (a : ℝ) ((a : ℝ) + 1)) volume := by
  have haR : (0 : ℝ) < (a : ℝ) := by
    have h2 : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hcont : ContinuousOn (fun x : ℝ => (1 : ℝ) / x ^ 2) (Set.Icc (a : ℝ) ((a : ℝ) + 1)) := by
    apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
    intro x hx
    simp only [Set.mem_Icc] at hx
    have hxpos : 0 < x := lt_of_lt_of_le haR hx.1
    positivity
  have hcomp : IsCompact (Set.Icc (a : ℝ) ((a : ℝ) + 1)) := isCompact_Icc
  exact (hcont.integrableOn_compact hcomp).mono_set Set.Ioc_subset_Icc_self
private theorem oneD_nonneg (x : ℝ) : 0 ≤ (1 : ℝ) / x ^ 2 := by
  positivity
private theorem prod_integral {m : ℕ} (s : Fin m → Set ℝ) (hs : ∀ i, MeasurableSet (s i))
    (g : Fin m → ℝ → ℝ) :
    ∫ x : Fin m → ℝ in Set.pi Set.univ s, (∏ i, g i (x i)) =
      ∏ i, ∫ x in s i, g i x := by
  have hmeas : MeasurableSet (Set.pi Set.univ s) :=
    MeasurableSet.pi Set.countable_univ (fun i _ => hs i)
  have h1 : ∫ x : Fin m → ℝ in Set.pi Set.univ s, (∏ i, g i (x i)) =
      ∫ x : Fin m → ℝ, (Set.pi Set.univ s).indicator (fun x => ∏ i, g i (x i)) x := by
    rw [integral_indicator hmeas]
  have h2 : ∀ i, ∫ x in s i, g i x = ∫ x, (s i).indicator (g i) x := by
    intro i
    rw [integral_indicator (hs i)]
  rw [h1]
  simp_rw [h2]
  have hfun : (Set.pi Set.univ s).indicator (fun x : Fin m → ℝ => ∏ i, g i (x i)) =
      (fun x : Fin m → ℝ => ∏ i, (s i).indicator (g i) (x i)) := by
    funext x
    by_cases hx : x ∈ Set.pi Set.univ s
    · simp only [Set.indicator_of_mem hx]
      congr 1
      funext i
      have hi : x i ∈ s i := hx i (Set.mem_univ i)
      simp [Set.indicator_of_mem hi]
    · simp only [Set.indicator_of_notMem hx]
      have hex : ∃ i, x i ∉ s i := by
        simpa [Set.mem_pi] using hx
      obtain ⟨i, hi⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]
      simp [Set.indicator_of_notMem hi]
  rw [hfun]
  exact integral_fintype_prod_volume_eq_prod (fun i => (s i).indicator (g i))
private theorem bochner_to_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {f : α → ℝ} (hint : IntegrableOn f s μ)
    (hpos : ∀ x ∈ s, 0 ≤ f x) :
    ENNReal.ofReal (∫ x in s, f x ∂μ) = ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ := by
  have h1 : ∫ x in s, f x ∂μ = ∫ x, s.indicator f x ∂μ := (integral_indicator hs).symm
  have h2 : ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ =
      ∫⁻ x, s.indicator (fun x => ENNReal.ofReal (f x)) x ∂μ :=
    (lintegral_indicator hs _).symm
  rw [h1, h2]
  have hfun : s.indicator (fun x => ENNReal.ofReal (f x)) =
      fun x => ENNReal.ofReal (s.indicator f x) := by
    funext x
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  rw [hfun]
  apply ofReal_integral_eq_lintegral_ofReal
  · exact (integrable_indicator_iff hs).mpr hint
  · filter_upwards with x
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx, hpos x hx]
    · simp [Set.indicator_of_notMem hx]
private def cube {m : ℕ} (a : Fin m → ℕ) : Set (Fin m → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ioc (a i : ℝ) ((a i : ℝ) + 1))
private theorem cube_measurable {m : ℕ} (a : Fin m → ℕ) : MeasurableSet (cube a) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)
private theorem cube_disjoint {m : ℕ} {a b : Fin m → ℕ} (h : a ≠ b) :
    Disjoint (cube a) (cube b) := by
  unfold cube
  rw [Set.disjoint_pi]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  refine ⟨i, Set.mem_univ i, ?_⟩
  have hne : a i ≠ b i := hi
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : a i + 1 ≤ b i := Nat.succ_le_of_lt hlt
    have hleR : (a i : ℝ) + 1 ≤ (b i : ℝ) := by
      have hcast : ((a i + 1 : ℕ) : ℝ) ≤ ((b i : ℕ) : ℝ) := Nat.cast_le.mpr hle
      simpa using hcast
    exact Set.Ioc_disjoint_Ioc_of_le hleR
  · have hle : b i + 1 ≤ a i := Nat.succ_le_of_lt hgt
    have hleR : (b i : ℝ) + 1 ≤ (a i : ℝ) := by
      have hcast : ((b i + 1 : ℕ) : ℝ) ≤ ((a i : ℕ) : ℝ) := Nat.cast_le.mpr hle
      simpa using hcast
    exact (Set.Ioc_disjoint_Ioc_of_le hleR).symm
private theorem cube_subset {m : ℕ} (F : (Fin m → ℝ) → ℝ)
    (hmono : MonotoneOn F {x | ∀ i, 2 ≤ x i}) (y : ℝ) (a : Fin m → ℕ)
    (ha : ∀ i, 2 ≤ a i) (hy : y ≤ F (fun i => (a i : ℝ))) :
    cube a ⊆ {x : Fin m → ℝ | (∀ i, 2 ≤ x i) ∧ y ≤ F x} := by
  intro x hx
  simp only [cube, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_Ioc,
    Set.mem_ofPred_eq] at hx ⊢
  have hge : ∀ i, (a i : ℝ) ≤ x i := fun i => le_of_lt (hx i).1
  have h2x : ∀ i, 2 ≤ x i := by
    intro i
    have haR : (2 : ℝ) ≤ (a i : ℝ) := by exact_mod_cast ha i
    exact le_trans haR (hge i)
  refine ⟨h2x, le_trans hy ?_⟩
  have haRmem : (fun i => (a i : ℝ)) ∈ {x : Fin m → ℝ | ∀ i, 2 ≤ x i} := by
    simp only [Set.mem_ofPred_eq]
    intro i
    exact_mod_cast ha i
  have hxmem : x ∈ {x : Fin m → ℝ | ∀ i, 2 ≤ x i} := by
    simp only [Set.mem_ofPred_eq]
    exact h2x
  have hle : (fun i => (a i : ℝ)) ≤ x := fun i => hge i
  exact hmono haRmem hxmem hle
private theorem cube_integrable {m : ℕ} (a : Fin m → ℕ) (ha : ∀ i, 2 ≤ a i) :
    IntegrableOn (fun x : Fin m → ℝ => ∏ i, (1 : ℝ) / x i ^ 2) (cube a) volume := by
  have hs : ∀ i, MeasurableSet (Set.Ioc (a i : ℝ) ((a i : ℝ) + 1)) := fun _ =>
    measurableSet_Ioc
  have hint1 : ∀ i, IntegrableOn (fun x : ℝ => (1 : ℝ) / x ^ 2)
      (Set.Ioc (a i : ℝ) ((a i : ℝ) + 1)) volume := fun i => oneD_integrable (a i) (ha i)
  have hInt1 : ∀ i, Integrable
      ((Set.Ioc (a i : ℝ) ((a i : ℝ) + 1)).indicator (fun x : ℝ => (1 : ℝ) / x ^ 2))
      volume := fun i => (integrable_indicator_iff (hs i)).mpr (hint1 i)
  have hProd : Integrable
      (fun x : Fin m → ℝ => ∏ i, (Set.Ioc (a i : ℝ) ((a i : ℝ) + 1)).indicator
        (fun x : ℝ => (1 : ℝ) / x ^ 2) (x i)) volume :=
    Integrable.fintype_prod hInt1
  have hfun : (fun x : Fin m → ℝ => ∏ i, (Set.Ioc (a i : ℝ) ((a i : ℝ) + 1)).indicator
        (fun x : ℝ => (1 : ℝ) / x ^ 2) (x i)) =
      (cube a).indicator (fun x : Fin m → ℝ => ∏ i, (1 : ℝ) / x i ^ 2) := by
    funext x
    by_cases hx : x ∈ cube a
    · simp only [Set.indicator_of_mem hx]
      congr 1
      funext i
      have hi : x i ∈ Set.Ioc (a i : ℝ) ((a i : ℝ) + 1) := by
        simp only [cube, Set.mem_pi, Set.mem_univ, forall_true_left] at hx
        exact hx i
      simp [Set.indicator_of_mem hi]
    · simp only [Set.indicator_of_notMem hx]
      have hex : ∃ i, x i ∉ Set.Ioc (a i : ℝ) ((a i : ℝ) + 1) := by
        simp only [cube, Set.mem_pi, Set.mem_univ, forall_true_left] at hx
        simpa using hx
      obtain ⟨i, hi⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]
      simp [Set.indicator_of_notMem hi]
  rw [hfun] at hProd
  exact (integrable_indicator_iff (cube_measurable a)).mp hProd
private theorem cube_nonneg {m : ℕ} (x : Fin m → ℝ) :
    0 ≤ ∏ i, (1 : ℝ) / x i ^ 2 :=
  Finset.prod_nonneg fun i _ => oneD_nonneg (x i)
private theorem cube_integral {m : ℕ} (a : Fin m → ℕ) (ha : ∀ i, 2 ≤ a i) :
    ∫ x : Fin m → ℝ in cube a, ∏ i, (1 : ℝ) / x i ^ 2 =
      ∏ i, 1 / ((a i : ℝ) * ((a i : ℝ) + 1)) := by
  have h := prod_integral (fun i => Set.Ioc (a i : ℝ) ((a i : ℝ) + 1))
    (fun _ => measurableSet_Ioc) (fun _ x => (1 : ℝ) / x ^ 2)
  simp only [cube] at h ⊢
  rw [h]
  congr 1
  funext i
  exact oneD_integral (a i) (ha i)
private theorem cube_lintegral {m : ℕ} (a : Fin m → ℕ) (ha : ∀ i, 2 ≤ a i) :
    ∫⁻ x : Fin m → ℝ in cube a, ENNReal.ofReal (∏ i, (1 : ℝ) / x i ^ 2) =
      ∏ i, ENNReal.ofReal (1 / ((a i : ℝ) * ((a i : ℝ) + 1))) := by
  have hConv := bochner_to_lintegral (cube_measurable a) (cube_integrable a ha)
    (fun x _ => cube_nonneg x)
  rw [cube_integral a ha] at hConv
  have hpos : ∀ i ∈ Finset.univ, 0 ≤ (1 : ℝ) / ((a i : ℝ) * ((a i : ℝ) + 1)) := by
    intro i _
    positivity
  rw [ENNReal.ofReal_prod_of_nonneg hpos] at hConv
  exact hConv.symm
private theorem coord_le {m : ℕ} (a : Fin m → ℕ) (ha : ∀ i, 2 ≤ a i) (i : Fin m) :
    ENNReal.ofReal (1 / ((a i : ℝ) * ((a i : ℝ) - 1))) ≤
      3 * ENNReal.ofReal (1 / ((a i : ℝ) * ((a i : ℝ) + 1))) := by
  have haR : (2 : ℝ) ≤ (a i : ℝ) := by exact_mod_cast ha i
  have hpos : (0 : ℝ) < (a i : ℝ) := by linarith
  have hpos1 : (0 : ℝ) < (a i : ℝ) - 1 := by linarith
  have hpos2 : (0 : ℝ) < (a i : ℝ) + 1 := by linarith
  have hpos3 : (0 : ℝ) < (a i : ℝ) * ((a i : ℝ) - 1) := mul_pos hpos hpos1
  have hpos4 : (0 : ℝ) < (a i : ℝ) * ((a i : ℝ) + 1) := mul_pos hpos hpos2
  have hreal : (1 : ℝ) / ((a i : ℝ) * ((a i : ℝ) - 1)) ≤
      3 / ((a i : ℝ) * ((a i : ℝ) + 1)) := by
    rw [div_le_div_iff₀ hpos3 hpos4]
    nlinarith
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by simp
  rw [h3, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hmul : (3 : ℝ) * (1 / ((a i : ℝ) * ((a i : ℝ) + 1))) =
      3 / ((a i : ℝ) * ((a i : ℝ) + 1)) := by
    ring
  rw [hmul]
  exact ENNReal.ofReal_le_ofReal hreal
private theorem cube_compare {m : ℕ} (a : Fin m → ℕ) (ha : ∀ i, 2 ≤ a i) :
    ∏ i, ENNReal.ofReal (1 / ((a i : ℝ) * ((a i : ℝ) - 1))) ≤
      (3 : ℝ≥0∞) ^ m * ∫⁻ x : Fin m → ℝ in cube a,
        ENNReal.ofReal (∏ i, (1 : ℝ) / x i ^ 2) := by
  rw [cube_lintegral a ha]
  have h3pow : (3 : ℝ≥0∞) ^ m = ∏ _ : Fin m, (3 : ℝ≥0∞) := by
    simp [Finset.prod_const, Finset.card_univ]
  rw [h3pow, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod fun i _ => coord_le a ha i
private def levelSet {m : ℕ} (F : (Fin m → ℝ) → ℝ) (y : ℝ) : Set (Fin m → ℕ) :=
  {a | (∀ i, 2 ≤ a i) ∧ y ≤ F (fun i => (a i : ℝ))}
private def cylSet {m : ℕ} (a : Fin m → ℕ) : Set ℝ :=
  {x ∈ unitInterval | ∀ j : Fin m, lurothDigitSeq x j = a j}
private theorem union_eq {m : ℕ} (F : (Fin m → ℝ) → ℝ) (y : ℝ) :
    {x ∈ unitInterval | y ≤ F (fun i => (lurothDigitSeq x i : ℝ))} =
      ⋃ s : levelSet F y, cylSet s.val := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, cylSet, levelSet]
  constructor
  · rintro ⟨hx, hy⟩
    have ha : ∀ i : Fin m, 2 ≤ lurothDigitSeq x i := fun i => digit_ge_two hx _
    refine ⟨⟨fun i : Fin m => lurothDigitSeq x i, ha, hy⟩, hx, fun j => rfl⟩
  · rintro ⟨s, hx, hs⟩
    have heq : (fun i : Fin m => (lurothDigitSeq x i : ℝ)) = (fun i => (s.val i : ℝ)) := by
      funext i
      rw [hs i]
    rw [heq]
    exact ⟨hx, s.property.2⟩
private theorem cyl_disjoint {m : ℕ} (F : (Fin m → ℝ) → ℝ) (y : ℝ) :
    Pairwise (Function.onFun Disjoint (fun s : levelSet F y => cylSet s.val)) := by
  intro s t hst
  have hval : s.val ≠ t.val := fun hval => hst (Subtype.ext hval)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hval
  apply Set.disjoint_left.mpr
  intro x hx1 hx2
  simp only [cylSet, Set.mem_ofPred_eq] at hx1 hx2
  have h1 := hx1.2 i
  have h2 := hx2.2 i
  exact hi (h1.symm.trans h2)
private theorem cyl_union_meas {m : ℕ} (F : (Fin m → ℝ) → ℝ) (y : ℝ) :
    volume {x ∈ unitInterval | y ≤ F (fun i => (lurothDigitSeq x i : ℝ))} =
      ∑' s : levelSet F y, volume (cylSet s.val) := by
  rw [union_eq F y]
  exact measure_iUnion (cyl_disjoint F y) fun s => cylinder_measurable s.val
private theorem cube_disjoint_subtype {m : ℕ} (F : (Fin m → ℝ) → ℝ) (y : ℝ) :
    Pairwise (Function.onFun Disjoint (fun s : levelSet F y => cube s.val)) := by
  intro s t hst
  have hval : s.val ≠ t.val := fun hval => hst (Subtype.ext hval)
  exact cube_disjoint hval
private theorem cube_union_subset {m : ℕ} (F : (Fin m → ℝ) → ℝ)
    (hmono : MonotoneOn F {x | ∀ i, 2 ≤ x i}) (y : ℝ) :
    ⋃ s : levelSet F y, cube s.val ⊆
      {x : Fin m → ℝ | (∀ i, 2 ≤ x i) ∧ y ≤ F x} := by
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨s, hs⟩ := hx
  exact cube_subset F hmono y s.val s.property.1 s.property.2 hs
private theorem cube_union_integral {m : ℕ} (F : (Fin m → ℝ) → ℝ)
    (hmono : MonotoneOn F {x | ∀ i, 2 ≤ x i}) (y : ℝ) :
    ∑' s : levelSet F y, ∫⁻ x : Fin m → ℝ in cube s.val,
        ENNReal.ofReal (∏ i, (1 : ℝ) / x i ^ 2) ≤
      ∫⁻ x : Fin m → ℝ in {x : Fin m → ℝ | (∀ i, 2 ≤ x i) ∧ y ≤ F x},
        ENNReal.ofReal (∏ i, (1 : ℝ) / x i ^ 2) := by
  have hEq : ∫⁻ x : Fin m → ℝ in ⋃ s : levelSet F y, cube s.val,
        ENNReal.ofReal (∏ i, (1 : ℝ) / x i ^ 2) =
      ∑' s : levelSet F y, ∫⁻ x : Fin m → ℝ in cube s.val,
        ENNReal.ofReal (∏ i, (1 : ℝ) / x i ^ 2) :=
    lintegral_iUnion (fun s : levelSet F y => cube_measurable s.val)
      (cube_disjoint_subtype F y) _
  rw [← hEq]
  exact lintegral_mono_set (cube_union_subset F hmono y)
end volume_lurothDigits_ge_le
open volume_lurothDigits_ge_le
/-- **Upper bound for the measure of a Lüroth digit superlevel set.** Let $m \in \mathbb{N}$, let
$F : \mathbb{R}^m \to \mathbb{R}$ be non-decreasing on $[2, \infty)^m$ for the coordinatewise
order, let $y \in \mathbb{R}$, and write $d_k(x)$ for the $k$-th Lüroth digit of $x$. Then the
Lebesgue measure of $\{x \in (0, 1] : F(d_1(x), \dots, d_m(x)) \ge y\}$ is at most
$$3^m \int_{\{x \in [2, \infty)^m : F(x) \ge y\}} \prod_{i=1}^{m} \frac{1}{x_i^2} \, dx.$$

The paper states this bound for $y = \Psi(n)$ under the hypotheses of its Theorem 4; only
the monotonicity of $F$ is used.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 6
(`integers-2024-A67-thm-6`). -/
public theorem volume_lurothDigits_ge_le {m : ℕ} (F : (Fin m → ℝ) → ℝ)
    (hmono : MonotoneOn F {x | ∀ i, 2 ≤ x i}) (y : ℝ) :
    volume {x ∈ Set.Ioc (0 : ℝ) 1 | y ≤ F (fun i => (lurothDigitSeq x i : ℝ))} ≤
      3 ^ m * ∫⁻ x in {x : Fin m → ℝ | (∀ i, 2 ≤ x i) ∧ y ≤ F x},
        ENNReal.ofReal (∏ i, 1 / x i ^ 2) := by
  have hLe : ∀ s : levelSet F y, volume (cylSet s.val) ≤
      (3 : ℝ≥0∞) ^ m * ∫⁻ x : Fin m → ℝ in cube s.val,
        ENNReal.ofReal (∏ i, (1 : ℝ) / x i ^ 2) := by
    intro s
    have hEq : volume (cylSet s.val) =
        ∏ i, ENNReal.ofReal (1 / ((s.val i : ℝ) * ((s.val i : ℝ) - 1))) :=
      cylinder_volume s.val
    rw [hEq]
    exact cube_compare s.val s.property.1
  calc volume {x ∈ Set.Ioc (0 : ℝ) 1 | y ≤ F (fun i => (lurothDigitSeq x i : ℝ))} =
        ∑' s : levelSet F y, volume (cylSet s.val) := cyl_union_meas F y
    _ ≤ ∑' s : levelSet F y, (3 : ℝ≥0∞) ^ m * ∫⁻ x : Fin m → ℝ in cube s.val,
          ENNReal.ofReal (∏ i, (1 : ℝ) / x i ^ 2) := tsum_le_tsum hLe
    _ = (3 : ℝ≥0∞) ^ m * ∑' s : levelSet F y, ∫⁻ x : Fin m → ℝ in cube s.val,
          ENNReal.ofReal (∏ i, (1 : ℝ) / x i ^ 2) := ENNReal.tsum_mul_left
    _ ≤ (3 : ℝ≥0∞) ^ m * ∫⁻ x : Fin m → ℝ in {x : Fin m → ℝ | (∀ i, 2 ≤ x i) ∧ y ≤ F x},
          ENNReal.ofReal (∏ i, (1 : ℝ) / x i ^ 2) := by
        gcongr
        exact cube_union_integral F hmono y
end MetaMathlibExt
