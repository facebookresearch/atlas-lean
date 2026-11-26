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
import MathlibExt.NumberTheory.LurothConsecutiveDigitsVolumeLurothCylinder

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

-- The digit sequence is measurable by the imported joint law of the digits, which also gives
-- the cylinder masses through `volume_lurothCylinder`.
private theorem cylinder_measurable {n : ℕ} (c : Fin n → ℕ) :
    MeasurableSet {x ∈ unitInterval | ∀ j : Fin n, lurothDigitSeq x j = c j} := by
  obtain ⟨_, _, _, hmp⟩ :=
    volume_lurothConsecutiveDigits_zero_one_integral.measurePreserving_digitSeq
  have hset : {x ∈ unitInterval | ∀ j : Fin n, lurothDigitSeq x j = c j} =
      (⋂ j : Fin n, (fun x => lurothDigitSeq x j) ⁻¹' {c j}) ∩ unitInterval := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff, unitInterval, Set.mem_Ioc]
    tauto
  rw [hset]
  exact (MeasurableSet.iInter fun j : Fin n =>
    ((measurable_pi_apply (j : ℕ)).comp hmp.measurable) (measurableSet_singleton _)).inter
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
private theorem prod_integral {m : ℕ} (s : Fin m → Set ℝ) (g : Fin m → ℝ → ℝ) :
    ∫ x : Fin m → ℝ in Set.pi Set.univ s, (∏ i, g i (x i)) =
      ∏ i, ∫ x in s i, g i x := by
  rw [volume_pi, Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod g
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
  rw [IntegrableOn, cube, volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (f := fun _ x => (1 : ℝ) / x ^ 2)
    fun i => oneD_integrable (a i) (ha i)
private theorem cube_nonneg {m : ℕ} (x : Fin m → ℝ) :
    0 ≤ ∏ i, (1 : ℝ) / x i ^ 2 :=
  Finset.prod_nonneg fun i _ => oneD_nonneg (x i)
private theorem cube_integral {m : ℕ} (a : Fin m → ℕ) (ha : ∀ i, 2 ≤ a i) :
    ∫ x : Fin m → ℝ in cube a, ∏ i, (1 : ℝ) / x i ^ 2 =
      ∏ i, 1 / ((a i : ℝ) * ((a i : ℝ) + 1)) := by
  have h := prod_integral (fun i => Set.Ioc (a i : ℝ) ((a i : ℝ) + 1))
    (fun _ x => (1 : ℝ) / x ^ 2)
  simp only [cube] at h ⊢
  rw [h]
  congr 1
  funext i
  exact oneD_integral (a i) (ha i)
private theorem cube_lintegral {m : ℕ} (a : Fin m → ℕ) (ha : ∀ i, 2 ≤ a i) :
    ∫⁻ x : Fin m → ℝ in cube a, ENNReal.ofReal (∏ i, (1 : ℝ) / x i ^ 2) =
      ∏ i, ENNReal.ofReal (1 / ((a i : ℝ) * ((a i : ℝ) + 1))) := by
  have hConv := ofReal_integral_eq_lintegral_ofReal (cube_integrable a ha)
    (ae_restrict_of_forall_mem (cube_measurable a) fun x _ => cube_nonneg x)
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
      volume_lurothCylinder s.val
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
