/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LurothConvergent
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Borel–Bernstein theorem for Lüroth digits

The measure of the set of points whose digits meet or exceed a sequence of positive thresholds
infinitely often is determined by summability of the reciprocal thresholds.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology Function

namespace MetaMathlibExt
namespace volume_lurothDigit_ge_zero_one

private abbrev unitInterval := Ioc (0 : ℝ) 1
private noncomputable abbrev μ : Measure ℝ := volume.restrict unitInterval

private theorem prob_univ : μ univ = 1 := by
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
  have hdisj : Pairwise (Disjoint on B) := by
    intro i j hij
    apply disjoint_left.2
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
    simp only [mem_inter_iff, mem_preimage, mem_iUnion, hB]
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
  have h := branch_sum D univ MeasurableSet.univ
  simp only [preimage_univ, inter_univ, prob_univ, mul_one] at h
  rw [branch_sum D t ht, h]

private noncomputable def block (D : ℕ → Set ℕ) (n : ℕ) : Set ℝ :=
  ⋂ i ∈ Finset.range n, (fun x => lurothDigitSeq x i) ⁻¹' D i

private theorem block_measure (D : ℕ → Set ℕ) (n : ℕ) :
    μ (block D n) = ∏ i ∈ Finset.range n, μ (lurothDigit ⁻¹' D i) := by
  induction n generalizing D with
  | zero => simp [block]
  | succ n ih =>
    let tail := block (fun i => D (i + 1)) n
    have htail : MeasurableSet tail :=
      .iInter fun i => .iInter fun _ => (measurable_seq i) (.of_discrete)
    have heq : block D (n + 1) = lurothDigit ⁻¹' D 0 ∩ lurothMap ⁻¹' tail := by
      ext x
      simp only [block, tail, mem_inter_iff, mem_preimage, mem_iInter, Finset.mem_range]
      constructor
      · intro h
        exact ⟨h 0 (by omega), fun i hi => by
          simpa [lurothDigitSeq, Function.iterate_succ_apply] using h (i + 1) (by omega)⟩
      · rintro ⟨h, ht⟩ (_ | i) hi
        · exact h
        · simpa [lurothDigitSeq, Function.iterate_succ_apply] using ht i (by omega)
    rw [heq, first_tail _ _ htail, Finset.prod_range_succ', mul_comm]
    exact congrArg (· * _) (ih _)

-- Fill gaps in a finite selection of digits with unrestricted digit sets.
private theorem finite_law (D : ℕ → Set ℕ) (s : Finset ℕ) :
    μ (⋂ i ∈ s, (fun x => lurothDigitSeq x i) ⁻¹' D i) =
      ∏ i ∈ s, μ (lurothDigit ⁻¹' D i) := by
  obtain ⟨n, hn⟩ := s.exists_nat_subset_range
  let A (i : ℕ) : Set ℕ := if i ∈ s then D i else univ
  have hblock : (⋂ i ∈ s, (fun x => lurothDigitSeq x i) ⁻¹' D i) = block A n := by
    ext x
    simp only [block, mem_iInter, mem_preimage]
    constructor
    · intro h i _
      by_cases hi : i ∈ s <;> simp [A, hi, h]
    · intro h i hi
      simpa [A, hi] using h i (hn hi)
  rw [hblock, block_measure]
  have hw (i : ℕ) :
      μ (lurothDigit ⁻¹' A i) = if i ∈ s then μ (lurothDigit ⁻¹' D i) else 1 := by
    by_cases hi : i ∈ s <;> simp [A, hi]
  simp only [hw, Finset.prod_ite_mem, Finset.inter_eq_right.mpr hn]

private theorem marginal (D : ℕ → Set ℕ) (i : ℕ) :
    μ ((fun x => lurothDigitSeq x i) ⁻¹' D i) = μ (lurothDigit ⁻¹' D i) := by
  simpa using finite_law D {i}

private theorem indep (D : ℕ → Set ℕ) :
    iIndepSet (fun i => (fun x => lurothDigitSeq x i) ⁻¹' D i) μ := by
  apply (iIndepSet_iff_meas_biInter (fun i => (measurable_seq i) (.of_discrete))).2
  intro s
  simpa only [marginal D] using finite_law D s

-- On (0,1] the first digit lies between 1/x and 2/x.
private theorem tail_bounds (y : ℝ) (hy : 0 < y) :
    ENNReal.ofReal (min 1 y⁻¹) ≤ μ {x | y ≤ (lurothDigit x : ℝ)} ∧
      μ {x | y ≤ (lurothDigit x : ℝ)} ≤ ENNReal.ofReal (2 * y⁻¹) := by
  rw [Measure.restrict_apply' measurableSet_Ioc]
  constructor
  · calc
      ENNReal.ofReal (min 1 y⁻¹) = volume (Ioc (0 : ℝ) (min 1 y⁻¹)) := by simp
      _ ≤ _ := by
        apply measure_mono
        rintro x ⟨hx, hu⟩
        have hxy := (le_min_iff.mp hu).2
        have h : y ≤ 1 / x := (le_div_iff₀ hx).2 (by
          rw [inv_eq_one_div, le_div_iff₀ hy] at hxy
          exact (mul_comm y x).trans_le hxy)
        have hd := Nat.lt_floor_add_one (1 / x)
        exact ⟨h.trans (by simpa [lurothDigit] using hd.le), hx, (le_min_iff.mp hu).1⟩
  · calc
      _ ≤ volume (Ioc (0 : ℝ) (2 * y⁻¹)) := by
        apply measure_mono
        rintro x ⟨hd, hx, hu⟩
        have hf := Nat.floor_le (by positivity : 0 ≤ 1 / x)
        have hfloor := (le_div_iff₀ hx).1 hf
        have he : y ≤ (⌊1 / x⌋₊ : ℝ) + 1 := by simpa [lurothDigit] using hd
        have hmul := mul_le_mul_of_nonneg_right he hx.le
        exact ⟨hx, (le_div_iff₀ hy).2 (by nlinarith)⟩
      _ = _ := by simp

end volume_lurothDigit_ge_zero_one

open volume_lurothDigit_ge_zero_one

namespace volume_lurothConsecutiveDigits_zero_one_integral

private theorem indepFun : iIndepFun (fun i x => lurothDigitSeq x i) μ := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.2
  intro s D _
  simpa only [marginal D] using finite_law D s

private theorem first_digit_mass (d : ℕ) :
    μ (lurothDigit ⁻¹' {d}) =
      if 2 ≤ d then ENNReal.ofReal (1 / ((d : ℝ) * ((d : ℝ) - 1))) else 0 := by
  have h := branch_sum {d} univ MeasurableSet.univ
  simp only [preimage_univ, inter_univ, prob_univ, mul_one] at h
  rw [h]
  by_cases hd : 2 ≤ d
  · obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
    let ins : Unique {j : ℕ // j + 2 ∈ ({n + 2} : Set ℕ)} :=
      ⟨⟨⟨n, rfl⟩⟩, fun j => Subtype.ext (Nat.add_right_cancel j.property)⟩
    have hdefault : (default : {j : ℕ // j + 2 ∈ ({n + 2} : Set ℕ)}).val = n := rfl
    have hs : (↑n + 2 : ℝ) - 1 = ↑n + 1 := by ring
    simp [hdefault, slope, hs, one_div]
  · have : IsEmpty {j : ℕ // j + 2 ∈ ({d} : Set ℕ)} :=
      ⟨fun j => hd (show 2 ≤ d from j.property ▸ Nat.le_add_left 2 j.val)⟩
    simp [hd]

/-- **Joint distribution of Lüroth digits.** Under Lebesgue measure on $(0,1]$, the digit
sequence is distributed as a product of identical discrete measures, each giving mass
$1/(d(d-1))$ to digit $d \ge 2$ and zero mass to digits $0$ and $1$.

Source: ATLAS, *Measure of Lüroth cylinders*. The finite cylinder probabilities determine the
joint distribution. -/
public theorem measurePreserving_digitSeq :
    ∃ ν : Measure ℕ, IsProbabilityMeasure ν ∧
      (∀ d : ℕ, ν {d} = if 2 ≤ d then ENNReal.ofReal (1 / ((d : ℝ) * ((d : ℝ) - 1))) else 0) ∧
      MeasurePreserving lurothDigitSeq (volume.restrict (Ioc (0 : ℝ) 1))
        (Measure.infinitePi fun _ : ℕ => ν) := by
  have : IsProbabilityMeasure μ := ⟨prob_univ⟩
  refine ⟨μ.map lurothDigit,
    (Measure.isProbabilityMeasure_map_iff measurable_digit.aemeasurable).2 ‹_›,
    fun d => ?_, measurable_pi_iff.2 measurable_seq, ?_⟩
  · rw [Measure.map_apply measurable_digit (measurableSet_singleton d), first_digit_mass]
  · rw [show lurothDigitSeq = (fun x i => lurothDigitSeq x i) from rfl,
      indepFun.map_fun_eq_infinitePi_map measurable_seq]
    congr 1
    funext i
    ext s hs
    rw [Measure.map_apply (measurable_seq i) hs, Measure.map_apply measurable_digit hs,
      marginal (fun _ => s)]

end volume_lurothConsecutiveDigits_zero_one_integral

/-- **Borel–Bernstein theorem for Lüroth digits.** Let $(\Psi(n))_{n \ge 0}$ be a sequence of
positive reals, write $d_k(x)$ for the $k$-th Lüroth digit of $x$, and let $E$ be the set of
$x \in (0, 1]$ such that $d_{n+1}(x) \ge \Psi(n)$ for infinitely many $n$. If
$\sum_{n \ge 0} 1 / \Psi(n) < \infty$ then $E$ has Lebesgue measure $0$, and if
$\sum_{n \ge 0} 1 / \Psi(n) = \infty$ then $E$ has Lebesgue measure $1$.

The paper quotes this result from Jager and de Vroedt (its reference [3]).

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 1
(`integers-2024-A67-thm-1`). -/
public theorem volume_lurothDigit_ge_zero_one (Ψ : ℕ → ℝ) (hΨ : ∀ n, 0 < Ψ n) :
    let E := {x ∈ Set.Ioc (0 : ℝ) 1 | ∃ᶠ n in atTop, Ψ n ≤ lurothDigitSeq x n}
    (Summable (fun n => (Ψ n)⁻¹) → volume E = 0) ∧
      (¬ Summable (fun n => (Ψ n)⁻¹) → volume E = 1) := by
  let D (n : ℕ) : Set ℕ := {d | Ψ n ≤ (d : ℝ)}
  let A (n : ℕ) := (fun x => lurothDigitSeq x n) ⁻¹' D n
  have hA (n) : MeasurableSet (A n) := (measurable_seq n) .of_discrete
  have hE : volume {x ∈ Set.Ioc (0 : ℝ) 1 | ∃ᶠ n in atTop, Ψ n ≤ lurothDigitSeq x n} =
      μ (limsup A atTop) := by
    rw [Measure.restrict_apply' measurableSet_Ioc]
    congr 1
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_limsup_iff_frequently_mem, A, D, mem_preimage]
    exact and_comm
  dsimp only
  rw [hE]
  have hb (n) : ENNReal.ofReal (min 1 (Ψ n)⁻¹) ≤ μ (A n) ∧
      μ (A n) ≤ ENNReal.ofReal (2 * (Ψ n)⁻¹) := by
    dsimp only [A]
    rw [marginal D]
    exact tail_bounds _ (hΨ n)
  constructor
  · intro h
    apply measure_limsup_atTop_eq_zero
    exact ne_top_of_le_ne_top (h.mul_left 2).tsum_ofReal_ne_top
      (tsum_le_tsum fun n => (hb n).2)
  · intro h
    apply measure_limsup_eq_one hA (indep D)
    by_contra hfinite
    have hmin : Summable fun n => min 1 (Ψ n)⁻¹ := by
      refine .of_nonneg_of_le (fun n => le_min zero_le_one (inv_nonneg.2 (hΨ n).le)) (fun n => ?_)
        (ENNReal.summable_toReal hfinite)
      exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_tsum_ne_top hfinite n)).1 (hb n).1
    apply h (hmin.congr_atTop ?_)
    filter_upwards [hmin.tendsto_atTop_zero.eventually_lt_const zero_lt_one] with n hn
    change min 1 (Ψ n)⁻¹ < 1 at hn
    exact min_eq_right ((min_lt_iff.mp hn).resolve_left (lt_irrefl _)).le

end MetaMathlibExt
