/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Sort.Bucket.Basic
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Moments.Variance

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Continuous expected saved-bucket cost

CLRS, fourth edition, section8.4 (printed pages215-218). Coordinates are independent
continuous uniforms on `[0,1)`. Bucket counts need not be mutually independent.
All expected-time claims concern the actual `bucketSort` event count, via its public
filtered-bucket cost equation. The observable is zero outside the almost-sure valid
input set. No finite sampler, physical RAM cost or native-time estimate is substituted.
-/

open Set MeasureTheory ProbabilityTheory Cslib.Algorithms.Lean Filter
open scoped BigOperators

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.TimeM

private lemma classifier_fiber_generic {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorRing R] {n : ℕ} (hn : 0 < n) (i : Fin n) :
    Ico (0 : R) 1 ∩ (fun x : R => Nat.floor ((n : R) * x)) ⁻¹' {i.val} =
      Ico ((i.val : R) / n) (((i.val : R) + 1) / n) := by
  have hn' : 0 < (n : R) := by exact_mod_cast hn
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Ico]
  constructor
  · rintro ⟨hx, hf⟩
    have hprod := (Nat.floor_eq_iff (mul_nonneg (le_of_lt hn') hx.1)).1 hf
    constructor
    · exact (div_le_iff₀ hn').2 (by simpa [mul_comm] using hprod.1)
    · exact (lt_div_iff₀ hn').2 (by simpa [mul_comm] using hprod.2)
  · rintro ⟨hlo, hhi⟩
    have hlow : (i.val : R) ≤ (n : R) * x := by
      simpa [mul_comm] using (div_le_iff₀ hn').1 hlo
    have hupp : (n : R) * x < (i.val : R) + 1 := by
      simpa [mul_comm] using (lt_div_iff₀ hn').1 hhi
    have hi : (i.val : R) + 1 ≤ (n : R) := by
      exact_mod_cast Nat.succ_le_of_lt i.isLt
    have hx0 : 0 ≤ x := by
      have : 0 ≤ (i.val : R) / (n : R) := div_nonneg (Nat.cast_nonneg _) (le_of_lt hn')
      exact this.trans hlo
    have hx1 : x < 1 := by nlinarith
    exact ⟨⟨hx0, hx1⟩, (Nat.floor_eq_iff (mul_nonneg (le_of_lt hn') hx0)).2 ⟨hlow, hupp⟩⟩

private lemma classifier_measurable (n : ℕ) :
    Measurable (fun x : ℝ => Nat.floor ((n : ℝ) * x)) :=
  (measurable_const.mul measurable_id).nat_floor

private lemma classifier_mass {n : ℕ} (hn : 0 < n) (i : Fin n) :
    ProbabilityTheory.cond volume (Ico (0 : ℝ) 1)
      ((fun x : ℝ => Nat.floor ((n : ℝ) * x)) ⁻¹' {i.val}) =
      ENNReal.ofReal (1 / (n : ℝ)) := by
  have hset : MeasurableSet ((fun x : ℝ => Nat.floor ((n : ℝ) * x)) ⁻¹' {i.val}) :=
    (classifier_measurable n) (measurableSet_singleton _)
  change ProbabilityTheory.cond volume (Ico (0 : ℝ) 1)
    (id ⁻¹' ((fun x : ℝ => Nat.floor ((n : ℝ) * x)) ⁻¹' {i.val})) = _
  rw [(pdf.IsUniform.cond (μ := volume) (s := Ico (0 : ℝ) 1)).measure_preimage hset,
    classifier_fiber_generic (R := ℝ) hn i, Real.volume_Ico, Real.volume_Ico]
  simp only [sub_zero, ENNReal.ofReal_one, div_one]
  congr 1
  ring

private lemma countP_real_sum {α : Type u} (p : α → Bool) (xs : List α) :
    (xs.countP p : Real) = (xs.map fun x => if p x then (1 : Real) else 0).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases h : p x <;> simp [h, ih, add_comm]

private lemma occupancy_sum {n : Nat} (i : Fin n) (ω : Fin n → Real) :
    ((Array.ofFn ω).toList.countP (fun x => decide (Nat.floor ((n : Real) * x) = i.val))
      : Real) =
      ∑ j : Fin n, ((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
        (1 : Real → Real) (ω j) := by
  rw [countP_real_sum, Array.toList_ofFn, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : Nat.floor ((n : Real) * ω j) = i.val <;> simp [h, Set.indicator]

private lemma cond_real_probability :
    IsProbabilityMeasure (cond (volume : Measure Real) (Ico 0 1)) := by
  exact (pdf.IsUniform.cond : pdf.IsUniform (id : Real → Real) (Ico 0 1)
    (cond volume (Ico 0 1)) volume).isProbabilityMeasure
      (by simp [Real.volume_Ico]) (by simp [Real.volume_Ico])

private lemma indicator_memLp {n : Nat} (i : Fin n) :
    MemLp (((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
      (1 : Real → Real))
      2 (cond (volume : Measure Real) (Ico 0 1)) := by
  let : IsProbabilityMeasure (cond (volume : Measure Real) (Ico 0 1)) :=
    cond_real_probability
  exact (memLp_const (1 : Real)).indicator
    ((classifier_measurable n) (measurableSet_singleton _))

private lemma indicator_integral {n : Nat} (hn : 0 < n) (i : Fin n) :
    (∫ x : Real, ((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
      1 x ∂cond (volume : Measure Real) (Ico 0 1)) = 1 / (n : Real) := by
  rw [integral_indicator_one ((classifier_measurable n) (measurableSet_singleton _))]
  change ((cond (volume : Measure Real) (Ico 0 1))
    ((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val})).toReal = _
  rw [classifier_mass hn i, ENNReal.toReal_ofReal (by positivity)]

private lemma coordinate_integral {n : Nat} (hn : 0 < n) (i j : Fin n) :
    (∫ ω : Fin n → Real,
      ((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
        (1 : Real → Real) (ω j)
      ∂Measure.pi (fun _ : Fin n => cond (volume : Measure Real) (Ico 0 1))) =
      1 / (n : Real) := by
  let μ : Measure Real := cond (volume : Measure Real) (Ico 0 1)
  let : IsProbabilityMeasure μ := cond_real_probability
  have hp := measurePreserving_eval (fun _ : Fin n => μ) j
  have hm : AEStronglyMeasurable
      (((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
        (1 : Real → Real))
      (Measure.map (Function.eval j) (Measure.pi (fun _ : Fin n => μ))) := by
    rw [hp.map_eq]
    exact (indicator_memLp i).aestronglyMeasurable
  rw [← integral_map hp.measurable.aemeasurable hm, hp.map_eq]
  exact indicator_integral hn i

private lemma occupancy_memLp {n : Nat} (i : Fin n) :
    MemLp (fun ω : Fin n → Real =>
      ((Array.ofFn ω).toList.countP (fun x => decide (Nat.floor ((n : Real) * x) = i.val))
        : Real))
      2 (Measure.pi (fun _ : Fin n => cond (volume : Measure Real) (Ico 0 1))) := by
  let μ : Measure Real := cond (volume : Measure Real) (Ico 0 1)
  let : IsProbabilityMeasure μ := cond_real_probability
  rw [funext (occupancy_sum i)]
  apply memLp_finsetSum Finset.univ
  intro j _
  exact (indicator_memLp i).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin n => μ) j)

private lemma occupancy_mean {n : Nat} (hn : 0 < n) (i : Fin n) :
    (∫ ω : Fin n → Real,
      ((Array.ofFn ω).toList.countP (fun x => decide (Nat.floor ((n : Real) * x) = i.val))
        : Real)
      ∂Measure.pi (fun _ : Fin n => cond (volume : Measure Real) (Ico 0 1))) = 1 := by
  let μ : Measure Real := cond (volume : Measure Real) (Ico 0 1)
  let : IsProbabilityMeasure μ := cond_real_probability
  rw [funext (occupancy_sum i)]
  change (∫ ω : Fin n → Real, ∑ j : Fin n,
    ((((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
      (1 : Real → Real)) ∘ Function.eval j) ω
    ∂Measure.pi (fun _ : Fin n => μ)) = 1
  rw [integral_finsetSum Finset.univ (fun j _ =>
    ((indicator_memLp i).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => μ) j)).integrable (by norm_num))]
  simp only [Function.comp_apply]
  dsimp only [μ]
  simp_rw [coordinate_integral hn i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

private lemma indicator_variance {n : Nat} (hn : 0 < n) (i : Fin n) :
    variance (((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
      (1 : Real → Real)) (cond (volume : Measure Real) (Ico 0 1)) =
      1 / (n : Real) - (1 / (n : Real)) ^ 2 := by
  let : IsProbabilityMeasure (cond (volume : Measure Real) (Ico 0 1)) :=
    cond_real_probability
  have hs :
      (((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
        (1 : Real → Real)) ^ 2 =
      ((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
        (1 : Real → Real) := by
    funext x
    by_cases h : Nat.floor ((n : Real) * x) = i.val <;> simp [Set.indicator, h]
  rw [variance_eq_sub (indicator_memLp i), hs, indicator_integral hn i]

private lemma occupancy_variance {n : Nat} (hn : 0 < n) (i : Fin n) :
    variance (fun ω : Fin n → Real =>
      ((Array.ofFn ω).toList.countP (fun x => decide (Nat.floor ((n : Real) * x) = i.val))
        : Real))
      (Measure.pi (fun _ : Fin n => cond (volume : Measure Real) (Ico 0 1))) =
      1 - 1 / (n : Real) := by
  let μ : Measure Real := cond (volume : Measure Real) (Ico 0 1)
  let : IsProbabilityMeasure μ := cond_real_probability
  rw [funext (occupancy_sum i)]
  change variance (fun ω : Fin n → Real => ∑ j : Fin n,
    ((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
      (1 : Real → Real) (ω j)) (Measure.pi (fun _ : Fin n => μ)) = _
  have hs := variance_sum_pi (μ := fun _ : Fin n => μ)
    (X := fun _ : Fin n =>
      ((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
        (1 : Real → Real)) (fun _ => indicator_memLp i)
  have hfun :
      (∑ j : Fin n, fun ω : Fin n → Real =>
        ((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
          (1 : Real → Real) (ω j)) =
      (fun ω : Fin n → Real => ∑ j : Fin n,
        ((fun x : Real => Nat.floor ((n : Real) * x)) ⁻¹' {i.val}).indicator
          (1 : Real → Real) (ω j)) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hfun] at hs
  rw [hs]
  dsimp only [μ]
  simp_rw [indicator_variance hn i]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

private lemma occupancy_second {n : Nat} (hn : 0 < n) (i : Fin n) :
    (∫ ω : Fin n → Real,
      (((Array.ofFn ω).toList.countP (fun x => decide (Nat.floor ((n : Real) * x) = i.val))
        : Real) ^ 2)
      ∂Measure.pi (fun _ : Fin n => cond (volume : Measure Real) (Ico 0 1))) =
      2 - 1 / (n : Real) := by
  let : IsProbabilityMeasure (cond (volume : Measure Real) (Ico 0 1)) :=
    cond_real_probability
  have h := variance_eq_sub (occupancy_memLp i)
  rw [occupancy_variance hn i, occupancy_mean hn i] at h
  change 1 - 1 / (n : Real) =
    (∫ ω : Fin n → Real,
      (((Array.ofFn ω).toList.countP (fun x => decide (Nat.floor ((n : Real) * x) = i.val))
        : Real) ^ 2)
      ∂Measure.pi (fun _ : Fin n => cond (volume : Measure Real) (Ico 0 1))) - 1 ^ 2 at h
  linarith

private lemma insert_ret_cons (a b : ℝ) (xs : List ℝ) :
    (List.orderedInsertM TimeM.compareLE a (b :: xs)).ret =
      if a ≤ b then a :: b :: xs else b :: (List.orderedInsertM TimeM.compareLE a xs).ret := by
  by_cases h : a ≤ b <;> simp [List.orderedInsertM_cons, TimeM.compareLE, TimeM.tick, h]

private lemma insert_time_cons (a b : ℝ) (xs : List ℝ) :
    (List.orderedInsertM TimeM.compareLE a (b :: xs)).time =
      if a ≤ b then 1 else 1 + (List.orderedInsertM TimeM.compareLE a xs).time := by
  by_cases h : a ≤ b <;> simp [List.orderedInsertM_cons, TimeM.compareLE, TimeM.tick, h]

private lemma ofFn_coordinate_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (f : Fin n → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (j : ℕ) :
    Measurable (fun ω => ((List.ofFn (fun i => f i ω))[j]?).getD 0) := by
  by_cases hj : j < n
  · simpa [List.getElem?_ofFn, hj] using hf ⟨j, hj⟩
  · simp only [List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_none]
    exact measurable_const

private lemma insert_measurable {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (a : Ω → ℝ) (f : Fin n → Ω → ℝ) (ha : Measurable a)
    (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω =>
        (List.orderedInsertM TimeM.compareLE (a ω) (List.ofFn (fun i => f i ω))).time) ∧
      ∀ j : ℕ, Measurable (fun ω =>
        ((List.orderedInsertM TimeM.compareLE (a ω)
          (List.ofFn (fun i => f i ω))).ret[j]?).getD 0) := by
  classical
  induction n with
  | zero =>
      constructor
      · simp
      · intro j
        cases j with
        | zero => simpa using ha
        | succ j => simp
  | succ n ih =>
      obtain ⟨ht, hr⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
      have hp : MeasurableSet {ω | a ω ≤ f 0 ω} := measurableSet_le ha (hf 0)
      constructor
      · simp_rw [List.ofFn_succ, insert_time_cons]
        exact Measurable.ite hp measurable_const (measurable_const.add ht)
      · intro j
        cases j with
        | zero =>
            have h : Measurable (fun ω => if a ω ≤ f 0 ω then a ω else f 0 ω) :=
              Measurable.ite hp ha (hf 0)
            simpa only [List.ofFn_succ, insert_ret_cons, List.getElem?_cons_zero,
              apply_ite (fun xs : List ℝ => (xs[0]?).getD 0), Option.getD_some] using h
        | succ j =>
            have h : Measurable (fun ω => if a ω ≤ f 0 ω then
                ((List.ofFn (fun i => f i ω))[j]?).getD 0 else
                ((List.orderedInsertM TimeM.compareLE (a ω)
                  (List.ofFn (fun i => f i.succ ω))).ret[j]?).getD 0) :=
              Measurable.ite hp (ofFn_coordinate_measurable f hf j) (hr j)
            simpa only [List.ofFn_succ, insert_ret_cons, List.getElem?_cons_succ,
              apply_ite (fun xs : List ℝ => (xs[j + 1]?).getD 0)] using h

private lemma ofFn_getD_eq {n : ℕ} (xs : List ℝ) (h : xs.length = n) :
    List.ofFn (fun i : Fin n => (xs[i.val]?).getD 0) = xs := by
  subst n
  have hfun : (fun i : Fin xs.length => (xs[i.val]?).getD 0) =
      (fun i : Fin xs.length => xs[i.val]) := by
    funext i
    rw [List.getElem?_eq_getElem i.isLt]
    rfl
  rw [hfun]
  exact List.ofFn_getElem

private lemma sort_measurable {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (f : Fin n → Ω → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => (TimeM.insertionSort (List.ofFn (fun i => f i ω))).time) ∧
      ∀ j : ℕ, Measurable (fun ω =>
        ((TimeM.insertionSort (List.ofFn (fun i => f i ω))).ret[j]?).getD 0) := by
  induction n with
  | zero =>
      constructor
      · simp [TimeM.insertionSort]
      · intro j
        simp [TimeM.insertionSort]
  | succ n ih =>
      obtain ⟨ht, hr⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
      let g : Fin n → Ω → ℝ := fun i ω =>
        ((TimeM.insertionSort (List.ofFn (fun j => f j.succ ω))).ret[i.val]?).getD 0
      have hg : ∀ i, Measurable (g i) := fun i => hr i.val
      have hrepr (ω : Ω) : List.ofFn (fun i => g i ω) =
          (TimeM.insertionSort (List.ofFn (fun i => f i.succ ω))).ret := by
        apply ofFn_getD_eq
        rw [(TimeM.insertionSort_perm _).length_eq, List.length_ofFn]
      obtain ⟨hit, hir⟩ := insert_measurable n (f 0) g (hf 0) hg
      constructor
      · simp_rw [List.ofFn_succ, TimeM.insertionSort, List.insertionSortM_cons, TimeM.time_bind]
        have h : Measurable (fun ω =>
            (TimeM.insertionSort (List.ofFn (fun i => f i.succ ω))).time +
              (List.orderedInsertM TimeM.compareLE (f 0 ω) (List.ofFn (fun i => g i ω))).time) :=
          ht.add hit
        simpa only [hrepr, TimeM.insertionSort] using h
      · intro j
        simp_rw [List.ofFn_succ, TimeM.insertionSort, List.insertionSortM_cons, TimeM.ret_bind]
        simpa only [hrepr, TimeM.insertionSort] using hir j

private lemma mapped_sort_measurable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*}
    (l : List ι) (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => (TimeM.insertionSort (l.map (fun i => f i ω))).time) := by
  have h := (sort_measurable l.length (fun j => f (l.get j)) (fun j => hf (l.get j))).1
  have hlist (ω : Ω) : List.ofFn (fun j => f (l.get j) ω) =
      l.map (fun i => f i ω) := by
    change List.ofFn ((fun i => f i ω) ∘ l.get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  simpa only [hlist] using h

private lemma bucket_comparisons_measurable (n : ℕ) (i : ℕ) :
    Measurable (fun ω : Fin n → ℝ => (TimeM.insertionSort
      ((List.ofFn ω).filter (fun x => decide (Nat.floor ((n : ℝ) * x) = i))).reverse).time) := by
  let h : (Fin n → ℝ) × (Fin n → Bool) → ℕ := fun p =>
    (TimeM.insertionSort (((List.ofFn id).filter p.2).reverse.map p.1)).time
  have hh : Measurable h := by
    apply measurable_from_prod_countable_left
    intro mask
    exact mapped_sort_measurable ((List.ofFn id).filter mask).reverse
      (fun j (ω : Fin n → ℝ) => ω j) (fun j => measurable_pi_apply j)
  have hm : Measurable (fun ω : Fin n → ℝ =>
      fun j => decide (Nat.floor ((n : ℝ) * ω j) = i)) := by
    apply Measurable.of_eval
    intro j
    apply measurable_to_bool
    simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq, Function.comp_def] using
      ((classifier_measurable n).comp (measurable_pi_apply j)) (measurableSet_singleton i)
  have hcomp := hh.comp (measurable_id.prodMk hm)
  have hlist (ω : Fin n → ℝ) :
      ((List.ofFn ω).filter (fun x => decide (Nat.floor ((n : ℝ) * x) = i))).reverse =
        ((List.ofFn id).filter (fun j => decide (Nat.floor ((n : ℝ) * ω j) = i))).reverse.map
          ω := by
    have hsource : List.ofFn ω = (List.ofFn id).map ω := by simp
    rw [hsource, List.filter_map, ← List.map_reverse]
    rfl
  change Measurable (fun ω : Fin n → ℝ => (TimeM.insertionSort
    (((List.ofFn id).filter (fun j => decide (Nat.floor ((n : ℝ) * ω j) = i))).reverse.map ω)).time)
    at hcomp
  simpa only [hlist] using hcomp

private lemma actual_time_filter_eq {n : ℕ} (_hn : 0 < n) (ω : Fin n → ℝ)
    (hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1) :
    (bucketSort (Array.ofFn ω) hx).time = 5 * n +
      ∑ i : Fin n, (TimeM.insertionSort
        ((List.ofFn ω).filter (fun x => decide
          (Nat.floor ((n : ℝ) * x) = i.val))).reverse).time := by
  rw [bucketSort_time (Array.ofFn ω) hx]
  simp only [Array.size_ofFn, Array.toList_ofFn]
  congr 1
  apply Fintype.sum_equiv (finCongr (Array.size_ofFn (f := ω)))
  intro i
  rfl

private lemma input_valid_iff {n : ℕ} (ω : Fin n → ℝ) :
    (∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1) ↔ ∀ i, ω i ∈ Ico 0 1 := by
  constructor
  · intro hx i
    exact hx (ω i) (Array.mem_toList_iff.mpr (Array.mem_ofFn.mpr ⟨i, rfl⟩))
  · intro hω x hx
    obtain ⟨i, rfl⟩ := Array.mem_ofFn.mp (Array.mem_toList_iff.mp hx)
    exact hω i

private lemma input_valid_measurable (n : ℕ) :
    MeasurableSet {ω : Fin n → ℝ | ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1} := by
  convert MeasurableSet.iInter (fun i : Fin n =>
    (measurable_pi_apply i) (measurableSet_Ico (a := (0 : ℝ)) (b := 1))) using 1
  ext ω
  simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq, input_valid_iff]

open Classical in
private lemma actual_time_measurable (n : ℕ) :
    Measurable (fun ω : Fin n → ℝ =>
      if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0) := by
  classical
  by_cases hn : 0 < n
  · have ht : Measurable (fun ω : Fin n → ℝ => 5 * n + ∑ i : Fin n,
        (TimeM.insertionSort ((List.ofFn ω).filter
          (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val))).reverse).time) :=
      measurable_const.add (Finset.measurable_sum Finset.univ
        (fun i _ => bucket_comparisons_measurable n i.val))
    have hc : Measurable (fun ω : Fin n → ℝ => ((5 * n + ∑ i : Fin n,
        (TimeM.insertionSort ((List.ofFn ω).filter
          (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val))).reverse).time : ℕ) : ℝ)) :=
      (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp ht
    have hfun : (fun ω : Fin n → ℝ =>
        if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
          ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0) =
        (fun ω : Fin n → ℝ =>
          if ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then ((5 * n + ∑ i : Fin n,
            (TimeM.insertionSort ((List.ofFn ω).filter
              (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val))).reverse).time : ℕ) : ℝ)
          else 0) := by
      funext ω
      by_cases hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1
      · simp only [dite_eq_left hx, ite_eq_left hx, actual_time_filter_eq hn ω hx]
      · simp only [dite_eq_right hx, ite_eq_right hx]
    rw [hfun]
    exact Measurable.ite (input_valid_measurable n) hc measurable_const
  · have hn0 : n = 0 := by omega
    subst n
    have harray (ω : Fin 0 → ℝ) : Array.ofFn ω = #[] :=
      Array.size_eq_zero_iff.mp (by simp)
    simp only [harray, bucketSort_empty, TimeM.time_pure, Nat.cast_zero]
    have hfun : (fun ω : Fin 0 → ℝ =>
        if hx : ∀ x ∈ (#[] : Array ℝ).toList, x ∈ Ico 0 1 then (0 : ℝ) else 0) =
        (fun _ : Fin 0 → ℝ => (0 : ℝ)) := by funext ω; split <;> rfl
    rw [hfun]
    exact measurable_const

private lemma insertion_comparisons_twice (xs : List ℝ) :
    2 * ((TimeM.insertionSort xs).time : ℝ) ≤ (xs.length : ℝ) ^ 2 - xs.length := by
  have h := TimeM.insertionSort_time xs
  have ht : 2 * (TimeM.insertionSort xs).time ≤ xs.length * (xs.length - 1) := by omega
  by_cases hn : xs.length = 0
  · have hnil := List.length_eq_zero_iff.mp hn
    subst xs
    simp [TimeM.insertionSort]
  · have hp : 1 ≤ xs.length := by omega
    have hreal : (2 : ℝ) * (TimeM.insertionSort xs).time ≤
        (xs.length : ℝ) * ((xs.length - 1 : ℕ) : ℝ) := by exact_mod_cast ht
    rw [Nat.cast_sub hp, Nat.cast_one] at hreal
    nlinarith

private lemma actual_time_valid_bounds {n : ℕ} (hn : 0 < n) (ω : Fin n → ℝ)
    (hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1) :
    5 * (n : ℝ) ≤ (bucketSort (Array.ofFn ω) hx).time ∧
      2 * ((bucketSort (Array.ofFn ω) hx).time : ℝ) ≤ 10 * n +
        ∑ i : Fin n, (((Array.ofFn ω).toList.countP
          (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2 -
          ((Array.ofFn ω).toList.countP
            (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ)) := by
  have hs : 2 * (∑ i : Fin n, ((TimeM.insertionSort
      ((List.ofFn ω).filter (fun x => decide
        (Nat.floor ((n : ℝ) * x) = i.val))).reverse).time : ℝ)) ≤
      ∑ i : Fin n, (((Array.ofFn ω).toList.countP
        (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2 -
        ((Array.ofFn ω).toList.countP
          (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [List.length_reverse, ← List.countP_eq_length_filter, Array.toList_ofFn] using
      insertion_comparisons_twice
        ((List.ofFn ω).filter (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val))).reverse
  rw [actual_time_filter_eq hn ω hx]
  push_cast
  constructor
  · exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
  · nlinarith

open Classical in
private lemma actual_time_nonneg {n : ℕ} (ω : Fin n → ℝ) :
    0 ≤ (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
      ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0) := by
  split
  · exact Nat.cast_nonneg _
  · rfl

open Classical in
private lemma actual_time_zero (ω : Fin 0 → ℝ) :
    (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
      ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0) = 0 := by
  have harray : Array.ofFn ω = #[] := Array.size_eq_zero_iff.mp (by simp)
  simp only [harray, bucketSort_empty, TimeM.time_pure, Nat.cast_zero]
  split <;> rfl

open Classical in
private lemma actual_time_le_squares {n : ℕ} (hn : 0 < n) (ω : Fin n → ℝ) :
    (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
      ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0) ≤ 5 * n +
      ∑ i : Fin n, ((Array.ofFn ω).toList.countP
        (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2 := by
  have hsq : 0 ≤ ∑ i : Fin n, ((Array.ofFn ω).toList.countP
      (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  by_cases hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1
  · simp only [dite_eq_left hx]
    have hb := (actual_time_valid_bounds hn ω hx).2
    have hd : ∑ i : Fin n, (((Array.ofFn ω).toList.countP
        (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2 -
        ((Array.ofFn ω).toList.countP
          (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ)) ≤
        ∑ i : Fin n, ((Array.ofFn ω).toList.countP
          (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun i _ => sub_le_self _ (Nat.cast_nonneg _))
    nlinarith
  · simp only [dite_eq_right hx]
    exact add_nonneg (by positivity) hsq

open Classical in
private lemma actual_time_integrable (n : ℕ) :
    Integrable (fun ω : Fin n → ℝ =>
      if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
      (Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) := by
  let : IsProbabilityMeasure (cond (volume : Measure ℝ) (Ico 0 1)) := cond_real_probability
  by_cases hn : 0 < n
  · have hg : Integrable (fun ω : Fin n → ℝ => 5 * (n : ℝ) +
        ∑ i : Fin n, ((Array.ofFn ω).toList.countP
          (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2)
        (Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) :=
      (integrable_const (5 * (n : ℝ))).add
        (integrable_finsetSum Finset.univ (fun i _ => (occupancy_memLp i).integrable_sq))
    exact hg.mono_nonneg (actual_time_measurable n).aestronglyMeasurable
      (ae_of_all _ actual_time_nonneg) (ae_of_all _ (actual_time_le_squares hn))
  · have hn0 : n = 0 := by omega
    subst n
    simp_rw [actual_time_zero]
    exact integrable_zero _ _ _

private lemma valid_array_ae (n : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1)),
      ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 := by
  let : IsProbabilityMeasure (cond (volume : Measure ℝ) (Ico 0 1)) := cond_real_probability
  have h : ∀ᵐ ω ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1)),
      ∀ i : Fin n, ω i ∈ Ico 0 1 := by
    apply Filter.eventually_all.2
    intro i
    exact Measure.tendsto_eval_ae_ae.eventually
      (ae_cond_mem (measurableSet_Ico (a := (0 : ℝ)) (b := 1)))
  exact h.mono (fun ω hω => (input_valid_iff ω).mpr hω)

private lemma occupancy_difference_integrable {n : ℕ} (i : Fin n) :
    Integrable (fun ω : Fin n → ℝ =>
      ((Array.ofFn ω).toList.countP
        (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2 -
      ((Array.ofFn ω).toList.countP
        (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ))
      (Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) := by
  let : IsProbabilityMeasure (cond (volume : Measure ℝ) (Ico 0 1)) := cond_real_probability
  exact (occupancy_memLp i).integrable_sq.sub
    ((occupancy_memLp i).integrable (by norm_num))

private lemma occupancy_difference_integral {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (∫ ω : Fin n → ℝ,
      (((Array.ofFn ω).toList.countP
        (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2 -
      ((Array.ofFn ω).toList.countP
        (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ))
      ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) = 1 - 1 / (n : ℝ) := by
  let : IsProbabilityMeasure (cond (volume : Measure ℝ) (Ico 0 1)) := cond_real_probability
  rw [integral_sub (occupancy_memLp i).integrable_sq
    ((occupancy_memLp i).integrable (by norm_num)), occupancy_second hn i, occupancy_mean hn i]
  ring

private lemma time_bound_integral {n : ℕ} (hn : 0 < n) :
    (∫ ω : Fin n → ℝ, 10 * (n : ℝ) +
      ∑ i : Fin n, (((Array.ofFn ω).toList.countP
        (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2 -
      ((Array.ofFn ω).toList.countP
        (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ))
      ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) =
      10 * n + n - 1 := by
  let : IsProbabilityMeasure (cond (volume : Measure ℝ) (Ico 0 1)) := cond_real_probability
  rw [integral_add (integrable_const (10 * (n : ℝ)))
    (integrable_finsetSum Finset.univ (fun i _ => occupancy_difference_integrable i)),
    integral_finsetSum Finset.univ (fun i _ => occupancy_difference_integrable i)]
  simp_rw [occupancy_difference_integral hn]
  simp only [integral_const, probReal_univ, one_smul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp
  ring

open Classical in
private lemma actual_time_expected_bounds {n : ℕ} (hn : 0 < n) :
    5 * (n : ℝ) ≤
      (∫ ω : Fin n → ℝ,
        (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
          ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
        ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) ∧
      (∫ ω : Fin n → ℝ,
        (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
          ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
        ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) ≤
        5 * n + ((n : ℝ) - 1) / 2 := by
  let : IsProbabilityMeasure (cond (volume : Measure ℝ) (Ico 0 1)) := cond_real_probability
  have hl : (fun _ : Fin n → ℝ => 5 * (n : ℝ)) ≤ᵐ[
      Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))]
      (fun ω => if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0) := by
    filter_upwards [valid_array_ae n] with ω hx
    simpa only [dite_eq_left hx] using (actual_time_valid_bounds hn ω hx).1
  have hu : (fun ω : Fin n → ℝ => 2 *
      (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)) ≤ᵐ[
      Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))]
      (fun ω => 10 * (n : ℝ) + ∑ i : Fin n, (((Array.ofFn ω).toList.countP
        (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2 -
        ((Array.ofFn ω).toList.countP
          (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ))) := by
    filter_upwards [valid_array_ae n] with ω hx
    simpa only [dite_eq_left hx] using (actual_time_valid_bounds hn ω hx).2
  constructor
  · have h := integral_mono_ae (integrable_const (5 * (n : ℝ))) (actual_time_integrable n) hl
    simpa using h
  · have h := integral_mono_ae ((actual_time_integrable n).const_mul 2)
      ((integrable_const (10 * (n : ℝ))).add
        (integrable_finsetSum Finset.univ (fun i _ => occupancy_difference_integrable i))) hu
    simp only [Pi.add_apply] at h
    rw [integral_const_mul, time_bound_integral hn] at h
    linarith

open Classical in
private lemma actual_time_expected_zero :
    (∫ ω : Fin 0 → ℝ,
      (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 0 => cond (volume : Measure ℝ) (Ico 0 1))) = 0 := by
  simp_rw [actual_time_zero]
  exact integral_zero _ _

/-- Each actual floor bucket has mean occupancy one under independent continuous uniforms. -/
public theorem bucketSort_occupancy_mean {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (∫ ω : Fin n → ℝ, ((Array.ofFn ω).toList.countP
      (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ)
      ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) = 1 :=
  occupancy_mean hn i

/-- Variance of the actual floor-bucket count in the continuous product model. -/
public theorem bucketSort_occupancy_variance {n : ℕ} (hn : 0 < n) (i : Fin n) :
    variance (fun ω : Fin n → ℝ => ((Array.ofFn ω).toList.countP
      (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ))
      (Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) =
      1 - 1 / (n : ℝ) := occupancy_variance hn i

/-- Second moment of the actual floor-bucket count under independent continuous uniforms. -/
public theorem bucketSort_occupancy_secondMoment {n : ℕ} (hn : 0 < n) (i : Fin n) :
    (∫ ω : Fin n → ℝ, ((Array.ofFn ω).toList.countP
      (fun x => decide (Nat.floor ((n : ℝ) * x) = i.val)) : ℝ) ^ 2
      ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) =
      2 - 1 / (n : ℝ) := occupancy_second hn i

open Classical in
/-- The actual conditional saved-bucket executor time is measurable, with no caller premise. -/
public theorem bucketSort_time_measurable (n : ℕ) :
    Measurable (fun ω : Fin n → ℝ =>
      if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0) :=
  actual_time_measurable n

open Classical in
/-- The actual conditional saved-bucket executor time is integrable for every input size. -/
public theorem bucketSort_time_integrable (n : ℕ) :
    Integrable (fun ω : Fin n → ℝ =>
      if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
      (Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) :=
  actual_time_integrable n

open Classical in
/-- Mandatory executed phase events give the continuous expected-time lower bound. -/
public theorem bucketSort_time_expected_lower {n : ℕ} (hn : 0 < n) :
    5 * (n : ℝ) ≤ (∫ ω : Fin n → ℝ,
      (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) :=
  (actual_time_expected_bounds hn).1

open Classical in
/-- Actual insertion comparisons give the sharper continuous expected-time upper bound. -/
public theorem bucketSort_time_expected_upper {n : ℕ} (hn : 0 < n) :
    (∫ ω : Fin n → ℝ,
      (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))) ≤
      5 * n + ((n : ℝ) - 1) / 2 := (actual_time_expected_bounds hn).2

open Classical in
/-- Empty continuous input has actual expected time zero. -/
public theorem bucketSort_time_expected_zero :
    (∫ ω : Fin 0 → ℝ,
      (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 0 => cond (volume : Measure ℝ) (Ico 0 1))) = 0 :=
  actual_time_expected_zero

open Classical in
/-- Singleton continuous input pays exactly the five executed phase events. -/
public theorem bucketSort_time_expected_one :
    (∫ ω : Fin 1 → ℝ,
      (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin 1 => cond (volume : Measure ℝ) (Ico 0 1))) = 5 := by
  obtain ⟨hl, hu⟩ := actual_time_expected_bounds (n := 1) (by decide)
  norm_num only [Nat.cast_one, mul_one, sub_self, zero_div, add_zero] at hl hu
  exact le_antisymm hu hl

open Classical in
/-- The actual continuous expected saved-bucket execution time is Theta of input size. -/
public theorem bucketSort_time_expected_isTheta :
    Asymptotics.IsTheta atTop
      (fun n : ℕ => ∫ ω : Fin n → ℝ,
        (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
          ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
        ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1)))
      (fun n : ℕ => (n : ℝ)) := by
  let f : ℕ → ℝ := fun n => ∫ ω : Fin n → ℝ,
    (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
      ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
    ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1))
  change Asymptotics.IsTheta atTop f (fun n : ℕ => (n : ℝ))
  have h : ∀ᶠ n : ℕ in atTop, 0 ≤ f n ∧ f n ≤ 6 * (n : ℝ) ∧ (n : ℝ) ≤ f n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : 0 < n := by omega
    have hl : 5 * (n : ℝ) ≤ f n := bucketSort_time_expected_lower hp
    have hu : f n ≤ 5 * n + ((n : ℝ) - 1) / 2 := bucketSort_time_expected_upper hp
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact ⟨by linarith, by linarith, by linarith⟩
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨6, h.mono ?_⟩
    intro n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn.1,
      abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)] using hn.2.1
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨1, h.mono ?_⟩
    intro n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn.1, one_mul,
      abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)] using hn.2.2

end Cslib.Algorithms.Lean.TimeM
