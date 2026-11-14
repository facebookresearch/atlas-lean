/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import MathlibExt.InformationTheory.FiniteEntropy

/-!
# Shannon conditional entropy through finite measurable quantizations

Conditional probabilities are conditional expectations of atom indicators.
Taking the supremum over finite quantizations extends discrete Shannon
conditional entropy to arbitrary measurable outputs, without using differential
entropy. Information is measured in bits.

For a finite joint law `p : PMF (α × β)` the last section computes these quantities:

* `measureMutualInformation_toMeasure`: the mutual information is
  `H(X) + H(Y) - H(X, Y)`, through Mathlib's `klDiv` on a finite space (`toReal_klDiv_eq_sum`).
* `shannonEntropy_le_add` (**subadditivity**) and `measureMutualInformation_toMeasure_eq_zero_iff`
  (zero exactly for independent coordinates).
* `finiteConditionalEntropy p = -∑ p(a, b) log₂ (p(a, b) / p_X(a))`, the chain rule
  `shannonEntropy_eq_add_finiteConditionalEntropy` (`H(X, Y) = H(X) + H(Y | X)`), and
  `finiteConditionalEntropy_le` (conditioning does not increase entropy).
-/

@[expose] public section

namespace InformationTheory

open MeasureTheory
open scoped BigOperators ENNReal

/-- Conditional Shannon entropy of a finite measurable observation, in bits. -/
noncomputable def quantizedConditionalEntropy {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (m : {m : MeasurableSpace Ω // m ≤ mΩ}) {n : ℕ}
    (f : Ω → Fin n) (_hf : Measurable f) : ℝ :=
  ∫ ω, (∑ i, Real.negMulLog
    (MeasureTheory.condExp m.1 μ.toMeasure (fun z => if f z = i then (1 : ℝ) else 0) ω)) /
      Real.log 2 ∂μ.toMeasure

/-- A singleton observation has zero conditional entropy. -/
@[simp] theorem quantizedConditionalEntropy_singleton {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (m : {m : MeasurableSpace Ω // m ≤ mΩ}) :
    quantizedConditionalEntropy μ m (fun _ : Ω => (0 : Fin 1)) measurable_const = 0 := by
  simp [quantizedConditionalEntropy, MeasureTheory.condExp_const m.2]

/-- Every constant finite observation has zero conditional entropy. -/
@[simp] theorem quantizedConditionalEntropy_const {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (m : {m : MeasurableSpace Ω // m ≤ mΩ}) {n : ℕ} (c : Fin n) :
    quantizedConditionalEntropy μ m (fun _ : Ω => c) measurable_const = 0 := by
  classical
  simp [quantizedConditionalEntropy, MeasureTheory.condExp_const m.2, apply_ite]

/-- Shannon conditional entropy of an output given a sub-sigma-algebra.
Source: the supremum over all finite measurable output quantizations. -/
noncomputable def conditionalShannonEntropy {Ω Y : Type*}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace Y] (μ : ProbabilityMeasure Ω)
    (m : {m : MeasurableSpace Ω // m ≤ mΩ}) (output : Ω → Y)
    (houtput : Measurable output) : ℝ≥0∞ :=
  sSup {h | ∃ (n : ℕ) (q : Y → Fin n) (hq : Measurable q),
    h = ENNReal.ofReal (quantizedConditionalEntropy μ m (q ∘ output) (hq.comp houtput))}

/-- The quantization supremum of an actual constant output is zero. -/
@[simp] theorem conditionalShannonEntropy_const {Ω Y : Type*}
    [mΩ : MeasurableSpace Ω] [MeasurableSpace Y] (μ : ProbabilityMeasure Ω)
    (m : {m : MeasurableSpace Ω // m ≤ mΩ}) (y : Y) :
    conditionalShannonEntropy μ m (fun _ : Ω => y) measurable_const = 0 := by
  apply le_antisymm ?_ bot_le
  unfold conditionalShannonEntropy
  apply sSup_le
  rintro h ⟨n, q, _, rfl⟩
  simp [Function.comp_def, quantizedConditionalEntropy_const]

/-- Mutual information of a joint probability law, in bits, allowing infinity.
Source: KL divergence from the actual product of the actual marginals. -/
noncomputable def measureMutualInformation {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : ProbabilityMeasure (X × Y)) : ℝ≥0∞ :=
  klDiv (μ : Measure (X × Y))
    (((μ : Measure (X × Y)).map Prod.fst).prod ((μ : Measure (X × Y)).map Prod.snd)) /
      ENNReal.ofReal (Real.log 2)

/-! ### Finite joint laws -/

section Finite

open Real

variable {α β : Type*}

theorem map_fst_apply [Finite α] (p : PMF (α × β)) [Fintype β] (a : α) :
    (p.map Prod.fst) a = ∑ b, p (a, b) := by
  classical
  have := Fintype.ofFinite α
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
    Finset.sum_eq_single a (fun x _ hx ↦ by simp [Ne.symm hx]) (by simp)]
  simp

theorem map_snd_apply [Fintype α] [Finite β] (p : PMF (α × β)) (b : β) :
    (p.map Prod.snd) b = ∑ a, p (a, b) := by
  classical
  have := Fintype.ofFinite β
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  simp

theorem toReal_map_fst_apply [Finite α] [Fintype β] (p : PMF (α × β)) (a : α) :
    ((p.map Prod.fst) a).toReal = ∑ b, (p (a, b)).toReal := by
  rw [map_fst_apply, ENNReal.toReal_sum fun b _ ↦ PMF.apply_ne_top p _]

theorem toReal_map_snd_apply [Fintype α] [Finite β] (p : PMF (α × β)) (b : β) :
    ((p.map Prod.snd) b).toReal = ∑ a, (p (a, b)).toReal := by
  rw [map_snd_apply, ENNReal.toReal_sum fun a _ ↦ PMF.apply_ne_top p _]

variable [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β]

theorem toMeasure_absolutelyContinuous_prod [Finite α] [Finite β] (p : PMF (α × β)) :
    p.toMeasure ≪ (p.map Prod.fst).toMeasure.prod (p.map Prod.snd).toMeasure := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  refine Measure.AbsolutelyContinuous.mk fun s hsm hs ↦ ?_
  rw [← Set.biUnion_of_singleton s, measure_biUnion_null_iff s.toFinite.countable]
  rintro ⟨a, b⟩ hz
  have h0 := measure_mono_null (Set.singleton_subset_iff.mpr hz) hs
  rw [← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), mul_eq_zero,
    map_fst_apply, map_snd_apply, Finset.sum_eq_zero_iff, Finset.sum_eq_zero_iff] at h0
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rcases h0 with h | h
  · exact h b (Finset.mem_univ b)
  · exact h a (Finset.mem_univ a)

/-- The divergence of a finite joint law from the product of its marginals, in nats, is
`(H(X) + H(Y) - H(X, Y)) log 2`. -/
theorem toReal_klDiv_prod [Fintype α] [Fintype β] (p : PMF (α × β)) :
    (klDiv p.toMeasure ((p.map Prod.fst).toMeasure.prod (p.map Prod.snd).toMeasure)).toReal =
      (shannonEntropy (p.map Prod.fst) + shannonEntropy (p.map Prod.snd) - shannonEntropy p) *
        log 2 := by
  set P : α → β → ℝ := fun a b ↦ (p (a, b)).toReal with hP
  have hX : ∀ a, ((p.map Prod.fst) a).toReal = ∑ b, P a b := toReal_map_fst_apply p
  have hY : ∀ b, ((p.map Prod.snd) b).toReal = ∑ a, P a b := toReal_map_snd_apply p
  have hP0 : ∀ a b, 0 ≤ P a b := fun _ _ ↦ ENNReal.toReal_nonneg
  have hle1 : ∀ a b, P a b ≤ ∑ b', P a b' := fun a b ↦
    Finset.single_le_sum (fun b' _ ↦ hP0 a b') (Finset.mem_univ b)
  have hle2 : ∀ a b, P a b ≤ ∑ a', P a' b := fun a b ↦
    Finset.single_le_sum (fun a' _ ↦ hP0 a' b) (Finset.mem_univ a)
  have hsing : ∀ a b, ((p.map Prod.fst).toMeasure.prod (p.map Prod.snd).toMeasure).real {(a, b)} =
      ((p.map Prod.fst) a).toReal * ((p.map Prod.snd) b).toReal := fun a b ↦ by
    rw [measureReal_def, ← Set.singleton_prod_singleton, Measure.prod_prod,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton a),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), ENNReal.toReal_mul]
  rw [toReal_klDiv_eq_sum (toMeasure_absolutelyContinuous_prod p) (by simp),
    Fintype.sum_prod_type]
  simp only [toMeasure_real_singleton, hsing, hX, hY]
  change ∑ a, ∑ b, P a b * log (P a b / ((∑ b', P a b') * ∑ a', P a' b)) = _
  have hterm : ∀ a b, P a b * log (P a b / ((∑ b', P a b') * (∑ a', P a' b))) =
      P a b * log (P a b) - P a b * log (∑ b', P a b') - P a b * log (∑ a', P a' b) := by
    intro a b
    rcases (hP0 a b).eq_or_lt with h | h
    · rw [← h]
      simp
    · have h1 : 0 < ∑ b', P a b' := h.trans_le (hle1 a b)
      have h2 : 0 < ∑ a', P a' b := h.trans_le (hle2 a b)
      rw [log_div h.ne' (mul_pos h1 h2).ne', log_mul h1.ne' h2.ne']
      ring
  simp_rw [hterm, Finset.sum_sub_distrib]
  have hlog : log 2 ≠ 0 := (log_pos one_lt_two).ne'
  have hHX : shannonEntropy (p.map Prod.fst) * log 2 =
      -∑ a, ∑ b, P a b * log (∑ b', P a b') := by
    rw [shannonEntropy, div_mul_cancel₀ _ hlog, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [hX, negMulLog, ← Finset.sum_mul]
    ring
  have hHY : shannonEntropy (p.map Prod.snd) * log 2 =
      -∑ a, ∑ b, P a b * log (∑ a', P a' b) := by
    rw [Finset.sum_comm, shannonEntropy, div_mul_cancel₀ _ hlog, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [hY, negMulLog, ← Finset.sum_mul]
    ring
  have hH : shannonEntropy p * log 2 = -∑ a, ∑ b, P a b * log (P a b) := by
    rw [shannonEntropy, div_mul_cancel₀ _ hlog, Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [negMulLog, hP]
    ring
  rw [sub_mul, add_mul, hHX, hHY, hH]
  ring

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
/-- **Subadditivity of entropy**: `H(X, Y) ≤ H(X) + H(Y)`. -/
theorem shannonEntropy_le_add [Fintype α] [Fintype β] (p : PMF (α × β)) :
    shannonEntropy p ≤ shannonEntropy (p.map Prod.fst) + shannonEntropy (p.map Prod.snd) := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  have : MeasurableSingletonClass α := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have : MeasurableSingletonClass β := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have h := toReal_klDiv_prod p
  have h0 : 0 ≤ (shannonEntropy (p.map Prod.fst) + shannonEntropy (p.map Prod.snd) -
      shannonEntropy p) * log 2 := h ▸ ENNReal.toReal_nonneg
  have := nonneg_of_mul_nonneg_left h0 (log_pos one_lt_two)
  linarith

/-- **Mutual information of a finite joint law**: `I(X; Y) = H(X) + H(Y) - H(X, Y)`, in bits. -/
theorem measureMutualInformation_toMeasure [Fintype α] [Fintype β] (p : PMF (α × β)) :
    measureMutualInformation (⟨p.toMeasure, inferInstance⟩ : ProbabilityMeasure (α × β)) =
      ENNReal.ofReal
        (shannonEntropy (p.map Prod.fst) + shannonEntropy (p.map Prod.snd) - shannonEntropy p) := by
  have hne := klDiv_ne_top (toMeasure_absolutelyContinuous_prod p)
    (Integrable.of_finite (f := llr p.toMeasure
      ((p.map Prod.fst).toMeasure.prod (p.map Prod.snd).toMeasure)))
  change klDiv p.toMeasure ((p.toMeasure.map Prod.fst).prod (p.toMeasure.map Prod.snd)) /
    ENNReal.ofReal (log 2) = _
  rw [PMF.toMeasure_map Prod.fst p measurable_fst, PMF.toMeasure_map Prod.snd p measurable_snd,
    ← ENNReal.ofReal_toReal hne, ← ENNReal.ofReal_div_of_pos (log_pos one_lt_two),
    toReal_klDiv_prod, mul_div_cancel_right₀ _ (log_pos one_lt_two).ne']

omit [MeasurableSingletonClass α] [MeasurableSingletonClass β] in
/-- The mutual information of a joint law given by a `PMF` vanishes exactly when the coordinates
are independent. -/
theorem measureMutualInformation_toMeasure_eq_zero_iff (p : PMF (α × β)) :
    measureMutualInformation (⟨p.toMeasure, inferInstance⟩ : ProbabilityMeasure (α × β)) = 0 ↔
      p.toMeasure = (p.map Prod.fst).toMeasure.prod (p.map Prod.snd).toMeasure := by
  change klDiv p.toMeasure ((p.toMeasure.map Prod.fst).prod (p.toMeasure.map Prod.snd)) /
    ENNReal.ofReal (log 2) = 0 ↔ _
  rw [PMF.toMeasure_map Prod.fst p measurable_fst, PMF.toMeasure_map Prod.snd p measurable_snd,
    ENNReal.div_eq_zero_iff, or_iff_left ENNReal.ofReal_ne_top, klDiv_eq_zero_iff]

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
/-- The conditional entropy `H(Y | X) = -∑ p(a, b) log₂ (p(a, b) / p_X(a))` of a finite joint law,
in bits: the finite counterpart of `conditionalShannonEntropy`. -/
noncomputable def finiteConditionalEntropy [Fintype α] [Fintype β] (p : PMF (α × β)) : ℝ :=
  -∑ a, ∑ b, (p (a, b)).toReal * logb 2 ((p (a, b)).toReal / ((p.map Prod.fst) a).toReal)

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
/-- **Chain rule**: `H(X, Y) = H(X) + H(Y | X)`. -/
theorem shannonEntropy_eq_add_finiteConditionalEntropy [Fintype α] [Fintype β]
    (p : PMF (α × β)) :
    shannonEntropy p = shannonEntropy (p.map Prod.fst) + finiteConditionalEntropy p := by
  have hX := toReal_map_fst_apply p
  have hlog : log 2 ≠ 0 := (log_pos one_lt_two).ne'
  rw [shannonEntropy, Fintype.sum_prod_type, shannonEntropy, finiteConditionalEntropy,
    ← sub_eq_iff_eq_add', ← sub_div, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hX, negMulLog]
  simp only [neg_mul, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib,
    sub_neg_eq_add, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rcases (ENNReal.toReal_nonneg : 0 ≤ (p (a, b)).toReal).eq_or_lt with h | h
  · rw [← h]
    simp
  · have h1 : 0 < ∑ b', (p (a, b')).toReal :=
      h.trans_le (Finset.single_le_sum (f := fun b' ↦ (p (a, b')).toReal)
        (fun b' _ ↦ ENNReal.toReal_nonneg) (Finset.mem_univ b))
    rw [negMulLog, logb, log_div h.ne' h1.ne']
    field_simp
    ring

omit [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] in
/-- **Conditioning does not increase entropy**: `H(Y | X) ≤ H(Y)`. -/
theorem finiteConditionalEntropy_le [Fintype α] [Fintype β] (p : PMF (α × β)) :
    finiteConditionalEntropy p ≤ shannonEntropy (p.map Prod.snd) := by
  have h1 := shannonEntropy_eq_add_finiteConditionalEntropy p
  have h2 := shannonEntropy_le_add p
  linarith

end Finite

end InformationTheory
