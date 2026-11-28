/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Knockoff
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# False discovery rate control by the knockoff filter

The knockoff filter of R. F. Barber and E. J. Candès (*Controlling the false discovery rate via
knockoffs*, Ann. Statist. 43 (2015), arXiv:1404.5609) and its model-X form (E. Candès, Y. Fan,
L. Janson and J. Lv, *Panning for gold*, J. R. Statist. Soc. B 80 (2018), arXiv:1610.02351)
controls the false discovery rate in finite samples. Both proofs have two parts: a construction
(fixed-design knockoffs for the Gaussian linear model, or model-X knockoffs with
`(X, X̃)_swap(S) =ᵈ (X, X̃)` and `X̃ ⊥ Y | X`) that makes the signs of the null statistics `W_j`
i.i.d. fair coins independent of `|W|` (Barber–Candès Lemma 1; Candès et al. Lemma 3.3), and a
probabilistic argument showing that any statistics with that sign property give FDR control
(Barber–Candès Theorems 1-2; Candès et al. Theorem 3.4, whose proof "is the same as that of
Theorems 1 and 2 in [Barber–Candès], since all we need is that the null statistics have signs
distributed as i.i.d. coin flips"). The statements below are the second part, FDR control by
knockoff+ and modified FDR control by knockoff, with the sign property written as invariance of
the law of `W` under flipping the signs of any set of null statistics (`flipSigns`), which is how
both lemmas are proved.

Both proofs use the leave-one-out argument of Barber, Candès and Samworth, *Robust inference with
knockoffs*, arXiv:1801.03896, Appendix A.1 and Lemma 6, which treats the knockoff+ threshold
(offset `1`) and the knockoff threshold (offset `0`) alike.

## Main results

* `integral_falseDiscoveryProportion_knockoffSelection_one_le`: knockoff+ controls the false
  discovery rate, `E[|Ŝ ∩ H0| / (|Ŝ| ∨ 1)] ≤ q`.
* `integral_card_inter_div_knockoffSelection_zero_le`: knockoff controls the modified false
  discovery rate, `E[|Ŝ ∩ H0| / (|Ŝ| + q⁻¹)] ≤ q`.
-/

@[expose] public section

open Finset MeasureTheory
open MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Probability.Statistics.MultipleTesting.Knockoff

namespace MathlibExt.Probability.KnockoffFDRWanted

variable {p : ℕ}

private noncomputable def estimatedFDP (c : ℕ) (w : Fin p → ℝ) (t : ℝ) : ℝ :=
  ((c : ℝ) + ((univ.filter fun i => w i ≤ -t).card : ℝ)) /
    max ((univ.filter fun i => t ≤ w i).card : ℝ) 1

private theorem threshold_le_coe_iff {c : ℕ} {q r : ℝ} {w : Fin p → ℝ} :
    knockoffThreshold c q w ≤ (r : WithTop ℝ) ↔
      ∃ j, w j ≠ 0 ∧ estimatedFDP c w |w j| ≤ q ∧ |w j| ≤ r := by
  simp [knockoffThreshold, estimatedFDP, Finset.inf_le_iff, and_assoc]

private theorem measurable_filter {α : Type*} [MeasurableSpace α] (s : Finset (Fin p))
    {P : α → Fin p → Prop} [∀ x, DecidablePred (P x)]
    (hP : ∀ i, MeasurableSet {x | P x i}) :
    Measurable fun x => s.filter (P x) := by
  refine measurable_finset_iff.2 fun i => measurableSet_setOfPred.1 ?_
  by_cases hi : i ∈ s
  · simpa [hi] using hP i
  · simp [hi]

private theorem measurable_estimatedFDP (c : ℕ) (t : (Fin p → ℝ) → ℝ) (ht : Measurable t) :
    Measurable fun w => estimatedFDP c w (t w) := by
  unfold estimatedFDP
  have hneg : Measurable (fun w => univ.filter fun i => w i ≤ -t w) :=
    measurable_filter _ fun i => measurableSet_le (measurable_pi_apply i) ht.neg
  have hpos : Measurable (fun w => univ.filter fun i => t w ≤ w i) :=
    measurable_filter _ fun i => measurableSet_le ht (measurable_pi_apply i)
  have hcard : Measurable (fun s : Finset (Fin p) => (s.card : ℝ)) := measurable_of_countable _
  exact (measurable_const.add (hcard.comp hneg)).div ((hcard.comp hpos).max measurable_const)

private theorem measurableSet_threshold_le (c : ℕ) (q : ℝ) (r : (Fin p → ℝ) → ℝ)
    (hr : Measurable r) :
    MeasurableSet {w | knockoffThreshold c q w ≤ (r w : WithTop ℝ)} := by
  simp_rw [threshold_le_coe_iff, Set.ofPred_exists]
  refine MeasurableSet.iUnion fun j : Fin p => ?_
  have hj : Measurable fun w : Fin p → ℝ => w j := measurable_pi_apply j
  have habs : Measurable fun w : Fin p → ℝ => |w j| := by
    simp_rw [abs_eq_max_neg]
    exact hj.max hj.neg
  exact (measurableSet_eq_fun hj measurable_const).compl.inter
    ((measurableSet_le (measurable_estimatedFDP c _ habs) measurable_const).inter
      (measurableSet_le habs hr))

private theorem measurable_selection (c : ℕ) (q : ℝ) :
    Measurable (knockoffSelection c q : (Fin p → ℝ) → Finset (Fin p)) := by
  unfold knockoffSelection
  exact measurable_filter _ fun j => measurableSet_threshold_le c q _ (measurable_pi_apply j)

private noncomputable def negatives (c : ℕ) (H0 : Finset (Fin p)) (q : ℝ) (w : Fin p → ℝ) :
    Finset (Fin p) :=
  H0.filter fun j => knockoffThreshold c q w ≤ ((-w j : ℝ) : WithTop ℝ)

private theorem measurable_negatives (c : ℕ) (H0 : Finset (Fin p)) (q : ℝ) :
    Measurable (negatives c H0 q) := by
  unfold negatives
  exact measurable_filter _ fun j => measurableSet_threshold_le c q _ (measurable_pi_apply j).neg

-- At a finite threshold `t`, the null negatives are the nulls with `w j ≤ -t`.
private theorem negatives_eq_filter {c : ℕ} {q t : ℝ} {w : Fin p → ℝ}
    (ht : knockoffThreshold c q w = (t : WithTop ℝ)) (H0 : Finset (Fin p)) :
    negatives c H0 q w = H0.filter (fun j => w j ≤ -t) := by
  ext j
  simp only [negatives, mem_filter, ht, WithTop.coe_le_coe]
  exact and_congr_right fun _ => by constructor <;> intro h <;> linarith

private noncomputable def nullWeight (c : ℕ) (H0 : Finset (Fin p)) (q : ℝ) (j : Fin p)
    (w : Fin p → ℝ) : ℝ :=
  if j ∈ knockoffSelection c q w then 1 / (1 + ((negatives c H0 q w).card : ℝ)) else 0

private theorem measurable_nullWeight (c : ℕ) (H0 : Finset (Fin p)) (q : ℝ) (j : Fin p) :
    Measurable (nullWeight c H0 q j) := by
  unfold nullWeight
  have hc : Measurable fun w => ((negatives c H0 q w).card : ℝ) :=
    (measurable_of_countable fun s : Finset (Fin p) => (s.card : ℝ)).comp
      (measurable_negatives c H0 q)
  exact ((measurable_const.div (measurable_const.add hc)).ite
    ((measurable_selection c q) (measurableSet_mem_finset j)) measurable_const)

private theorem norm_nullWeight_le_one (c : ℕ) (H0 : Finset (Fin p)) (q : ℝ) (j : Fin p)
    (w : Fin p → ℝ) : ‖nullWeight c H0 q j w‖ ≤ 1 := by
  unfold nullWeight
  split_ifs
  · rw [Real.norm_of_nonneg (by positivity), div_le_one (by positivity)]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  · simp

-- The total null weight is the number of selected nulls over one plus the null negatives.
private theorem sum_nullWeight_eq (c : ℕ) (H0 : Finset (Fin p)) (q : ℝ) (w : Fin p → ℝ) :
    ∑ j ∈ H0, nullWeight c H0 q j w =
      ((knockoffSelection c q w ∩ H0).card : ℝ) / (1 + ((negatives c H0 q w).card : ℝ)) := by
  classical
  unfold nullWeight
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one_div, filter_mem_eq_inter, inter_comm H0]

private theorem measurable_flip (S : Finset (Fin p)) :
    Measurable (flipSigns S : (Fin p → ℝ) → (Fin p → ℝ)) := by
  refine measurable_pi_iff.2 fun i => ?_
  change Measurable (fun w : Fin p → ℝ => if i ∈ S then -w i else w i)
  split_ifs
  · exact (measurable_pi_apply i).neg
  · exact measurable_pi_apply i

private theorem abs_flip (S : Finset (Fin p)) (w : Fin p → ℝ) (j : Fin p) :
    |flipSigns S w j| = |w j| := by
  by_cases h : j ∈ S <;> simp [flipSigns, h]

-- Swapping the two flipped coordinates exchanges their memberships in each threshold count.
private theorem card_filter_flip_eq (w : Fin p → ℝ) (j k : Fin p) (P : ℝ → Prop)
    [DecidablePred P] (hpos : P (-w j) ↔ P (-w k)) (hneg : P (w k) ↔ P (w j)) :
    (univ.filter fun i => P (flipSigns {j} w i)).card =
      (univ.filter fun i => P (flipSigns {k} w i)).card := by
  by_cases hjk : j = k
  · subst k
    rfl
  refine Finset.card_bijective (Equiv.swap j k) (Equiv.swap j k).bijective fun i => ?_
  simp only [mem_filter, mem_univ, true_and]
  rcases eq_or_ne i j with rfl | hij
  · simpa [flipSigns] using hpos
  rcases eq_or_ne i k with rfl | hik
  · simpa [flipSigns, hjk, Ne.symm hjk] using hneg
  rw [Equiv.swap_apply_of_ne_of_ne hij hik]
  simp [flipSigns, hij, hik]

private theorem estimatedFDP_flip_eq (c : ℕ) {w : Fin p → ℝ} {j k : Fin p} {t : ℝ}
    (ht : 0 < t) (hj : t ≤ -w j) (hk : t ≤ -w k) :
    estimatedFDP c (flipSigns {j} w) t = estimatedFDP c (flipSigns {k} w) t := by
  unfold estimatedFDP
  have hneg := card_filter_flip_eq w j k (fun x => x ≤ -t)
    (iff_of_false (by linarith) (by linarith)) (iff_of_true (by linarith) (by linarith))
  have hpos := card_filter_flip_eq w j k (fun x => t ≤ x)
    (iff_of_true hj hk) (iff_of_false (by linarith) (by linarith))
  rw [hneg, hpos]

private theorem threshold_le_of_mem_selection {c : ℕ} {q : ℝ} {w : Fin p → ℝ} {j : Fin p}
    (hj : j ∈ knockoffSelection c q w) :
    knockoffThreshold c q w ≤ (w j : WithTop ℝ) :=
  (mem_filter.mp hj).2

-- At the smaller threshold both flipped coordinates have magnitude at least that threshold.
-- The two counts agree there, so the smaller threshold is a candidate for the other vector too.
private theorem flipped_threshold_le_of_le {c : ℕ} {q : ℝ} {w : Fin p → ℝ} {j k : Fin p}
    (hj : j ∈ knockoffSelection c q (flipSigns {j} w))
    (hk : k ∈ knockoffSelection c q (flipSigns {k} w))
    (hjk : knockoffThreshold c q (flipSigns {j} w) ≤ knockoffThreshold c q (flipSigns {k} w)) :
    knockoffThreshold c q (flipSigns {k} w) ≤ knockoffThreshold c q (flipSigns {j} w) := by
  have hj' := threshold_le_of_mem_selection hj
  have hk' := hjk.trans (threshold_le_of_mem_selection hk)
  cases ht : knockoffThreshold c q (flipSigns {j} w) with
  | top => exact le_top
  | coe t =>
    rw [ht, WithTop.coe_le_coe] at hj' hk'
    have hcounts := estimatedFDP_flip_eq c (pos_of_knockoffThreshold_eq_coe ht)
      (by simpa [flipSigns] using hj') (by simpa [flipSigns] using hk')
    obtain ⟨i, hi0, hiq, hit⟩ := exists_eq_of_knockoffThreshold_eq_coe ht
    have habs : |flipSigns {k} w i| = |flipSigns {j} w i| := by rw [abs_flip, abs_flip]
    refine threshold_le_coe_iff.2 ⟨i, ?_, ?_, (habs.trans hit).le⟩
    · exact abs_pos.mp (habs ▸ abs_pos.mpr hi0)
    · rw [habs, hit, ← hcounts, ← hit]
      simpa [estimatedFDP] using hiq

private theorem flipped_threshold_eq {c : ℕ} {q : ℝ} {w : Fin p → ℝ} {j k : Fin p}
    (hj : j ∈ knockoffSelection c q (flipSigns {j} w))
    (hk : k ∈ knockoffSelection c q (flipSigns {k} w)) :
    knockoffThreshold c q (flipSigns {j} w) = knockoffThreshold c q (flipSigns {k} w) := by
  rcases le_total (knockoffThreshold c q (flipSigns {j} w))
      (knockoffThreshold c q (flipSigns {k} w)) with h | h
  · exact h.antisymm (flipped_threshold_le_of_le hj hk h)
  · exact (flipped_threshold_le_of_le hk hj h).antisymm h

private theorem sum_flipped_nullWeight_le_one (c : ℕ) (H0 : Finset (Fin p)) (q : ℝ)
    (w : Fin p → ℝ) : ∑ j ∈ H0, nullWeight c H0 q j (flipSigns {j} w) ≤ 1 := by
  classical
  let eligible := H0.filter fun j => j ∈ knockoffSelection c q (flipSigns {j} w)
  unfold nullWeight
  rw [← sum_filter]
  change ∑ j ∈ eligible, 1 / (1 + ((negatives c H0 q (flipSigns {j} w)).card : ℝ)) ≤ 1
  calc
    _ ≤ ∑ _j ∈ eligible, 1 / (eligible.card : ℝ) := by
      apply sum_le_sum
      intro j hj
      have hsel := (mem_filter.mp hj).2
      -- Every other index selected after its own flip is negative at the common threshold.
      have hsub : eligible.erase j ⊆ negatives c H0 q (flipSigns {j} w) := by
        intro k hk
        obtain ⟨hkj, hkeligible⟩ := mem_erase.mp hk
        obtain ⟨hk0, hksel⟩ := mem_filter.mp hkeligible
        have hT := flipped_threshold_eq hsel hksel
        have hle := threshold_le_of_mem_selection hksel
        exact mem_filter.mpr ⟨hk0, by simpa [hT, flipSigns, hkj] using hle⟩
      have hcard := Nat.succ_le_succ (card_le_card hsub)
      rw [Nat.succ_eq_add_one, card_erase_add_one hj, Nat.succ_eq_add_one, add_comm _ 1] at hcard
      have hpos : 0 < eligible.card := card_pos.mpr ⟨j, hj⟩
      exact one_div_le_one_div_of_le (by exact_mod_cast hpos) (by exact_mod_cast hcard)
    _ = (eligible.card : ℝ) / (eligible.card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ 1 := div_self_le_one _

private theorem fdp_le_sum_nullWeight (H0 : Finset (Fin p)) (q : ℝ) (w : Fin p → ℝ) :
    falseDiscoveryProportion H0 (knockoffSelection 1 q w) ≤
      q * ∑ j ∈ H0, nullWeight 1 H0 q j w := by
  rw [sum_nullWeight_eq]
  cases ht : knockoffThreshold 1 q w with
  | top =>
    have he : knockoffSelection 1 q w = ∅ := by ext j; simp [knockoffSelection, ht]
    simp [he, falseDiscoveryProportion]
  | coe t =>
    rw [negatives_eq_filter ht, ← mul_div_assoc]
    exact falseDiscoveryProportion_knockoffSelection_one_le ht H0

-- At a finite knockoff threshold `t`, a nonempty selection `Ŝ` has `#{j : w j ≤ -t} ≤ q · #Ŝ`.
-- So `1 + #{j ∈ H0 : w j ≤ -t} ≤ q (#Ŝ + q⁻¹)` whenever a null is selected.
private theorem card_inter_div_le_sum_nullWeight (H0 : Finset (Fin p)) {q : ℝ} (hq : 0 < q)
    (w : Fin p → ℝ) :
    ((knockoffSelection 0 q w ∩ H0).card : ℝ) / ((knockoffSelection 0 q w).card + q⁻¹) ≤
      q * ∑ j ∈ H0, nullWeight 0 H0 q j w := by
  rw [sum_nullWeight_eq]
  cases ht : knockoffThreshold 0 q w with
  | top =>
    have he : knockoffSelection 0 q w = ∅ := by ext j; simp [knockoffSelection, ht]
    simp [he]
  | coe t =>
    rw [negatives_eq_filter ht]
    have hratio := knockoffThreshold_ratio_le ht
    set A := knockoffSelection 0 q w ∩ H0
    set s : ℝ := ((knockoffSelection 0 q w).card : ℝ)
    set N : ℝ := ((univ.filter fun i => w i ≤ -t).card : ℝ)
    set N0 : ℝ := ((H0.filter fun j => w j ≤ -t).card : ℝ)
    rcases A.eq_empty_or_nonempty with hA | hA
    · simp [hA]
    have hs : (1 : ℝ) ≤ s :=
      Nat.one_le_cast.mpr (card_pos.mpr (hA.mono inter_subset_left))
    have hN0N : N0 ≤ N := by
      simp only [N0, N]
      exact_mod_cast Finset.card_le_card fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; exact hj.2
    have hNs : N ≤ q * s := by
      rw [max_eq_left hs, Nat.cast_zero, zero_add, div_le_iff₀ (by linarith)] at hratio
      linarith
    have hN0 : 0 ≤ N0 := Nat.cast_nonneg _
    have ha : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg _
    have hden : s + q⁻¹ = (q * s + 1) / q := by field_simp
    rw [hden, div_div_eq_mul_div, mul_comm _ q, mul_div_assoc]
    gcongr q * (_ / ?_)
    linarith

-- The leave-one-out step: the null weights have expectation at most one, because flipping the
-- sign of a single null coordinate preserves the law of `W`, and after their own flips the null
-- weights sum to at most one.
private theorem integral_le_of_le_mul_sum_nullWeight {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {W : Ω → Fin p → ℝ} (hW : Measurable W)
    (H0 : Finset (Fin p)) (hflip : ∀ S ⊆ H0, μ.map (fun ω => flipSigns S (W ω)) = μ.map W)
    (c : ℕ) {q : ℝ} (hq0 : 0 ≤ q) {f : Ω → ℝ} (hf0 : ∀ ω, 0 ≤ f ω)
    (hf : ∀ ω, f ω ≤ q * ∑ j ∈ H0, nullWeight c H0 q j (W ω)) :
    ∫ ω, f ω ∂μ ≤ q := by
  have hflipMeas (j : Fin p) : Measurable fun ω => flipSigns {j} (W ω) :=
    (measurable_flip _).comp hW
  have hWeightInt (j : Fin p) {U : Ω → Fin p → ℝ} (hU : Measurable U) :
      Integrable (fun ω => nullWeight c H0 q j (U ω)) μ :=
    Integrable.of_bound ((measurable_nullWeight c H0 q j).comp hU).aestronglyMeasurable 1
      (ae_of_all _ fun ω => norm_nullWeight_le_one c H0 q j (U ω))
  have hFlippedInt (j : Fin p) :
      Integrable (fun ω => nullWeight c H0 q j (flipSigns {j} (W ω))) μ :=
    hWeightInt j (hflipMeas j)
  have hIntegral (j : Fin p) (hj : j ∈ H0) :
      ∫ ω, nullWeight c H0 q j (W ω) ∂μ =
        ∫ ω, nullWeight c H0 q j (flipSigns {j} (W ω)) ∂μ := by
    have hm := (measurable_nullWeight c H0 q j).aestronglyMeasurable (μ := μ.map W)
    rw [← integral_map hW.aemeasurable hm, ← hflip {j} (singleton_subset_iff.mpr hj)]
    exact integral_map (hflipMeas j).aemeasurable
      (measurable_nullWeight c H0 q j).aestronglyMeasurable
  calc
    _ ≤ ∫ ω, q * ∑ j ∈ H0, nullWeight c H0 q j (W ω) ∂μ :=
      integral_mono_of_nonneg (ae_of_all _ hf0)
        ((integrable_finsetSum _ fun j _ => hWeightInt j hW).const_mul q) (ae_of_all _ hf)
    _ = q * ∑ j ∈ H0, ∫ ω, nullWeight c H0 q j (W ω) ∂μ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hWeightInt j hW)]
    _ = q * ∫ ω, ∑ j ∈ H0, nullWeight c H0 q j (flipSigns {j} (W ω)) ∂μ := by
      rw [integral_finsetSum _ (fun j _ => hFlippedInt j)]
      congr 1
      exact sum_congr rfl hIntegral
    _ ≤ q * ∫ _ : Ω, (1 : ℝ) ∂μ :=
      mul_le_mul_of_nonneg_left
        (integral_mono (integrable_finsetSum _ fun j _ => hFlippedInt j) (integrable_const _)
          (fun ω => sum_flipped_nullWeight_le_one c H0 q (W ω))) hq0
    _ = q := by simp

set_option linter.unusedVariables false in
/-- **FDR control by knockoff+.** Let `W : Ω → ℝ^p` be measurable statistics on a probability
space and `H0` the set of null variables, and suppose that flipping the signs of any set `S ⊆ H0`
of null statistics leaves the law of `W` unchanged. Then for `0 ≤ q ≤ 1` the knockoff+ selection
`Ŝ = {j : W_j ≥ T₊}` has false discovery rate `E[|Ŝ ∩ H0| / (|Ŝ| ∨ 1)] ≤ q`.

Source: R. F. Barber and E. J. Candès, *Controlling the false discovery rate via knockoffs*,
Ann. Statist. 43 (2015) 2055-2085, arXiv:1404.5609, Theorem 2, through Lemma 1 (i.i.d. signs for
the nulls), which is the only property of `W` its proof uses; E. Candès, Y. Fan, L. Janson and
J. Lv, *Panning for gold: model-X knockoffs for high dimensional controlled variable selection*,
J. R. Statist. Soc. B 80 (2018), arXiv:1610.02351, Theorem 3.4 (knockoff+ part) with Lemma 3.3. -/
theorem integral_falseDiscoveryProportion_knockoffSelection_one_le {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ} {W : Ω → Fin p → ℝ}
    (hW : Measurable W) (H0 : Finset (Fin p))
    (hflip : ∀ S ⊆ H0, μ.map (fun ω => flipSigns S (W ω)) = μ.map W) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion H0 (knockoffSelection 1 q (W ω)) ∂μ ≤ q :=
  integral_le_of_le_mul_sum_nullWeight μ hW H0 hflip 1 hq0
    (fun _ => falseDiscoveryProportion_nonneg _ _) (fun ω => fdp_le_sum_nullWeight H0 q (W ω))

set_option linter.unusedVariables false in
/-- **Modified FDR control by knockoff.** Under the hypotheses of
`integral_falseDiscoveryProportion_knockoffSelection_one_le`, for `0 < q ≤ 1` the knockoff
selection `Ŝ = {j : W_j ≥ T}` (offset `0`) satisfies `E[|Ŝ ∩ H0| / (|Ŝ| + q⁻¹)] ≤ q`.

Source: R. F. Barber and E. J. Candès, *Controlling the false discovery rate via knockoffs*,
Ann. Statist. 43 (2015), arXiv:1404.5609, Theorem 1 (stated for `q ∈ [0, 1]`; at `q = 0` the
source's bound is trivial if `q⁻¹` is read as `+∞`, but Lean's convention `0⁻¹ = 0` can make it
fail, so only `0 < q` is kept here), through Lemma 1;
E. Candès, Y. Fan, L. Janson and J. Lv, J. R. Statist. Soc. B 80 (2018), arXiv:1610.02351,
Theorem 3.4 (knockoff part) with Lemma 3.3. -/
theorem integral_card_inter_div_knockoffSelection_zero_le {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ} {W : Ω → Fin p → ℝ}
    (hW : Measurable W) (H0 : Finset (Fin p))
    (hflip : ∀ S ⊆ H0, μ.map (fun ω => flipSigns S (W ω)) = μ.map W) {q : ℝ} (hq0 : 0 < q)
    (hq1 : q ≤ 1) :
    ∫ ω, ((knockoffSelection 0 q (W ω) ∩ H0).card : ℝ) /
        ((knockoffSelection 0 q (W ω)).card + q⁻¹) ∂μ ≤ q :=
  integral_le_of_le_mul_sum_nullWeight μ hW H0 hflip 0 hq0.le (fun _ => by positivity)
    (fun ω => card_inter_div_le_sum_nullWeight H0 hq0 (W ω))

end MathlibExt.Probability.KnockoffFDRWanted
