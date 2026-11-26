/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.ItemScore
public import Mathlib.Analysis.Convex.Deriv

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Order.Filter.AtTopBot.Field

/-! # Maximum-likelihood ability in the two-parameter logistic model -/

@[expose] public section

open Filter Set
open scoped Topology

namespace MathlibExt.Probability.Statistics.Measurement

open MathlibExt.Probability.Statistics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Log-likelihood of ability `t` for the binary pattern `Y` in the finite 2PL model,
with item discriminations `a` and difficulties `b`. -/
noncomputable def twoPLAbilityLogLikelihood (a b : ι → ℝ) (Y : ι → Bool) (t : ℝ) : ℝ :=
  Real.log ((twoPLPMF a b t Y).toReal)

/-- The canonical 2PL score, viewed as a function of ability for a fixed response pattern. -/
noncomputable abbrev twoPLAbilityScore (a b : ι → ℝ) (Y : ι → Bool) (t : ℝ) : ℝ :=
  VectorInference.score (fun s x => (twoPLPMF a b s x).toReal) t Y

/-- The derivative of the log-likelihood is the ability score. -/
theorem twoPLAbilityLogLikelihood_hasDerivAt (a b : ι → ℝ) (Y : ι → Bool) (t : ℝ) :
    HasDerivAt (twoPLAbilityLogLikelihood a b Y) (twoPLAbilityScore a b Y t) t := by
  rw [twoPLAbilityScore, twoPL_score_eq_sum]
  exact twoPL_logPMF_hasDerivAt a b t Y

/-- The score derivative is minus the sum of the discrimination-squared Bernoulli variances. -/
theorem twoPLAbilityScore_hasDerivAt (a b : ι → ℝ) (Y : ι → Bool) (t : ℝ) :
    HasDerivAt (twoPLAbilityScore a b Y)
      (∑ i, -(a i ^ 2 * Real.sigmoid (a i * (t - b i)) *
        (1 - Real.sigmoid (a i * (t - b i))))) t := by
  have hscore : twoPLAbilityScore a b Y = fun s =>
      ∑ i, a i * ((if Y i then (1 : ℝ) else 0) - Real.sigmoid (a i * (s - b i))) :=
    funext fun s => twoPL_score_eq_sum a b s Y
  rw [hscore]
  refine HasDerivAt.fun_sum (fun i _ => ?_)
  have haff : HasDerivAt (fun s : ℝ => a i * (s - b i)) (a i) t := by
    simpa using ((hasDerivAt_id t).sub_const (b i)).const_mul (a i)
  let p := Real.sigmoid (a i * (t - b i))
  have hp : HasDerivAt (fun s : ℝ => Real.sigmoid (a i * (s - b i)))
      (p * (1 - p) * a i) t :=
    HasDerivAt.comp t (h := fun s : ℝ => a i * (s - b i)) (h₂ := Real.sigmoid)
      (Real.hasDerivAt_sigmoid _) haff
  change HasDerivAt _ (-(a i ^ 2 * p * (1 - p))) t
  rw [show -(a i ^ 2 * p * (1 - p)) = a i * -(p * (1 - p) * a i) by ring]
  exact (hp.const_sub (if Y i then (1 : ℝ) else 0)).const_mul (a i)

private theorem abilityScore_deriv_neg [Nonempty ι] (a b : ι → ℝ) (Y : ι → Bool)
    (ha : ∀ i, 0 < a i) (t : ℝ) : deriv (twoPLAbilityScore a b Y) t < 0 := by
  rw [(twoPLAbilityScore_hasDerivAt a b Y t).deriv]
  apply Finset.sum_neg _ Finset.univ_nonempty
  intro i _
  exact neg_lt_zero.mpr (mul_pos (mul_pos (sq_pos_of_pos (ha i)) (Real.sigmoid_pos _))
    (sub_pos.mpr (Real.sigmoid_lt_one _)))

private theorem abilityLogLikelihood_max_iff_score_zero [Nonempty ι]
    (a b : ι → ℝ) (Y : ι → Bool) (ha : ∀ i, 0 < a i) (t : ℝ) :
    IsMaxOn (twoPLAbilityLogLikelihood a b Y) univ t ↔ twoPLAbilityScore a b Y t = 0 := by
  let l := twoPLAbilityLogLikelihood a b Y
  have hl : Differentiable ℝ l := fun x =>
    (twoPLAbilityLogLikelihood_hasDerivAt a b Y x).differentiableAt
  have hs : StrictAnti (twoPLAbilityScore a b Y) :=
    strictAnti_of_deriv_neg (abilityScore_deriv_neg a b Y ha)
  constructor
  · intro hm
    exact (hm.isLocalMax (by simp)).hasDerivAt_eq_zero
      (twoPLAbilityLogLikelihood_hasDerivAt a b Y t)
  · intro ht
    apply isMaxOn_univ_iff.mpr
    intro x
    rcases lt_trichotomy x t with h | rfl | h
    · obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope l h hl.continuous.continuousOn hl.differentiableOn
      rw [(twoPLAbilityLogLikelihood_hasDerivAt a b Y c).deriv] at he
      have hpos : 0 < (l t - l x) / (t - x) := by
        rw [← he, ← ht]
        exact hs hc.2
      exact (sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr h)).mp hpos)).le
    · exact le_rfl
    · obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope l h hl.continuous.continuousOn hl.differentiableOn
      rw [(twoPLAbilityLogLikelihood_hasDerivAt a b Y c).deriv] at he
      have hneg : (l x - l t) / (x - t) < 0 := by
        rw [← he, ← ht]
        exact hs hc.1
      exact (sub_neg.mp (by simpa only [zero_mul] using (div_lt_iff₀ (sub_pos.mpr h)).mp hneg)).le

private theorem abilitySigmoid_limits (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun t : ℝ => Real.sigmoid (a * (t - b))) atBot (𝓝 0) ∧
    Tendsto (fun t : ℝ => Real.sigmoid (a * (t - b))) atTop (𝓝 1) := by
  have hbot : Tendsto (fun t : ℝ => a * (t - b)) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos ha).mpr (by
      simpa only [sub_eq_add_neg, id_eq] using tendsto_atBot_add_const_right atBot (-b) tendsto_id)
  have htop : Tendsto (fun t : ℝ => a * (t - b)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ha).mpr (by
      simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-b) tendsto_id)
  exact ⟨Real.tendsto_sigmoid_atBot.comp hbot, Real.tendsto_sigmoid_atTop.comp htop⟩

/-- **Existence of the 2PL ability MLE.** For a finite nonempty set of binary items with
positive discriminations, the log-likelihood is strictly concave and has a maximizer
exactly when the response pattern contains both a correct and an incorrect answer.
A maximizer is exactly a zero of the score, and that zero is unique. For the all-correct
pattern the log-likelihood is strictly increasing to zero at positive infinity; for the
all-incorrect pattern it is strictly decreasing and tends to zero at negative infinity.
The Rasch case is obtained by taking all discriminations equal to one. The result does
not address confidence intervals, asymptotic inference or finite-test bias. See F. M. Lord,
*Applications of Item Response Theory to Practical Testing Problems* (1980). -/
theorem twoPLAbility_mle [Nonempty ι] (a b : ι → ℝ) (Y : ι → Bool) (ha : ∀ i, 0 < a i) :
    let l := twoPLAbilityLogLikelihood a b Y
    let score := twoPLAbilityScore a b Y
    StrictConcaveOn ℝ univ l ∧
      (∀ t, HasDerivAt l (score t) t ∧
        HasDerivAt score (∑ i, -(a i ^ 2 * Real.sigmoid (a i * (t - b i)) *
          (1 - Real.sigmoid (a i * (t - b i))))) t ∧ deriv score t < 0) ∧
      (∀ t, IsMaxOn l univ t ↔ score t = 0) ∧
      ((∃! t, score t = 0) ↔ (∃ i, Y i = true) ∧ (∃ i, Y i = false)) ∧
      ((∃ t, IsMaxOn l univ t) ↔ (∃ i, Y i = true) ∧ (∃ i, Y i = false)) ∧
      ((∀ i, Y i = true) → StrictMono l ∧ Tendsto l atTop (𝓝 0)) ∧
      ((∀ i, Y i = false) → StrictAnti l ∧ Tendsto l atBot (𝓝 0)) := by
  intro l score
  have hdiff (t : ℝ) : HasDerivAt l (score t) t := twoPLAbilityLogLikelihood_hasDerivAt a b Y t
  have hdscore (t : ℝ) := twoPLAbilityScore_hasDerivAt a b Y t
  have hneg (t : ℝ) : deriv score t < 0 := abilityScore_deriv_neg a b Y ha t
  have hanti : StrictAnti score := strictAnti_of_deriv_neg hneg
  have hstrict : StrictConcaveOn ℝ univ l := by
    apply StrictAnti.strictConcaveOn_univ_of_deriv (continuous_iff_continuousAt.mpr
      fun t => (hdiff t).continuousAt)
    rw [funext fun t => (hdiff t).deriv]
    exact hanti
  have hmax (t : ℝ) : IsMaxOn l univ t ↔ score t = 0 :=
    abilityLogLikelihood_max_iff_score_zero a b Y ha t
  have hsum : score = fun s =>
      ∑ i, a i * ((if Y i then (1 : ℝ) else 0) - Real.sigmoid (a i * (s - b i))) :=
    funext fun s => twoPL_score_eq_sum a b s Y
  have hpos (hY : ∀ i, Y i = true) (t : ℝ) : 0 < score t := by
    rw [hsum]
    simp only [hY, ite_true]
    exact Finset.sum_pos (fun i _ => mul_pos (ha i) (sub_pos.mpr (Real.sigmoid_lt_one _)))
      Finset.univ_nonempty
  have hneg' (hY : ∀ i, Y i = false) (t : ℝ) : score t < 0 := by
    rw [hsum]
    simp only [hY, Bool.false_eq_true, ite_false, zero_sub]
    exact Finset.sum_neg (fun i _ => mul_neg_of_pos_of_neg (ha i) (neg_lt_zero.mpr
      (Real.sigmoid_pos _))) Finset.univ_nonempty
  have hmixed : (∃! t, score t = 0) ↔ (∃ i, Y i = true) ∧ (∃ i, Y i = false) := by
    constructor
    · rintro ⟨t, ht, _⟩
      constructor
      · by_contra h
        have hY (i : ι) : Y i = false := by
          cases hi : Y i
          · rfl
          · exact (h ⟨i, hi⟩).elim
        exact (hneg' hY t).ne ht
      · by_contra h
        have hY (i : ι) : Y i = true := by
          cases hi : Y i
          · exact (h ⟨i, hi⟩).elim
          · rfl
        exact (hpos hY t).ne' ht
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      let r : ι → ℝ := fun k => if Y k then 1 else 0
      have hlo : Tendsto score atBot (𝓝 (∑ k, a k * r k)) := by
        rw [hsum]
        apply tendsto_finsetSum
        intro k _
        simpa only [r, sub_zero] using
          ((abilitySigmoid_limits (a k) (b k) (ha k)).1.const_sub (r k)).const_mul (a k)
      have hhi : Tendsto score atTop (𝓝 (∑ k, a k * (r k - 1))) := by
        rw [hsum]
        exact tendsto_finsetSum _ fun k _ =>
          ((abilitySigmoid_limits (a k) (b k) (ha k)).2.const_sub (r k)).const_mul (a k)
      have hlow : 0 < ∑ k, a k * r k := by
        refine Finset.sum_pos' (fun k _ => mul_nonneg (ha k).le ?_) ?_
        · unfold r
          split_ifs <;> norm_num
        · exact ⟨i, Finset.mem_univ _, by simpa [r, hi] using ha i⟩
      have hhigh : (∑ k, a k * (r k - 1)) < 0 := by
        apply Finset.sum_neg' (fun k _ => mul_nonpos_of_nonneg_of_nonpos (ha k).le
          (by unfold r; split_ifs <;> norm_num))
        exact ⟨j, Finset.mem_univ _, by simpa [r, hj] using ha j⟩
      have hcont : Continuous score :=
        continuous_iff_continuousAt.mpr fun t => (hdscore t).continuousAt
      obtain ⟨t, ht⟩ := intermediate_value_univ₂_eventually₂ (g := fun _ => (0 : ℝ))
        hcont continuous_const ((hhi.eventually_lt_const hhigh).mono fun _ h => h.le)
        ((hlo.eventually_const_lt hlow).mono fun _ h => h.le)
      exact ⟨t, ht, fun s hs => hanti.injective (hs.trans ht.symm)⟩
  refine ⟨hstrict, fun t => ⟨hdiff t, hdscore t, hneg t⟩, hmax, hmixed, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨t, ht⟩
      have hz := (hmax t).mp ht
      exact hmixed.mp ⟨t, hz, fun s hs => hanti.injective (hs.trans hz.symm)⟩
    · intro h
      obtain ⟨t, ht, _⟩ := hmixed.mpr h
      exact ⟨t, (hmax t).mpr ht⟩
  · intro hY
    refine ⟨strictMono_of_deriv_pos (fun t => by rw [(hdiff t).deriv]; exact hpos hY t), ?_⟩
    have he (t : ℝ) : l t = ∑ i, Real.log (Real.sigmoid (a i * (t - b i))) := by
      simp only [l, twoPLAbilityLogLikelihood, twoPL_logPMF_toReal_eq_sum, hY, ite_true]
    rw [funext he]
    have hlim (i : ι) : Tendsto (fun t => Real.log (Real.sigmoid (a i * (t - b i))))
        atTop (𝓝 0) := by
      simpa only [Real.log_one] using ((abilitySigmoid_limits (a i) (b i) (ha i)).2.log one_ne_zero)
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  · intro hY
    refine ⟨strictAnti_of_deriv_neg (fun t => by rw [(hdiff t).deriv]; exact hneg' hY t), ?_⟩
    have he (t : ℝ) : l t = ∑ i, Real.log (1 - Real.sigmoid (a i * (t - b i))) := by
      simp only [l, twoPLAbilityLogLikelihood, twoPL_logPMF_toReal_eq_sum,
        hY, Bool.false_eq_true, ite_false]
    rw [funext he]
    have hlim (i : ι) : Tendsto (fun t => Real.log (1 - Real.sigmoid (a i * (t - b i))))
        atBot (𝓝 0) := by
      have hp : Tendsto (fun t : ℝ => 1 - Real.sigmoid (a i * (t - b i))) atBot (𝓝 1) := by
        simpa only [sub_zero] using (abilitySigmoid_limits (a i) (b i) (ha i)).1.const_sub 1
      simpa only [Real.log_one] using hp.log one_ne_zero
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hlim i)

end MathlibExt.Probability.Statistics.Measurement
