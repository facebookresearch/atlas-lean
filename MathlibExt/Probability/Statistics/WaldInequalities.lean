/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SequentialAnalysis
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Wald's inequalities for the sequential probability ratio test

For mutually absolutely continuous probability measures `P₀` and `P₁` and i.i.d. observations, the
likelihood ratio `Rₙ = ∏_{i ≤ n} (dP₁/dP₀)(Xᵢ)` is the density of `P₁^ℕ` with respect to `P₀^ℕ` on
the `σ`-algebra of the first `n` observations. Summing over the value of the stopping time gives
Wald's inequalities for the SPRT (Encyclopedia of Mathematics, *Sequential probability ratio
test*, equation (a2)):
`P₁(accept P₀) ≤ e^a P₀(accept P₀)` and `e^b P₀(accept P₁) ≤ P₁(accept P₁)`.

## Main statements

* `MeasureTheory.Measure.pi_eq_withDensity_rnDeriv`: the density of a finite product law.
* `MeasureTheory.infinitePi_apply_eq_setLIntegral_prod_rnDeriv`: the likelihood-ratio change of
  measure on the first `n` observations.
* `MeasureTheory.sprt_acceptZero_le`, `MeasureTheory.sprt_acceptOne_ge`: Wald's inequalities.

## References

* B. Eisenberg, *Sequential probability ratio test*, Encyclopedia of Mathematics, equations
  (a1)–(a2).
* T. L. Lai, *Sequential analysis: some classical problems and new challenges*, Statistica Sinica
  11 (2001) 303–408, §2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X]



/-- **Density of a finite product of absolutely continuous laws.** If `P₁ ≪ P₀` are probability
measures on `X` and `ι` is finite, the product law `P₁^ι` has density
`x ↦ ∏ i, (dP₁/dP₀)(x i)` with respect to `P₀^ι`: the likelihood ratio of `|ι|` independent
observations, as in the integrals of Wald's inequalities (Encyclopedia of Mathematics,
*Sequential probability ratio test*, equations (a1)–(a2)). -/
theorem Measure.pi_eq_withDensity_rnDeriv {ι : Type*} [Fintype ι] (P₀ P₁ : Measure X)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) :
    Measure.pi (fun _ : ι => P₁) =
      (Measure.pi fun _ : ι => P₀).withDensity (fun x => ∏ i, P₁.rnDeriv P₀ (x i)) := by
  classical
  refine Measure.pi_eq fun s hs => ?_
  have hsm : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hsm, ← lintegral_indicator hsm]
  have hind : (Set.univ.pi s).indicator (fun x : ι → X => ∏ i, P₁.rnDeriv P₀ (x i)) =
      fun x => ∏ i, (s i).indicator (P₁.rnDeriv P₀) (x i) := by
    funext x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      refine prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (prod_eq_zero (mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [hind]
  have hmeas : ∀ i, Measurable ((s i).indicator (P₁.rnDeriv P₀)) := fun i =>
    (Measure.measurable_rnDeriv _ _).indicator (hs i)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun univ
    (fun i (x : ι → X) => (s i).indicator (P₁.rnDeriv P₀) (x i))
    (iIndepFun_pi (μ := fun _ : ι => P₀) (X := fun i => (s i).indicator (P₁.rnDeriv P₀))
      fun i => (hmeas i).aemeasurable)
    (fun i => (hmeas i).comp (measurable_pi_apply i))]
  refine prod_congr rfl fun i _ => ?_
  rw [(measurePreserving_eval (fun _ : ι => P₀) i).lintegral_comp (hmeas i),
    lintegral_indicator (hs i), Measure.setLIntegral_rnDeriv h₁₀]


/-- **Likelihood-ratio change of measure on the first `n` observations.** If `P₁ ≪ P₀` and the
event `A` depends only on the observations `X₁, …, Xₙ`, then
`P₁^ℕ(A) = ∫_A ∏_{i<n} (dP₁/dP₀)(Xᵢ) dP₀^ℕ`: the likelihood ratio `Rₙ` is the density of `P₁^ℕ`
with respect to `P₀^ℕ` on `σ(X₁, …, Xₙ)`. This is the change of measure behind Wald's inequalities
(Encyclopedia of Mathematics, *Sequential probability ratio test*, equation (a2)). -/
theorem infinitePi_apply_eq_setLIntegral_prod_rnDeriv (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (n : ℕ) {A : Set (ℕ → X)}
    (hA : MeasurableSet[observationFiltration X n] A) :
    Measure.infinitePi (fun _ : ℕ => P₁) A =
      ∫⁻ ω in A, ∏ i ∈ range n, P₁.rnDeriv P₀ (ω i) ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  change MeasurableSet[MeasurableSpace.pi.comap (range n).restrict] A at hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
  have hr : Measurable ((range n).restrict : (ℕ → X) → ((range n) → X)) :=
    Finset.measurable_restrict _
  rw [← Measure.map_apply hr hB, Measure.infinitePi_map_restrict,
    Measure.pi_eq_withDensity_rnDeriv P₀ P₁ h₁₀, withDensity_apply _ hB,
    ← Measure.infinitePi_map_restrict (μ := fun _ : ℕ => P₀),
    setLIntegral_map hB _ hr]
  · refine setLIntegral_congr_fun (hr hB) fun ω _ => ?_
    simp only [Finset.restrict]
    exact Finset.prod_coe_sort (range n) (fun i => P₁.rnDeriv P₀ (ω i))
  · exact Finset.measurable_prod _ fun i _ =>
      (Measure.measurable_rnDeriv _ _).comp (measurable_pi_apply i)


/-- **The cumulative log-likelihood ratio is adapted.** For probability laws, mutually
absolutely continuous, `Λₙ` is measurable with respect to `σ(X₁, …, Xₙ)`, so the SPRT decides
after `n` observations from those observations only (Lai 2001, §2, equation (2.1)). -/
theorem adapted_llrSum (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) :
    Adapted (observationFiltration X) (llrSum P₀ P₁ h₁₀ h₀₁) := by
  intro n
  change Measurable[MeasurableSpace.pi.comap (range n).restrict] (llrSum P₀ P₁ h₁₀ h₀₁ n)
  have hg : Measurable fun x : (range n) → X => ∑ i : range n, llr P₁ P₀ (x i) :=
    Finset.measurable_sum _ fun i _ =>
      (measurable_llr P₁ P₀).comp (measurable_pi_apply i)
  have : llrSum P₀ P₁ h₁₀ h₀₁ n =
      (fun x : (range n) → X => ∑ i : range n, llr P₁ P₀ (x i)) ∘
        (range n).restrict := by
    funext ω
    simp only [llrSum, Function.comp_apply, Finset.restrict]
    exact (Finset.sum_coe_sort (range n) (fun i => llr P₁ P₀ (ω i))).symm
  rw [this]
  exact hg.comp (comap_measurable _)

/-- **The SPRT stopping time is a stopping time** of the observations, possibly infinite, for
probability laws, mutually absolutely continuous (Lai 2001, §2, equation (2.1)). -/
theorem isStoppingTime_sprtTime (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (a b : ℝ) :
    IsStoppingTime (observationFiltration X) (sprtTime P₀ P₁ h₁₀ h₀₁ a b) :=
  (adapted_llrSum P₀ P₁ h₁₀ h₀₁).isStoppingTime_hittingAfter
    (measurableSet_Iic.union measurableSet_Ici)

private theorem ae_rnDeriv_coord (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₀₁ : P₀ ≪ P₁) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => P₀),
      ∀ i, 0 < P₁.rnDeriv P₀ (ω i) ∧ P₁.rnDeriv P₀ (ω i) < ∞ := by
  have h1 : ∀ᵐ x ∂P₀, 0 < P₁.rnDeriv P₀ x ∧ P₁.rnDeriv P₀ x < ∞ :=
    (Measure.rnDeriv_pos' h₀₁).and (Measure.rnDeriv_lt_top P₁ P₀)
  refine ae_all_iff.mpr fun i => ?_
  exact ae_of_ae_map (μ := Measure.infinitePi fun _ : ℕ => P₀) (f := fun ω : ℕ → X => ω i)
    (p := fun x => 0 < P₁.rnDeriv P₀ x ∧ P₁.rnDeriv P₀ x < ∞)
    (measurable_pi_apply i).aemeasurable
    (by rw [Measure.infinitePi_map_eval (fun _ : ℕ => P₀) i]; exact h1)

private theorem prod_rnDeriv_eq_ofReal_exp (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (n : ℕ) {ω : ℕ → X}
    (hω : ∀ i, 0 < P₁.rnDeriv P₀ (ω i) ∧ P₁.rnDeriv P₀ (ω i) < ∞) :
    ∏ i ∈ range n, P₁.rnDeriv P₀ (ω i) =
      ENNReal.ofReal (Real.exp (llrSum P₀ P₁ h₁₀ h₀₁ n ω)) := by
  rw [llrSum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  refine prod_congr rfl fun i _ => ?_
  have hpos : 0 < (P₁.rnDeriv P₀ (ω i)).toReal :=
    ENNReal.toReal_pos (hω i).1.ne' (hω i).2.ne
  rw [llr, Real.exp_log hpos, ENNReal.ofReal_toReal (hω i).2.ne]


/-- **Wald's inequality on the acceptance of the null hypothesis.** For the SPRT with
log-boundaries `a` and `b`, `P₁(accept P₀) ≤ e^a P₀(accept P₀)`, where both events require the
test to stop. This is the first line of Wald's inequalities, `β = ∫_{λ_N ≤ A} λ_N dP₀ ≤ A (1 - α)`
(Encyclopedia of Mathematics, *Sequential probability ratio test*, equation (a2), whose lower
boundary `A` is `e^a` here); `1 - α` equals `P₀(accept P₀)` when the SPRT stops `P₀`-almost
surely. The source takes `a < 0 < b`; the inequality holds for all `a` and `b`. -/
theorem sprt_acceptZero_le {P₀ P₁ : Measure X} [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (a b : ℝ) :
    Measure.infinitePi (fun _ : ℕ => P₁) (sprtAcceptZero P₀ P₁ h₁₀ h₀₁ a b) ≤
      ENNReal.ofReal (Real.exp a) *
        Measure.infinitePi (fun _ : ℕ => P₀) (sprtAcceptZero P₀ P₁ h₁₀ h₀₁ a b) := by
  set E : ℕ → Set (ℕ → X) := fun n =>
    {ω | sprtTime P₀ P₁ h₁₀ h₀₁ a b ω = n} ∩ (llrSum P₀ P₁ h₁₀ h₀₁ n) ⁻¹' Set.Iic a with hEdef
  have hU : sprtAcceptZero P₀ P₁ h₁₀ h₀₁ a b = ⋃ n, E n := by
    ext ω; simp [sprtAcceptZero, hEdef]
  have hEn : ∀ n, MeasurableSet[observationFiltration X n] (E n) := fun n =>
    ((isStoppingTime_sprtTime P₀ P₁ h₁₀ h₀₁ a b).measurableSet_eq n).inter
      (adapted_llrSum P₀ P₁ h₁₀ h₀₁ n measurableSet_Iic)
  have hEm : ∀ n, MeasurableSet (E n) := fun n => (observationFiltration X).le n _ (hEn n)
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun ω h1 h2 => hnm ?_
    have := h1.1.symm.trans h2.1
    exact_mod_cast this
  have hcoord := ae_rnDeriv_coord P₀ P₁ h₀₁
  have hn : ∀ n, Measure.infinitePi (fun _ : ℕ => P₁) (E n) ≤
      ENNReal.ofReal (Real.exp a) * Measure.infinitePi (fun _ : ℕ => P₀) (E n) := by
    intro n
    rw [infinitePi_apply_eq_setLIntegral_prod_rnDeriv P₀ P₁ h₁₀ n (hEn n), ← setLIntegral_const]
    refine lintegral_mono_ae ((ae_restrict_iff' (hEm n)).mpr ?_)
    filter_upwards [hcoord] with ω hω hmem
    rw [prod_rnDeriv_eq_ofReal_exp P₀ P₁ h₁₀ h₀₁ n hω]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmem.2)
  rw [hU, measure_iUnion hdisj hEm, measure_iUnion hdisj hEm, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hn

/-- **Wald's inequality on the acceptance of the alternative.** For the SPRT with log-boundaries
`a` and `b`, `e^b P₀(accept P₁) ≤ P₁(accept P₁)`: the second line of Wald's inequalities,
`1 - β = ∫_{λ_N ≥ B} λ_N dP₀ ≥ B α` (Encyclopedia of Mathematics, *Sequential probability ratio
test*, equation (a2), whose upper boundary `B` is `e^b` here). With the first inequality it gives
Wald's approximations `e^b ≈ (1 - β)/α` and `e^a ≈ β/(1 - α)`, which are equalities when the
log-likelihood ratio has no overshoot. The source takes `a < 0 < b`; the inequality holds for all
`a` and `b`. -/
theorem sprt_acceptOne_ge {P₀ P₁ : Measure X} [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (h₀₁ : P₀ ≪ P₁) (a b : ℝ) :
    ENNReal.ofReal (Real.exp b) *
        Measure.infinitePi (fun _ : ℕ => P₀) (sprtAcceptOne P₀ P₁ h₁₀ h₀₁ a b) ≤
      Measure.infinitePi (fun _ : ℕ => P₁) (sprtAcceptOne P₀ P₁ h₁₀ h₀₁ a b) := by
  set E : ℕ → Set (ℕ → X) := fun n =>
    {ω | sprtTime P₀ P₁ h₁₀ h₀₁ a b ω = n} ∩ (llrSum P₀ P₁ h₁₀ h₀₁ n) ⁻¹' Set.Ici b with hEdef
  have hU : sprtAcceptOne P₀ P₁ h₁₀ h₀₁ a b = ⋃ n, E n := by
    ext ω; simp [sprtAcceptOne, hEdef]
  have hEn : ∀ n, MeasurableSet[observationFiltration X n] (E n) := fun n =>
    ((isStoppingTime_sprtTime P₀ P₁ h₁₀ h₀₁ a b).measurableSet_eq n).inter
      (adapted_llrSum P₀ P₁ h₁₀ h₀₁ n measurableSet_Ici)
  have hEm : ∀ n, MeasurableSet (E n) := fun n => (observationFiltration X).le n _ (hEn n)
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun ω h1 h2 => hnm ?_
    have := h1.1.symm.trans h2.1
    exact_mod_cast this
  have hcoord := ae_rnDeriv_coord P₀ P₁ h₀₁
  have hn : ∀ n, ENNReal.ofReal (Real.exp b) * Measure.infinitePi (fun _ : ℕ => P₀) (E n) ≤
      Measure.infinitePi (fun _ : ℕ => P₁) (E n) := by
    intro n
    rw [infinitePi_apply_eq_setLIntegral_prod_rnDeriv P₀ P₁ h₁₀ n (hEn n), ← setLIntegral_const]
    refine lintegral_mono_ae ((ae_restrict_iff' (hEm n)).mpr ?_)
    filter_upwards [hcoord] with ω hω hmem
    rw [prod_rnDeriv_eq_ofReal_exp P₀ P₁ h₁₀ h₀₁ n hω]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hmem.2)
  rw [hU, measure_iUnion hdisj hEm, measure_iUnion hdisj hEm, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum hn

end MeasureTheory
