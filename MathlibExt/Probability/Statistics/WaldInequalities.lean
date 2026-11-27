/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SequentialAnalysis
public import MathlibExt.MeasureTheory.Measure.PiWithDensity
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
* `MeasureTheory.infinitePi_apply_eq_setLIntegral_prod`,
  `MeasureTheory.infinitePi_apply_eq_setLIntegral_prod_rnDeriv`: the change of measure on the first
  `n` observations, for laws with densities and for the likelihood ratio.
* `MeasureTheory.setLIntegral_infinitePi_coord`: the Markov property of i.i.d. coordinates.
* `MeasureTheory.lintegral_enat_eq_tsum`: the tail-sum formula for a random time.
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



/-- The product of laws `Q i = P₀.withDensity (f i)` has density `x ↦ ∏ i, f i (x i)`. -/
private theorem pi_eq_withDensity_prod {ι : Type*} [Fintype ι] (P₀ : Measure X)
    [IsProbabilityMeasure P₀] (Q : ι → Measure X) [∀ i, IsProbabilityMeasure (Q i)]
    (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (hQ : ∀ i, Q i = P₀.withDensity (f i)) :
    Measure.pi Q = (Measure.pi fun _ : ι => P₀).withDensity (fun x => ∏ i, f i (x i)) := by
  have : ∀ i, SigmaFinite (P₀.withDensity (f i)) := fun i => by rw [← hQ i]; infer_instance
  refine Measure.pi_eq fun s hs => ?_
  rw [← Measure.pi_withDensity (μ := fun _ : ι => P₀) hf, Measure.pi_pi]
  exact prod_congr rfl fun i _ => by rw [hQ i]

/-- **Density of a finite product of absolutely continuous laws.** If `P₁ ≪ P₀` are probability
measures on `X` and `ι` is finite, the product law `P₁^ι` has density
`x ↦ ∏ i, (dP₁/dP₀)(x i)` with respect to `P₀^ι`: the likelihood ratio of `|ι|` independent
observations, as in the integrals of Wald's inequalities (Encyclopedia of Mathematics,
*Sequential probability ratio test*, equations (a1)–(a2)). -/
theorem Measure.pi_eq_withDensity_rnDeriv {ι : Type*} [Fintype ι] (P₀ P₁ : Measure X)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) :
    Measure.pi (fun _ : ι => P₁) =
      (Measure.pi fun _ : ι => P₀).withDensity (fun x => ∏ i, P₁.rnDeriv P₀ (x i)) :=
  pi_eq_withDensity_prod P₀ (fun _ => P₁) (fun _ => P₁.rnDeriv P₀)
    (fun _ => Measure.measurable_rnDeriv _ _)
    (fun _ => (Measure.withDensity_rnDeriv_eq P₁ P₀ h₁₀).symm)

/-- **Change of measure on the first `n` observations, for laws with densities.** Let `P₀` be a
probability measure on `X` and let each `Q i`, `i : ℕ`, be a probability measure on `X` with
`Q i = P₀.withDensity (f i)` for a measurable density `f i : X → ℝ≥0∞`. If the event `A` depends
only on the first `n` coordinates (it is measurable for `observationFiltration X n`), then
`(Measure.infinitePi Q)(A) = ∫_A ∏_{i<n} f i (ω i) dP₀^ℕ`. For instance, the law of the
observations with a change point, for `P₁ ≪ P₀`, has density `1` before the change and
`dP₁/dP₀` after it. -/
theorem infinitePi_apply_eq_setLIntegral_prod (P₀ : Measure X) [IsProbabilityMeasure P₀]
    (Q : ℕ → Measure X) [∀ i, IsProbabilityMeasure (Q i)] (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hQ : ∀ i, Q i = P₀.withDensity (f i)) (n : ℕ)
    {A : Set (ℕ → X)} (hA : MeasurableSet[observationFiltration X n] A) :
    Measure.infinitePi Q A =
      ∫⁻ ω in A, ∏ i ∈ range n, f i (ω i) ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  change MeasurableSet[MeasurableSpace.pi.comap (range n).restrict] A at hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
  have hr : Measurable ((range n).restrict : (ℕ → X) → ((range n) → X)) :=
    Finset.measurable_restrict _
  rw [← Measure.map_apply hr hB, Measure.infinitePi_map_restrict,
    pi_eq_withDensity_prod P₀ (fun i : range n => Q i) (fun i => f i) (fun i => hf i)
      (fun i => hQ i), withDensity_apply _ hB,
    ← Measure.infinitePi_map_restrict (μ := fun _ : ℕ => P₀),
    setLIntegral_map hB _ hr]
  · refine setLIntegral_congr_fun (hr hB) fun ω _ => ?_
    simp only [Finset.restrict]
    exact Finset.prod_coe_sort (range n) (fun i => f i (ω i))
  · exact Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i)

/-- **Likelihood-ratio change of measure on the first `n` observations.** If `P₁ ≪ P₀` and the
event `A` depends only on the observations `X₁, …, Xₙ`, then
`P₁^ℕ(A) = ∫_A ∏_{i<n} (dP₁/dP₀)(Xᵢ) dP₀^ℕ`: the likelihood ratio `Rₙ` is the density of `P₁^ℕ`
with respect to `P₀^ℕ` on `σ(X₁, …, Xₙ)`. This is the change of measure behind Wald's inequalities
(Encyclopedia of Mathematics, *Sequential probability ratio test*, equation (a2)). -/
theorem infinitePi_apply_eq_setLIntegral_prod_rnDeriv (P₀ P₁ : Measure X) [IsProbabilityMeasure P₀]
    [IsProbabilityMeasure P₁] (h₁₀ : P₁ ≪ P₀) (n : ℕ) {A : Set (ℕ → X)}
    (hA : MeasurableSet[observationFiltration X n] A) :
    Measure.infinitePi (fun _ : ℕ => P₁) A =
      ∫⁻ ω in A, ∏ i ∈ range n, P₁.rnDeriv P₀ (ω i) ∂Measure.infinitePi (fun _ : ℕ => P₀) :=
  infinitePi_apply_eq_setLIntegral_prod P₀ (fun _ => P₁) (fun _ => P₁.rnDeriv P₀)
    (fun _ => Measure.measurable_rnDeriv _ _)
    (fun _ => (Measure.withDensity_rnDeriv_eq P₁ P₀ h₁₀).symm) n hA

/-! ### Coordinates, stopping times and the Markov property -/

theorem measurable_coord_observationFiltration {n i : ℕ} (hi : i < n) :
    Measurable[observationFiltration X n] fun ω : ℕ → X => ω i := by
  change Measurable[MeasurableSpace.pi.comap (range n).restrict] fun ω : ℕ → X => ω i
  exact (@measurable_pi_apply (range n) (fun _ => X) (fun _ => inferInstance)
    ⟨i, mem_range.2 hi⟩).comp (comap_measurable _)

theorem setOfPred_natCast_add_one_le_eq {Ω : Type*} (T : Ω → WithTop ℕ) (n : ℕ) :
    {ω | ((n + 1 : ℕ) : WithTop ℕ) ≤ T ω} = {ω | (n : WithTop ℕ) < T ω} := by
  ext ω
  change ((n + 1 : ℕ) : ℕ∞) ≤ (T ω : ℕ∞) ↔ (n : ℕ∞) < (T ω : ℕ∞)
  rw [Nat.cast_add, Nat.cast_one]
  exact ENat.add_one_le_iff (ENat.natCast_ne_top n)

/-- **Markov property of i.i.d. coordinates.** Let `P₀` be a probability measure on `X`, let the
event `F` and the function `u : (ℕ → X) → ℝ≥0∞` be measurable for `observationFiltration X n`
(they depend only on the first `n` coordinates), and let `h : ℝ≥0∞ → X → ℝ≥0∞` be jointly
measurable. Then `∫_F h (u ω) (ω n) dP₀^ℕ = ∫_F ∫ h (u ω) x dP₀(x) dP₀^ℕ`: the next coordinate
`ω n` can be integrated out first. -/
theorem setLIntegral_infinitePi_coord (P₀ : Measure X) [IsProbabilityMeasure P₀] (n : ℕ)
    {F : Set (ℕ → X)} (hF : MeasurableSet[observationFiltration X n] F) {u : (ℕ → X) → ℝ≥0∞}
    (hu : Measurable[observationFiltration X n] u) {h : ℝ≥0∞ → X → ℝ≥0∞}
    (hh : Measurable (Function.uncurry h)) :
    ∫⁻ ω in F, h (u ω) (ω n) ∂Measure.infinitePi (fun _ : ℕ => P₀) =
      ∫⁻ ω in F, ∫⁻ x, h (u ω) x ∂P₀ ∂Measure.infinitePi (fun _ : ℕ => P₀) := by
  classical
  have hle : observationFiltration X n ≤ observationFiltration X (n + 1) :=
    (observationFiltration X).mono (Nat.le_succ n)
  have hFm : MeasurableSet F := (observationFiltration X).le n F hF
  have hun : Measurable[observationFiltration X (n + 1)] u := hu.mono hle le_rfl
  have hcoord : Measurable[observationFiltration X (n + 1)] fun ω : ℕ → X => ω n :=
    measurable_coord_observationFiltration (Nat.lt_succ_self n)
  set f : (ℕ → X) → ℝ≥0∞ := F.indicator fun ω => h (u ω) (ω n) with hf
  set g : (ℕ → X) → ℝ≥0∞ := F.indicator fun ω => ∫⁻ x, h (u ω) x ∂P₀ with hg
  have hfm : Measurable[observationFiltration X (n + 1)] f :=
    (hh.comp (hun.prodMk hcoord)).indicator (hle F hF)
  have hgm : Measurable[observationFiltration X n] g :=
    (hh.lintegral_prod_right'.comp hu).indicator hF
  have hFdep : ∀ x t, Function.update x n t ∈ F ↔ x ∈ F := by
    intro x t
    have hind : Measurable[observationFiltration X n] (F.indicator fun _ => (1 : ℝ≥0∞)) :=
      Measurable.indicator measurable_const hF
    have hdep := hind.dependsOn_of_piFinset
    have := hdep (x := Function.update x n t) (y := x) fun i hi =>
      Function.update_of_ne (mem_range.1 hi).ne _ _
    by_cases hx : x ∈ F <;> by_cases hx' : Function.update x n t ∈ F <;> simp_all
  have hudep : ∀ x t, u (Function.update x n t) = u x := fun x t =>
    hu.dependsOn_of_piFinset fun i hi => Function.update_of_ne (mem_range.1 hi).ne _ _
  obtain ⟨x₀⟩ : Nonempty (ℕ → X) := Measure.nonempty_of_neZero (Measure.infinitePi fun _ : ℕ => P₀)
  rw [← lintegral_indicator hFm, ← lintegral_indicator hFm]
  change ∫⁻ ω, f ω ∂_ = ∫⁻ ω, g ω ∂_
  rw [lintegral_infinitePi_of_piFinset (fun _ : ℕ => P₀) (s := range (n + 1)) hfm x₀,
    lintegral_infinitePi_of_piFinset (fun _ : ℕ => P₀) (s := range n) hgm x₀, range_add_one,
    lmarginal_insert' _ (hfm.mono ((observationFiltration X).le _) le_rfl) notMem_range_self]
  congr 1
  funext x
  simp only [hf, hg, Set.indicator, hFdep, hudep, Function.update_self]
  split_ifs <;> simp

private theorem enat_toENNReal_eq_tsum (k : ℕ∞) :
    (k : ℝ≥0∞) = ∑' n : ℕ, if (n : ℕ∞) < k then 1 else 0 := by
  induction k using ENat.recTopCoe with
  | top =>
    simp only [ENat.natCast_lt_top, ite_true, ENat.toENNReal_top]
    exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
  | coe m =>
    rw [tsum_eq_sum (s := range m)]
    · rw [sum_congr rfl (g := fun _ => (1 : ℝ≥0∞)) fun n hn => by simp [mem_range.1 hn]]
      simp
    · intro n hn
      simpa using hn

/-- **Tail-sum formula for a random time.** For a measure `μ` on `Ω` and a random time
`T : Ω → WithTop ℕ` such that every event `{n < T}` is measurable, the lower integral of `T`, read
in `ℝ≥0∞` with `⊤ ↦ ∞`, is `∑_{n ≥ 0} μ {n < T}`. -/
theorem lintegral_enat_eq_tsum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {T : Ω → WithTop ℕ} (hT : ∀ n : ℕ, MeasurableSet {ω | (n : WithTop ℕ) < T ω}) :
    ∫⁻ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) ∂μ = ∑' n : ℕ, μ {ω | (n : WithTop ℕ) < T ω} := by
  have hpt : ∀ ω, ((show ℕ∞ from T ω) : ℝ≥0∞) =
      ∑' n : ℕ, {ω | (n : WithTop ℕ) < T ω}.indicator 1 ω := by
    intro ω
    refine (enat_toENNReal_eq_tsum (T ω)).trans ?_
    congr 1
    funext n
    simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply]
    have hiff : ((n : ℕ∞) < (show ℕ∞ from T ω)) ↔ ((n : WithTop ℕ) < T ω) := Iff.rfl
    by_cases hn : (n : WithTop ℕ) < T ω
    · rw [ite_eq_left (hiff.2 hn), ite_eq_left hn]
    · rw [ite_eq_right (mt hiff.1 hn), ite_eq_right hn]
  simp_rw [hpt]
  rw [lintegral_tsum fun n => (measurable_one.indicator (hT n)).aemeasurable]
  congr 1
  funext n
  rw [lintegral_indicator_one (hT n)]

/-! ### Wald's inequalities -/

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
