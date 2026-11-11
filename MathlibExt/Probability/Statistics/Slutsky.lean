/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Slutsky's theorem: product, ratio and scalar-multiple forms

Mathlib proves the joint form of Slutsky's theorem,
`MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const`, its continuous-mapping
corollary `TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const`, and the sum
form `TendstoInDistribution.add_of_tendstoInMeasure_const`. This file adds the product, ratio and
scalar-multiple forms.

Throughout, `X n →ᵈ Z` where the `X n` live on one probability space `(Ω'', μ'')` and `Z` may
live on another space `(Ω', μ')`, and `Y n → c` in probability on the same space as the `X n`.
The second limit must be a **constant**: for a nonconstant limit of `Y n`, the marginal
convergences `X n →ᵈ Z`, `Y n →ᵈ W` do not determine the law of `(X n, Y n)`, and none of these
conclusions follow without joint convergence.

## Main statements

* `MeasureTheory.tendstoInMeasure_of_tendstoInDistribution_const`: convergence in distribution
  to a constant implies convergence in probability to it.
* `MeasureTheory.TendstoInMeasure.comp_const_of_continuousAt`: convergence in probability to a
  constant is preserved by a function continuous at that constant.
* `MeasureTheory.TendstoInMeasure.inv_const`: if `Y n → c ≠ 0` in probability then
  `(Y n)⁻¹ → c⁻¹` in probability.
* `MeasureTheory.TendstoInDistribution.mul_of_tendstoInMeasure_const`: `X n * Y n →ᵈ c * Z`.
* `MeasureTheory.TendstoInDistribution.div_of_tendstoInMeasure_const`: `X n / Y n →ᵈ Z / c`
  for `c ≠ 0`.
* `MeasureTheory.TendstoInDistribution.smul_of_tendstoInMeasure_const`: `Y n • X n →ᵈ c • Z`
  for vector-valued `X n` and real `Y n`.
* `MeasureTheory.TendstoInDistribution.congr_hasLaw`: the limit may be replaced by any random
  variable with the same law (a utility shared by the asymptotic-test files).

Since a sequence converging in distribution to a constant converges to it in probability, these
theorems also apply when `Y n →ᵈ c` is given.
`TendstoInDistribution.mul_tendstoInMeasure_zero` in
`MathlibExt.Probability.Statistics.MLEAsymptoticNormality` is the `c = 0` case of
`mul_of_tendstoInMeasure_const` composed with that fact.

## References

* A. W. van der Vaart, *Asymptotic Statistics* (1998), Lemma 2.8.
-/

@[expose] public section

open Filter Topology

namespace MeasureTheory

section ConstLimit

variable {ι Ω Ω' E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} {l : Filter ι}

/-- **Convergence in distribution to a constant implies convergence in probability.** If the
random variables `X i` on one probability space converge in distribution to the constant `c`,
then they converge to `c` in probability. -/
theorem tendstoInMeasure_of_tendstoInDistribution_const [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {X : ι → Ω → E} {c : E} (h : TendstoInDistribution X l (fun _ : Ω' => c) (fun _ => P) P') :
    TendstoInMeasure P X l (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  set F : Set E := {y | ε ≤ dist y c}
  have hF : IsClosed F := isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hF
  have hc : (P'.map fun _ : Ω' => c) F = 0 := by
    rw [Measure.map_const, measure_univ, one_smul, Measure.dirac_apply' _ hF.measurableSet]
    simp [F, hε.not_ge]
  simp only [ProbabilityMeasure.coe_mk, hc] at hlim
  have heq : ∀ i, P {ω | ε ≤ dist (X i ω) c} = (P.map (X i)) F := fun i => by
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable i) hF.measurableSet]
    rfl
  simp_rw [heq]
  refine tendsto_order.2 ⟨fun a ha => absurd ha ENNReal.not_lt_zero, fun a ha => ?_⟩
  exact eventually_lt_of_limsup_lt (hlim.trans_lt ha)

end ConstLimit

variable {ι Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'} {l : Filter ι}

/-- Convergence in probability to a constant is preserved by a function continuous at that
constant. -/
theorem TendstoInMeasure.comp_const_of_continuousAt {E F : Type*} [PseudoMetricSpace E]
    [PseudoMetricSpace F] {Y : ι → Ω → E} {c : E} {f : E → F} (hf : ContinuousAt f c)
    (hY : TendstoInMeasure μ Y l (fun _ ↦ c)) :
    TendstoInMeasure μ (fun n ω ↦ f (Y n ω)) l (fun _ ↦ f c) := by
  rw [tendstoInMeasure_iff_dist] at hY ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hf ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hY δ hδ) (fun _ ↦ zero_le)
    fun n ↦ measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra h
  exact (hδε (not_le.1 h)).not_ge hω

/-- If `Y n` converges in probability to a nonzero constant `c`, then `(Y n)⁻¹` converges in
probability to `c⁻¹`. -/
theorem TendstoInMeasure.inv_const {Y : ι → Ω → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hY : TendstoInMeasure μ Y l (fun _ ↦ c)) :
    TendstoInMeasure μ (fun n ω ↦ (Y n ω)⁻¹) l (fun _ ↦ c⁻¹) :=
  TendstoInMeasure.comp_const_of_continuousAt (continuousAt_inv₀ hc) hY

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [l.IsCountablyGenerated]

/-- **Slutsky's theorem (scalar-multiple form).** If `X n` converges in distribution to `Z` and
the real random variables `Y n` (on the same space as the `X n`) converge in probability to the
constant `c`, then `Y n • X n` converges in distribution to `c • Z`. -/
theorem TendstoInDistribution.smul_of_tendstoInMeasure_const {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {X : ι → Ω → E} {Z : Ω' → E} {Y : ι → Ω → ℝ} {c : ℝ}
    (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ) μ')
    (hY : TendstoInMeasure μ Y l (fun _ ↦ c)) (hY_meas : ∀ n, AEMeasurable (Y n) μ) :
    TendstoInDistribution (fun n ω ↦ Y n ω • X n ω) l (fun ω ↦ c • Z ω) (fun _ ↦ μ) μ' :=
  hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : E × ℝ ↦ p.2 • p.1) (by fun_prop) hY hY_meas

/-- **Slutsky's theorem (product form).** If the real random variables `X n` converge in
distribution to `Z` and `Y n` (on the same space as the `X n`) converge in probability to the
constant `c`, then `X n * Y n` converges in distribution to `c * Z`. -/
theorem TendstoInDistribution.mul_of_tendstoInMeasure_const {X Y : ι → Ω → ℝ} {Z : Ω' → ℝ}
    {c : ℝ} (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ) μ')
    (hY : TendstoInMeasure μ Y l (fun _ ↦ c)) (hY_meas : ∀ n, AEMeasurable (Y n) μ) :
    TendstoInDistribution (fun n ω ↦ X n ω * Y n ω) l (fun ω ↦ c * Z ω) (fun _ ↦ μ) μ' :=
  hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ ↦ p.2 * p.1) (by fun_prop) hY hY_meas |>.congr
    (fun _ ↦ ae_of_all _ fun _ ↦ mul_comm _ _) (ae_of_all _ fun _ ↦ rfl)

/-- **Slutsky's theorem (ratio form).** If the real random variables `X n` converge in
distribution to `Z` and `Y n` (on the same space as the `X n`) converge in probability to the
nonzero constant `c`, then `X n / Y n` converges in distribution to `Z / c`. -/
theorem TendstoInDistribution.div_of_tendstoInMeasure_const {X Y : ι → Ω → ℝ} {Z : Ω' → ℝ}
    {c : ℝ} (hc : c ≠ 0) (hXZ : TendstoInDistribution X l Z (fun _ ↦ μ) μ')
    (hY : TendstoInMeasure μ Y l (fun _ ↦ c)) (hY_meas : ∀ n, AEMeasurable (Y n) μ) :
    TendstoInDistribution (fun n ω ↦ X n ω / Y n ω) l (fun ω ↦ Z ω / c) (fun _ ↦ μ) μ' :=
  hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ ↦ p.1 * p.2) (by fun_prop) (hY.inv_const hc)
    (fun n ↦ (hY_meas n).inv) |>.congr
    (fun _ ↦ ae_of_all _ fun _ ↦ (div_eq_mul_inv _ _).symm)
    (ae_of_all _ fun _ ↦ (div_eq_mul_inv _ _).symm)

end MeasureTheory

namespace MeasureTheory

/-- Convergence in distribution depends on the limit only through its law: if `X n →ᵈ Y` and
`Z` (on any probability space) has the same law `ρ` as `Y`, then `X n →ᵈ Z`. -/
theorem TendstoInDistribution.congr_hasLaw {ι Ω Ω₂ Ω₃ E : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace Ω₂] [MeasurableSpace Ω₃] [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {l : Filter ι} {μ : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μ i)]
    {P₂ : Measure Ω₂} {P₃ : Measure Ω₃} [IsProbabilityMeasure P₂] [IsProbabilityMeasure P₃]
    {X : ι → Ω → E} {Y : Ω₂ → E} {Z : Ω₃ → E} {ρ : Measure E}
    (h : TendstoInDistribution X l Y μ P₂) (hY : ProbabilityTheory.HasLaw Y ρ P₂)
    (hZ : ProbabilityTheory.HasLaw Z ρ P₃) :
    TendstoInDistribution X l Z μ P₃ where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := hZ.aemeasurable
  tendsto := by
    convert h.tendsto using 3
    exact congrArg 𝓝 (Subtype.ext (hZ.map_eq.trans hY.map_eq.symm))

end MeasureTheory
