/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.Kernel.MeasurableLIntegral

@[expose] public section

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace MathlibExt.Probability.MarkovChainChapmanKolmogorov

/-!
# Chapman–Kolmogorov equations for discrete-time Markov chains

For a discrete-time Markov chain `X` with transition kernel `κ`, the
`n`-step transition probabilities are given by the powers `κ ^ n` of the
kernel. This file derives two consequences of `IsMarkovChain`:

* the conditional form: given the past up to time `m`, the conditional
  probability that `X (m + n)` lies in `B` is `(κ ^ n) (X m) B`;
* the forward (law) form: the law of `X (m + n)` is the law of `X m`
  pushed forward through `κ ^ n`.

## Source

The `IsMarkovChain` definition comes from "Definition (Markov chain,
general)" (Lecture 30/31) in `v1/Atlas/TheoryOfProbability/targets.yaml`
and `v1/Atlas/TheoryOfProbability/code/MarkovChain.lean`. Its fields are
adaptedness and the one-step conditional-indicator identity. The archived
`IsMarkovChain.markov_property` in
`v1/Atlas/TheoryOfProbability/code/MarkovPropertyChain.lean` is a
projection of that one-step field.

The two `n`-step results below are new consequences of this definition.
They do not formalize the separate canonical path-space Markov property
for arbitrary bounded measurable future path functionals.

## Relation to Mathlib

Mathlib provides kernel powers and their composition identities in
`Mathlib.Probability.Kernel.Composition.Comp`. The induction here uses
`ProbabilityTheory.Kernel.pow_succ_apply_eq_lintegral`, measure binding,
and set integrals of conditional expectations. The conditional result
then uses `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`.

## Main results

* `IsMarkovChain`: `X` is a Markov chain with transition kernel `κ`
  with respect to the filtration `ℱ` under `μ` (adapted, plus the
  one-step conditional-probability identity).
* `IsMarkovChain.condExp_indicator_eq`: the conditional form above.
* `IsMarkovChain.map_eq_bind_pow`: the forward form above.
-/

/-- `IsMarkovChain X ℱ κ μ` asserts that the sequence of random variables `X : ℕ → Ω → S`
is a Markov chain with respect to the filtration `ℱ` with transition probability kernel
`κ` under the measure `μ`. Concretely it requires that `X` is `ℱ`-adapted and that for
each `n` and measurable `B ⊆ S`,

  `μ[1_{B} ∘ X (n+1) | ℱ n] = κ (X n ·) B  μ`-a.e.,

which is the standard form `P(X_{n+1} ∈ B | ℱ_n) = κ(X_n, B)` of the Markov property. -/
structure IsMarkovChain {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (κ : Kernel S S)
    [IsMarkovKernel κ] (μ : Measure Ω) : Prop where
  adapted : Adapted ℱ X
  markov_prop : ∀ n : ℕ, ∀ B : Set S, MeasurableSet B →
    μ[(B.indicator (fun _ => (1 : ℝ))) ∘ (X (n + 1)) | ℱ n] =ᵐ[μ]
      fun ω => (κ (X n ω) B).toReal

namespace IsMarkovChain

variable {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]

omit [IsProbabilityMeasure μ] in
/-- Each coordinate of a Markov chain is measurable. -/
private lemma measurable (hMC : IsMarkovChain X ℱ κ μ) (n : ℕ) : Measurable (X n) :=
  hMC.adapted.measurable

/-- Powers of a Markov kernel are Markov kernels. -/
private instance isMarkovKernel_pow (n : ℕ) : IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero =>
    show IsMarkovKernel (Kernel.id : Kernel S S)
    infer_instance
  | succ n ih =>
    show IsMarkovKernel (Kernel.comp (κ ^ n) κ)
    infer_instance

omit [MeasurableSpace S] in
/-- Composing an indicator with a map is the indicator of the preimage. -/
private lemma indicator_comp_preimage {Y : Ω → S} {B : Set S} :
    (B.indicator (fun _ => (1 : ℝ))) ∘ Y =
      Set.indicator (Y ⁻¹' B) (fun _ => (1 : ℝ)) := by
  ext ω
  rw [Function.comp_apply]
  by_cases hω : Y ω ∈ B
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
  · rw [Set.indicator_of_notMem hω,
      Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h))]

/-- One-step form of the transition law, as a measure identity: for `C ∈ ℱ k`,
the mass of `C ∩ {X (k+1) ∈ B}` equals the `κ`-average of `B` over `C`.
This is the set-integral form of the defining `markov_prop`. -/
private lemma measure_inter_preimage_eq_lintegral
    (hMC : IsMarkovChain X ℱ κ μ) (k : ℕ) {B : Set S} (hB : MeasurableSet B)
    {C : Set Ω} (hC : MeasurableSet[ℱ k] C) :
    μ (C ∩ X (k + 1) ⁻¹' B) = ∫⁻ ω in C, κ (X k ω) B ∂μ := by
  have hX_meas : Measurable (X (k + 1)) := hMC.measurable (k + 1)
  have hXk_meas : Measurable (X k) := hMC.measurable k
  have hf_int : Integrable ((B.indicator (fun _ => (1 : ℝ))) ∘ (X (k + 1))) μ := by
    rw [indicator_comp_preimage]
    exact (integrable_const (1 : ℝ)).indicator (hX_meas hB)
  have h_set : ∫ ω in C,
      μ[((B.indicator (fun _ => (1 : ℝ))) ∘ (X (k + 1))) | ℱ k] ω ∂μ =
      ∫ ω in C, ((B.indicator (fun _ => (1 : ℝ))) ∘ (X (k + 1))) ω ∂μ :=
    setIntegral_condExp (ℱ.le k) hf_int hC
  have h_ae' : ∀ᵐ ω ∂μ, ω ∈ C →
      μ[((B.indicator (fun _ => (1 : ℝ))) ∘ (X (k + 1))) | ℱ k] ω =
        (κ (X k ω) B).toReal :=
    (ae_restrict_iff' ((ℱ.le k) C hC)).mp (ae_restrict_of_ae (hMC.markov_prop k B hB))
  rw [setIntegral_congr_ae ((ℱ.le k) C hC) h_ae'] at h_set
  have h_lhs : ∫ ω in C, ((B.indicator (fun _ => (1 : ℝ))) ∘ (X (k + 1))) ω ∂μ =
      (μ (C ∩ X (k + 1) ⁻¹' B)).toReal := by
    rw [indicator_comp_preimage, setIntegral_indicator (hX_meas hB),
      setIntegral_const, smul_eq_mul, mul_one]
    rfl
  have h_rhs : ∫ ω in C, (κ (X k ω) B).toReal ∂μ =
      (∫⁻ ω in C, κ (X k ω) B ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [ENNReal.ofReal_toReal]
      exact (measure_lt_top _ _).ne
    · exact Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg
    · exact ((Kernel.measurable_coe κ hB).comp hXk_meas).ennreal_toReal.aestronglyMeasurable
  rw [h_lhs, h_rhs] at h_set
  have h_fin_lhs : μ (C ∩ X (k + 1) ⁻¹' B) ≠ ⊤ := (measure_lt_top _ _).ne
  have h_fin_rhs : ∫⁻ ω in C, κ (X k ω) B ∂μ ≠ ⊤ := by
    have h_le : ∫⁻ ω in C, κ (X k ω) B ∂μ ≤ 1 := by
      calc ∫⁻ ω in C, κ (X k ω) B ∂μ ≤ ∫⁻ ω, κ (X k ω) B ∂μ :=
            setLIntegral_le_lintegral _ _
        _ ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := lintegral_mono fun ω => by
              calc κ (X k ω) B ≤ κ (X k ω) Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
        _ = 1 := by simp [lintegral_const, measure_univ]
    exact (lt_of_le_of_lt h_le ENNReal.one_lt_top).ne
  exact (ENNReal.toReal_eq_toReal_iff' h_fin_lhs h_fin_rhs).mp h_set.symm

/-- The `n`-step transition law, as a measure identity: restricting `μ` to
any `C ∈ ℱ m` and pushing forward through `X (m + n)` is the same as
pushing forward through `X m` and then binding with `κ ^ n`. -/
private lemma map_restrict_eq_bind_pow (hMC : IsMarkovChain X ℱ κ μ)
    (n : ℕ) (m : ℕ) {C : Set Ω} (hC : MeasurableSet[ℱ m] C) :
    (μ.restrict C).map (X (m + n)) =
      ((μ.restrict C).map (X m)).bind (fun x => (κ ^ n) x) := by
  induction n generalizing m with
  | zero =>
    rw [Nat.add_zero]
    have h_fun : (fun x => ((κ ^ 0) x : Measure S)) = Measure.dirac := by
      funext x
      show (Kernel.id : Kernel S S) x = Measure.dirac x
      exact Kernel.id_apply x
    rw [h_fun, Measure.bind_dirac]
  | succ n ih =>
    ext A hA
    have h_lhs : ((μ.restrict C).map (X (m + (n + 1)))) A =
        μ (C ∩ X (m + (n + 1)) ⁻¹' A) := by
      rw [Measure.map_apply (hMC.measurable _) hA,
        Measure.restrict_apply (hMC.measurable _ hA), Set.inter_comm]
    have h_step1 : μ (C ∩ X (m + (n + 1)) ⁻¹' A) =
        ∫⁻ ω in C, κ (X (m + n) ω) A ∂μ :=
      hMC.measure_inter_preimage_eq_lintegral (m + n) hA
        ((ℱ.mono (Nat.le_add_right m n)) C hC)
    have h_step2 : (∫⁻ ω in C, κ (X (m + n) ω) A ∂μ) =
        ∫⁻ y, κ y A ∂(((μ.restrict C).map (X (m + n)))) := by
      rw [lintegral_map (Kernel.measurable_coe κ hA) (hMC.measurable (m + n))]
    have h_step3 : ∫⁻ y, κ y A ∂((μ.restrict C).map (X (m + n))) =
        ∫⁻ y, κ y A ∂(((μ.restrict C).map (X m)).bind (fun x => (κ ^ n) x)) := by
      rw [ih m hC]
    have h_step4 : ∫⁻ y, κ y A ∂(((μ.restrict C).map (X m)).bind (fun x => (κ ^ n) x)) =
        ∫⁻ ω in C, ∫⁻ y, κ y A ∂((κ ^ n) (X m ω)) ∂μ := by
      rw [Measure.lintegral_bind (Kernel.aemeasurable (κ ^ n))
        (Kernel.measurable_coe κ hA).aemeasurable,
        lintegral_map (Measurable.lintegral_kernel (Kernel.measurable_coe κ hA))
          (hMC.measurable m)]
    have h_step5 : (∫⁻ ω in C, ∫⁻ y, κ y A ∂((κ ^ n) (X m ω)) ∂μ) =
        ∫⁻ ω in C, (κ ^ (n + 1)) (X m ω) A ∂μ := by
      apply setLIntegral_congr_fun ((ℱ.le m) C hC)
      intro ω _
      exact (Kernel.pow_succ_apply_eq_lintegral κ n (X m ω) hA).symm
    have h_rhs : (((μ.restrict C).map (X m)).bind (fun x => (κ ^ (n + 1)) x)) A =
        ∫⁻ a, (κ ^ (n + 1)) a A ∂(((μ.restrict C).map (X m))) := by
      rw [Measure.bind_apply hA (Kernel.aemeasurable (κ ^ (n + 1)))]
    rw [h_lhs, h_step1, h_step2, h_step3, h_step4, h_step5, h_rhs]
    exact (lintegral_map (Kernel.measurable_coe (κ ^ (n + 1)) hA)
      (hMC.measurable m)).symm

/-- **Chapman–Kolmogorov equations, conditional form.** For a Markov chain
with transition kernel `κ`, the conditional probability that `X (m + n)`
lies in `B`, given the past up to time `m`, is `(κ ^ n) (X m) B`. For
`n = 1` this is the defining one-step Markov property; for general `n`
the `n`-step kernel is the `n`-fold composition of `κ`. -/
theorem condExp_indicator_eq (hMC : IsMarkovChain X ℱ κ μ)
    (m n : ℕ) {B : Set S} (hB : MeasurableSet B) :
    μ[((B.indicator (fun _ => (1 : ℝ))) ∘ (X (m + n))) | ℱ m] =ᵐ[μ]
      fun ω => ((κ ^ n) (X m ω) B).toReal := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le m) ?_ ?_ ?_ ?_).symm
  · rw [indicator_comp_preimage]
    exact (integrable_const (1 : ℝ)).indicator ((hMC.measurable _) hB)
  · intro s _hs _hμs
    exact (integrable_const (1 : ℝ)).mono'
      (((Kernel.measurable_coe (κ ^ n) hB).comp (hMC.measurable m)).ennreal_toReal
        |>.aestronglyMeasurable.restrict)
      (ae_of_all _ fun ω => by
        have h1 : ((κ ^ n) (X m ω) B).toReal ≤ 1 := by
          apply ENNReal.toReal_le_of_le_ofReal (by norm_num)
          rw [ENNReal.ofReal_one]
          calc (κ ^ n) (X m ω) B ≤ (κ ^ n) (X m ω) Set.univ :=
                measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        simpa using h1)
  · intro s hs _
    have h_lhs : ∫ x in s, ((B.indicator (fun _ => (1 : ℝ))) ∘ (X (m + n))) x ∂μ =
        (μ (s ∩ X (m + n) ⁻¹' B)).toReal := by
      rw [indicator_comp_preimage, setIntegral_indicator ((hMC.measurable _) hB),
        setIntegral_const, smul_eq_mul, mul_one]
      rfl
    have h_rhs : ∫ x in s, (fun ω => ((κ ^ n) (X m ω) B).toReal) x ∂μ =
        (∫⁻ x in s, (κ ^ n) (X m x) B ∂μ).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae]
      · congr 1
        apply lintegral_congr_ae
        filter_upwards with ω
        rw [ENNReal.ofReal_toReal]
        exact (measure_lt_top _ _).ne
      · exact Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg
      · exact ((Kernel.measurable_coe (κ ^ n) hB).comp (hMC.measurable m)).ennreal_toReal.aestronglyMeasurable
    have h_key : μ (s ∩ X (m + n) ⁻¹' B) = ∫⁻ x in s, (κ ^ n) (X m x) B ∂μ := by
      have h1 : μ (s ∩ X (m + n) ⁻¹' B) = ((μ.restrict s).map (X (m + n))) B := by
        rw [Measure.map_apply (hMC.measurable _) hB,
          Measure.restrict_apply ((hMC.measurable _) hB), Set.inter_comm]
      have h2 : (∫⁻ x in s, (κ ^ n) (X m x) B ∂μ) =
          (((μ.restrict s).map (X m)).bind (fun x => (κ ^ n) x)) B := by
        rw [Measure.bind_apply hB (Kernel.aemeasurable (κ ^ n)),
          lintegral_map (Kernel.measurable_coe (κ ^ n) hB) (hMC.measurable m)]
      rw [h1, hMC.map_restrict_eq_bind_pow n m hs, ← h2]
    rw [h_lhs, h_rhs, h_key]
  · have h_meas : Measurable[ℱ m] (fun ω => ((κ ^ n) (X m ω) B).toReal) := by
      have h1 : Measurable (fun x : S => ((κ ^ n) x B).toReal) :=
        (Kernel.measurable_coe (κ ^ n) hB).ennreal_toReal
      exact h1.comp (hMC.adapted m)
    exact h_meas.stronglyMeasurable.aestronglyMeasurable

/-- **Chapman–Kolmogorov equations, forward (law) form.** The law of
`X (m + n)` is the law of `X m` pushed forward through the `n`-step
kernel `κ ^ n`. -/
theorem map_eq_bind_pow (hMC : IsMarkovChain X ℱ κ μ) (m n : ℕ) :
    μ.map (X (m + n)) = (μ.map (X m)).bind (fun x => (κ ^ n) x) := by
  have h := hMC.map_restrict_eq_bind_pow n m MeasurableSet.univ
  rwa [Measure.restrict_univ] at h

end IsMarkovChain

end MathlibExt.Probability.MarkovChainChapmanKolmogorov

end
