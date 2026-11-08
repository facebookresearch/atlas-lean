/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainChapmanKolmogorov
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace MathlibExt.Probability.MarkovChainFunctionCK

open MathlibExt.Probability.MarkovChainChapmanKolmogorov

/-!
# Chapman–Kolmogorov equations for bounded measurable functions

For a discrete-time Markov chain `X` with transition kernel `κ`, the
`n`-step transition probabilities are the kernel powers `κ ^ n`. The
indicator form of this statement (conditional probability that
`X (m + n)` lies in `B`) is the Chapman–Kolmogorov theorem. This file
proves the function form: for every bounded measurable `f`, the
conditional expectation of `f (X (m + n))` given the past up to time `m`
is the `κ ^ n`-integral of `f` evaluated at `X m`.

## Source

The canonical `IsMarkovChain` predicate is defined in
`MathlibExt.Probability.MarkovChainChapmanKolmogorov`. It comes from
"Definition (Markov chain, general)" (Lecture 30/31) in
`v1/Atlas/TheoryOfProbability/targets.yaml` and
`v1/Atlas/TheoryOfProbability/code/MarkovChain.lean`: adaptedness and
`P(X_{n+1} ∈ B | ℱ_n) = κ(X_n, B)` for every measurable `B`.
The archived `IsMarkovChain.markov_property` in
`v1/Atlas/TheoryOfProbability/code/MarkovPropertyChain.lean` projects
that one-step indicator identity.

The three results here are its bounded state-function consequences.
The separate Lecture 31 property for arbitrary bounded future path
functionals has a larger scope.

## Relation to Mathlib and the canonical chain API

Mathlib provides kernel powers and `ProbabilityTheory.Kernel.integral_comp`.
The canonical `IsMarkovChain.condExp_indicator_eq` identifies the restricted
future law on each set measurable in `ℱ m`. Integrating a bounded strongly
measurable function against that law gives the function formula below.
The integrated formula directly uses the canonical
`IsMarkovChain.map_eq_bind_pow`. No additional Markov predicate is defined here.

The `IsMarkovChain` namespace below keeps the function theorem names; each
witness argument has the canonical predicate type.

## Main results

* `IsMarkovChain.condExp_one_step_eq_integral`: the one-step function
  form: `μ[ f ∘ X (k+1) | ℱ k ] =ᵐ fun ω => ∫ y, f y ∂ κ (X k ω)`.
* `IsMarkovChain.condExp_comp_eq_integral_pow`: the `n`-step function
  form: `μ[ f ∘ X (m+n) | ℱ m ] =ᵐ fun ω => ∫ y, f y ∂ (κ ^ n) (X m ω)`.
* `IsMarkovChain.integral_comp_eq`: the integrated form:
  `∫ ω, f (X (m+n) ω) ∂μ = ∫ ω, (∫ y, f y ∂ (κ ^ n) (X m ω)) ∂μ`.
-/

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

/-- Bochner integral against a bind: for a bounded strongly measurable
`f`, integrating against `ν.bind κ` is the `ν`-integral of the
`κ`-integrals. This follows from `Kernel.integral_comp` applied to a
constant kernel with value `ν`. -/
private theorem integral_bind_of_bounded {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {ν : Measure α} [IsFiniteMeasure ν]
    {η : Kernel α β} [IsMarkovKernel η] {f : β → ℝ}
    (hf : StronglyMeasurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ∫ y, f y ∂ (ν.bind η) = ∫ x, ∫ y, f y ∂ (η x) ∂ν := by
  have h_int : Integrable f (ν.bind η) :=
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  exact Kernel.integral_comp (κ := Kernel.const Unit ν) (η := η) (a := ()) h_int

/-- The canonical indicator formula identifies each restricted future law. -/
private lemma map_restrict_eq_bind_pow (hMC : IsMarkovChain X ℱ κ μ)
    (m n : ℕ) {C : Set Ω} (hC : MeasurableSet[ℱ m] C) :
    (μ.restrict C).map (X (m + n)) =
      ((μ.restrict C).map (X m)).bind (κ ^ n) := by
  ext B hB
  refine (ENNReal.toReal_eq_toReal_iff'
    (measure_lt_top _ _).ne (measure_lt_top _ _).ne).mp ?_
  change ((μ.restrict C).map (X (m + n))).real B =
    (((μ.restrict C).map (X m)).bind (κ ^ n)).real B
  rw [← integral_indicator_one hB, ← integral_indicator_one hB]
  let I : S → ℝ := B.indicator (fun _ => 1)
  have hI : StronglyMeasurable I := stronglyMeasurable_const.indicator hB
  have hIb : ∀ y, ‖I y‖ ≤ 1 := by
    intro y
    classical
    by_cases hy : y ∈ B <;> simp [I, hy]
  have h_int : Integrable (I ∘ X (m + n)) μ :=
    Integrable.of_bound (hI.measurable.comp (measurable hMC (m + n))).aestronglyMeasurable
      1 (ae_of_all _ fun ω => hIb (X (m + n) ω))
  calc ∫ y, I y ∂((μ.restrict C).map (X (m + n)))
      = ∫ ω in C, I (X (m + n) ω) ∂μ :=
        integral_map (measurable hMC (m + n)).aemeasurable hI.aestronglyMeasurable
    _ = ∫ ω in C, μ[I ∘ X (m + n) | ℱ m] ω ∂μ :=
        (setIntegral_condExp (ℱ.le m) h_int hC).symm
    _ = ∫ ω in C, ((κ ^ n) (X m ω) B).toReal ∂μ :=
        integral_congr_ae (ae_restrict_of_ae (hMC.condExp_indicator_eq m n hB))
    _ = ∫ ω in C, (∫ y, I y ∂(κ ^ n) (X m ω)) ∂μ := by
        simp only [I, integral_indicator_const (1 : ℝ) hB, smul_eq_mul, mul_one, Measure.real]
    _ = ∫ x, (∫ y, I y ∂(κ ^ n) x) ∂((μ.restrict C).map (X m)) :=
        (integral_map (measurable hMC m).aemeasurable
          hI.integral_kernel.aestronglyMeasurable).symm
    _ = ∫ y, I y ∂(((μ.restrict C).map (X m)).bind (κ ^ n)) :=
        (integral_bind_of_bounded hI hIb).symm

/-- **Chapman–Kolmogorov equations for bounded measurable functions.**
For a Markov chain `X` with transition kernel `κ`, the conditional
expectation of `f (X (m + n))` given the past up to time `m` is the
`κ ^ n`-integral of `f` evaluated at `X m`. For `n = 1` this is the
one-step function form; the general case follows by integrating the
canonical conditional-indicator formula over each past-measurable set. -/
theorem condExp_comp_eq_integral_pow (hMC : IsMarkovChain X ℱ κ μ)
    (m n : ℕ) {f : S → ℝ} (hf : StronglyMeasurable f)
    (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (m + n) | ℱ m ] =ᵐ[μ]
      fun ω => ∫ y, f y ∂ (κ ^ n) (X m ω) := by
  obtain ⟨C, hC⟩ := hfb
  have hXk : Measurable (X m) := (measurable hMC) m
  have hXk1 : Measurable (X (m + n)) := (measurable hMC) (m + n)
  have hf_int : Integrable (f ∘ X (m + n)) μ :=
    Integrable.of_bound (hf.measurable.comp hXk1).aestronglyMeasurable C
      (ae_of_all _ fun ω => hC (X (m + n) ω))
  have hg_sm : StronglyMeasurable (fun x => ∫ y, f y ∂ ((κ ^ n) x)) := hf.integral_kernel
  have hg_bdd : ∀ x, ‖∫ y, f y ∂ ((κ ^ n) x)‖ ≤ C := by
    intro x
    calc ‖∫ y, f y ∂ ((κ ^ n) x)‖ ≤ ∫ y, ‖f y‖ ∂ ((κ ^ n) x) := norm_integral_le_integral_norm _
      _ ≤ ∫ _, C ∂ ((κ ^ n) x) := by
          apply integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
          · exact integrable_const C
          · exact ae_of_all _ hC
      _ = C := by simp [integral_const]
  have hg_int : Integrable (fun ω => ∫ y, f y ∂ ((κ ^ n) (X m ω))) μ :=
    Integrable.of_bound (hg_sm.measurable.comp hXk).aestronglyMeasurable C
      (ae_of_all _ fun ω => hg_bdd (X m ω))
  have hg_meas : AEStronglyMeasurable[ℱ m]
      (fun ω => ∫ y, f y ∂ ((κ ^ n) (X m ω))) μ :=
    (hg_sm.measurable.comp (hMC.adapted m)).aestronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le m) hf_int ?_ ?_ hg_meas).symm
  · intro s _ _
    exact hg_int.integrableOn
  · intro s hCs _
    calc ∫ x in s, (∫ y, f y ∂ ((κ ^ n) (X m x))) ∂μ
        = ∫ y, (∫ z, f z ∂ ((κ ^ n) y)) ∂ ((μ.restrict s).map (X m)) := by
          symm
          exact integral_map (hXk.aemeasurable) hg_sm.aestronglyMeasurable
      _ = ∫ z, f z ∂ (((μ.restrict s).map (X m)).bind (κ ^ n)) :=
          (integral_bind_of_bounded hf hC).symm
      _ = ∫ z, f z ∂ ((μ.restrict s).map (X (m + n))) := by
          rw [map_restrict_eq_bind_pow hMC m n hCs]
      _ = ∫ x in s, (f ∘ X (m + n)) x ∂μ :=
          integral_map (hXk1.aemeasurable) hf.aestronglyMeasurable

/-- **One-step Chapman–Kolmogorov equation for functions.** For a
bounded measurable `f`, the conditional expectation of `f (X (k+1))`
given `ℱ k` is the `κ`-integral of `f` evaluated at `X k`. -/
theorem condExp_one_step_eq_integral (hMC : IsMarkovChain X ℱ κ μ) (k : ℕ)
    {f : S → ℝ} (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (k + 1) | ℱ k ] =ᵐ[μ] fun ω => ∫ y, f y ∂ (κ (X k ω)) := by
  simpa only [pow_one] using condExp_comp_eq_integral_pow hMC k 1 hf hfb

/-- **Integrated Chapman–Kolmogorov equation for functions.** The
unconditional expectation of `f (X (m + n))` is the expectation of the
`κ ^ n`-integral of `f` evaluated at `X m`. -/
theorem integral_comp_eq (hMC : IsMarkovChain X ℱ κ μ)
    (m n : ℕ) {f : S → ℝ} (hf : StronglyMeasurable f)
    (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    ∫ ω, f (X (m + n) ω) ∂μ =
      ∫ ω, (∫ y, f y ∂ (κ ^ n) (X m ω)) ∂μ := by
  obtain ⟨C, hC⟩ := hfb
  calc ∫ ω, f (X (m + n) ω) ∂μ
      = ∫ y, f y ∂μ.map (X (m + n)) :=
        (integral_map (measurable hMC (m + n)).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂((μ.map (X m)).bind (κ ^ n)) := by
        rw [hMC.map_eq_bind_pow m n]
    _ = ∫ x, (∫ y, f y ∂(κ ^ n) x) ∂μ.map (X m) :=
        integral_bind_of_bounded hf hC
    _ = ∫ ω, (∫ y, f y ∂(κ ^ n) (X m ω)) ∂μ :=
        integral_map (measurable hMC m).aemeasurable hf.integral_kernel.aestronglyMeasurable

end IsMarkovChain

end MathlibExt.Probability.MarkovChainFunctionCK

end
