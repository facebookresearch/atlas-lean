/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainFunctionCK
import MathlibExt.Probability.MarkovChainChapmanKolmogorov

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open MathlibExt.Probability.MarkovChainFunctionCK.IsMarkovChain
open MathlibExt.Probability.MarkovChainChapmanKolmogorov

namespace MathlibExtTest.Probability.MarkovChainFunctionCK

/-- The one-step function form, restated with its exact public signature. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : IsMarkovChain X ℱ κ μ) (k : ℕ) {f : S → ℝ}
    (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (k + 1) | ℱ k ] =ᵐ[μ] fun ω => ∫ y, f y ∂ (κ (X k ω)) :=
  condExp_one_step_eq_integral hMC k hf hfb

/-- The `n`-step function form, restated with its exact public signature. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : IsMarkovChain X ℱ κ μ) (m n : ℕ) {f : S → ℝ}
    (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (m + n) | ℱ m ] =ᵐ[μ]
      fun ω => ∫ y, f y ∂ (κ ^ n) (X m ω) :=
  condExp_comp_eq_integral_pow hMC m n hf hfb

/-- The integrated form, restated with its exact public signature. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : IsMarkovChain X ℱ κ μ) (m n : ℕ) {f : S → ℝ}
    (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    ∫ ω, f (X (m + n) ω) ∂μ =
      ∫ ω, (∫ y, f y ∂ (κ ^ n) (X m ω)) ∂μ :=
  integral_comp_eq hMC m n hf hfb

/-- A constant chain is a Markov chain with the constant Dirac kernel:
at each time the next state is `c`, so the one-step conditional
probability of `B` is `1` if `c ∈ B` and `0` otherwise, on both sides. -/
theorem constant_chain_isMarkovChain {Ω S : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace S] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (c : S) :
    IsMarkovChain (fun _ (_ : Ω) => c) ℱ (Kernel.const S (Measure.dirac c)) μ := by
  refine ⟨?_, ?_⟩
  · exact fun _ => measurable_const
  · intro n B hB
    classical
    have h_lhs : (B.indicator (fun _ => (1 : ℝ))) ∘ ((fun _ (_ : Ω) => c) (n + 1)) =
        fun _ => if c ∈ B then (1 : ℝ) else 0 := by
      ext ω
      simp [Set.indicator]
    rw [h_lhs, condExp_const (ℱ.le n)]
    refine Filter.EventuallyEq.of_eq ?_
    funext ω
    by_cases h : c ∈ B
    · simp [Kernel.const_apply, Measure.dirac_apply' _ hB, h]
    · simp [Kernel.const_apply, Measure.dirac_apply' _ hB, h]

/-- The `n`-step function form applied to the constant chain: the
conditional expectation of `f` at time `m + n` given `ℱ m` is the
`n`-step constant-kernel integral of `f` at `c`. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (c : S) (m n : ℕ) {f : S → ℝ}
    (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ ((fun _ (_ : Ω) => c) (m + n)) | ℱ m ] =ᵐ[μ]
      fun ω => ∫ y, f y ∂ (((Kernel.const S (Measure.dirac c)) ^ n)
        ((fun _ (_ : Ω) => c) m ω)) :=
  condExp_comp_eq_integral_pow
    (constant_chain_isMarkovChain ℱ c) m n hf hfb

/-- The one-step kernel integral of the identity on `ℝ` against the
constant Dirac kernel at `c` is `c`: the constant chain really does stay
at `c`. -/
example {Ω : Type*} (c : ℝ) :
    (fun ω : Ω => ∫ y, y ∂ (((Kernel.const ℝ (Measure.dirac c)) ^ 1)
      ((fun _ (_ : Ω) => c) 0 ω))) = fun _ => c := by
  funext ω
  rw [pow_one, Kernel.const_apply]
  exact integral_dirac' _ _ stronglyMeasurable_id

#print axioms condExp_one_step_eq_integral
#print axioms condExp_comp_eq_integral_pow
#print axioms integral_comp_eq


/-- Zero steps retain the present state and the original boundedness hypothesis. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : IsMarkovChain X ℱ κ μ) (k : ℕ) {f : S → ℝ}
    (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X k | ℱ k ] =ᵐ[μ] f ∘ X k := by
  have h := condExp_comp_eq_integral_pow hMC k 0 hf hfb
  have hdirac : (fun ω => ∫ y, f y ∂(κ ^ 0) (X k ω)) = f ∘ X k := by
    funext ω
    change ∫ y, f y ∂Kernel.id (X k ω) = f (X k ω)
    rw [Kernel.id_apply]
    exact integral_dirac' _ _ hf
  rwa [Nat.add_zero, hdirac] at h

/-- The general formula specializes to the one-step transition kernel. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : IsMarkovChain X ℱ κ μ) (k : ℕ) {f : S → ℝ}
    (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (k + 1) | ℱ k ] =ᵐ[μ] fun ω => ∫ y, f y ∂κ (X k ω) := by
  simpa only [pow_one] using condExp_comp_eq_integral_pow hMC k 1 hf hfb

/-- A signed indicator is a bounded state function with a literal uniform bound. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : IsMarkovChain X ℱ κ μ) (k n : ℕ) {B : Set S} (hB : MeasurableSet B) :
    μ[ (B.indicator (fun _ => (-2 : ℝ))) ∘ X (k + n) | ℱ k ] =ᵐ[μ]
      fun ω => ∫ y, B.indicator (fun _ => (-2 : ℝ)) y ∂(κ ^ n) (X k ω) := by
  have hf : StronglyMeasurable (B.indicator (fun _ => (-2 : ℝ))) :=
    stronglyMeasurable_const.indicator hB
  have hfb : ∃ C, ∀ y, ‖B.indicator (fun _ => (-2 : ℝ)) y‖ ≤ C := by
    classical
    refine ⟨2, fun y => ?_⟩
    by_cases hy : y ∈ B
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  exact condExp_comp_eq_integral_pow hMC k n hf hfb

/-- Existing canonical witnesses are accepted by the one-step function API. -/
theorem canonical_one_step {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : MathlibExt.Probability.MarkovChainChapmanKolmogorov.IsMarkovChain X ℱ κ μ)
    (k : ℕ) {f : S → ℝ} (hf : StronglyMeasurable f)
    (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (k + 1) | ℱ k ] =ᵐ[μ] fun ω => ∫ y, f y ∂κ (X k ω) :=
  MathlibExt.Probability.MarkovChainFunctionCK.IsMarkovChain.condExp_one_step_eq_integral
    hMC k hf hfb

/-- Existing canonical witnesses are accepted at every natural step count. -/
theorem canonical_n_steps {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : MathlibExt.Probability.MarkovChainChapmanKolmogorov.IsMarkovChain X ℱ κ μ)
    (k n : ℕ) {f : S → ℝ} (hf : StronglyMeasurable f)
    (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (k + n) | ℱ k ] =ᵐ[μ]
      fun ω => ∫ y, f y ∂(κ ^ n) (X k ω) :=
  MathlibExt.Probability.MarkovChainFunctionCK.IsMarkovChain.condExp_comp_eq_integral_pow
    hMC k n hf hfb

/-- Existing canonical witnesses are accepted by the integrated function API. -/
theorem canonical_integrated {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : MathlibExt.Probability.MarkovChainChapmanKolmogorov.IsMarkovChain X ℱ κ μ)
    (k n : ℕ) {f : S → ℝ} (hf : StronglyMeasurable f)
    (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    ∫ ω, f (X (k + n) ω) ∂μ =
      ∫ ω, (∫ y, f y ∂(κ ^ n) (X k ω)) ∂μ :=
  MathlibExt.Probability.MarkovChainFunctionCK.IsMarkovChain.integral_comp_eq hMC k n hf hfb

/-- A canonical witness also works at the zero-step boundary. -/
theorem canonical_zero_steps {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : MathlibExt.Probability.MarkovChainChapmanKolmogorov.IsMarkovChain X ℱ κ μ)
    (k : ℕ) {f : S → ℝ} (hf : StronglyMeasurable f)
    (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (k + 0) | ℱ k ] =ᵐ[μ]
      fun ω => ∫ y, f y ∂(κ ^ 0) (X k ω) :=
  MathlibExt.Probability.MarkovChainFunctionCK.IsMarkovChain.condExp_comp_eq_integral_pow
    hMC k 0 hf hfb

/-- The general canonical function API agrees with one-step indexing. -/
theorem canonical_one_step_from_n_steps {Ω S : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace S] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : MathlibExt.Probability.MarkovChainChapmanKolmogorov.IsMarkovChain X ℱ κ μ)
    (k : ℕ) {f : S → ℝ} (hf : StronglyMeasurable f)
    (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (k + 1) | ℱ k ] =ᵐ[μ]
      fun ω => ∫ y, f y ∂(κ ^ 1) (X k ω) :=
  MathlibExt.Probability.MarkovChainFunctionCK.IsMarkovChain.condExp_comp_eq_integral_pow
    hMC k 1 hf hfb
end MathlibExtTest.Probability.MarkovChainFunctionCK
