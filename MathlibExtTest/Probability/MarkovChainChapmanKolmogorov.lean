/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainChapmanKolmogorov

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open MathlibExt.Probability.MarkovChainChapmanKolmogorov

namespace MathlibExtTest.Probability.MarkovChainChapmanKolmogorov

/-- The conditional form, restated with its exact public signature. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : IsMarkovChain X ℱ κ μ) (m n : ℕ) {B : Set S} (hB : MeasurableSet B) :
    μ[((B.indicator (fun _ => (1 : ℝ))) ∘ (X (m + n))) | ℱ m] =ᵐ[μ]
      fun ω => ((κ ^ n) (X m ω) B).toReal :=
  hMC.condExp_indicator_eq m n hB

/-- The forward (law) form, restated with its exact public signature. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : IsMarkovChain X ℱ κ μ) (m n : ℕ) :
    μ.map (X (m + n)) = (μ.map (X m)).bind (fun x => (κ ^ n) x) :=
  hMC.map_eq_bind_pow m n

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

/-- The conditional form applied to the constant chain at `m = 0, n = 1`:
the conditional probability of `{X₁ ∈ B}` given `ℱ 0` is the one-step
constant-kernel probability `(dirac c) B`. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (c : S) {B : Set S} (hB : MeasurableSet B) :
    μ[((B.indicator (fun _ => (1 : ℝ))) ∘
      ((fun _ (_ : Ω) => c) (0 + 1))) | ℱ 0] =ᵐ[μ]
      fun ω => (((Kernel.const S (Measure.dirac c)) ^ 1)
        ((fun _ (_ : Ω) => c) 0 ω) B).toReal :=
  (constant_chain_isMarkovChain ℱ c).condExp_indicator_eq 0 1 hB

#print axioms MathlibExt.Probability.MarkovChainChapmanKolmogorov.IsMarkovChain.condExp_indicator_eq
#print axioms MathlibExt.Probability.MarkovChainChapmanKolmogorov.IsMarkovChain.map_eq_bind_pow

end MathlibExtTest.Probability.MarkovChainChapmanKolmogorov
