/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KolmogorovCycleNecessity
public import MathlibExt.Probability.MarkovChainChapmanKolmogorov

import Mathlib.MeasureTheory.Measure.Dirac.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal

namespace MathlibExt.Probability.FiniteMarkovChain

/-!
# Finite-state Markov chains

A finite-state Markov chain is a sequence `X : ℕ → Ω → Fin (M + 1)` whose
one-step conditional probabilities are given by a row-stochastic matrix `P`:
`μ[Xₙ₊₁ = j | ℱₙ] = P.prob (Xₙ) j` almost surely.

## Source and canonical definitions

The finite singleton-probability specification follows
`v1/Atlas/TheoryOfProbability/code/FiniteMarkovChain.lean`
("Definition: Markov chain, finite state", Lecture 30/31). Its filtration is
`Filtration ℕ m`, the type used by v1's `DiscreteFiltration Ω m`.
The transition matrix is the existing root `StochasticMatrix` from
`KolmogorovCycleNecessity`, with the same nonnegative entries and row sums.

The general definition from `v1/Atlas/TheoryOfProbability/code/MarkovChain.lean`
is the canonical `MarkovChainChapmanKolmogorov.IsMarkovChain`. Under the original
probability-space hypotheses, `IsFiniteMarkovChain.toIsMarkovChain` converts the
finite specification to this predicate using adaptedness and `condExp_indicator`.
The one-step forward law is the canonical `map_eq_bind_pow` specialized to one step.

The matrix-derived kernel, finite-set application and indicator argument are derived
results. The kernel uses Mathlib's `Kernel.ofFunOfCountable` with the original finite
sum of scaled Dirac measures. The canonical chain also supports existing n-step
indicator, law and bounded state-function APIs in `MarkovChainFunctionCK`; the separate
property for arbitrary future path functionals has a larger scope.
-/

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- `IsFiniteMarkovChain X P ℱ μ` asserts that the sequence `X : ℕ → Ω → Fin (M+1)`
is a Markov chain with transition matrix `P`, adapted to the filtration `ℱ`,
under the measure `μ`. Concretely: each `X n` is `ℱ n`-measurable, and the conditional
probability that `X (n+1) = j` given `ℱ n` equals `P.prob (X n) j`, matching the
Markov property `P(X_{n+1} = j | X_n = i, ...) = P_{ij}`.
Ported verbatim from `v1/Atlas/TheoryOfProbability/code/FiniteMarkovChain.lean`;
`v1` writes the filtration as `DiscreteFiltration Ω m`, which is `Filtration ℕ m`. -/
structure IsFiniteMarkovChain {M : ℕ} (X : ℕ → Ω → Fin (M + 1))
    (P : StochasticMatrix M) (ℱ : Filtration ℕ m) (μ : Measure Ω) : Prop where
  adapted : ∀ n, @Measurable _ _ (ℱ n) _ (X n)
  markov_prop : ∀ n : ℕ, ∀ j : Fin (M + 1),
    μ[(fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0) | ℱ n] =ᵐ[μ]
      fun ω => P.prob (X n ω) j

/-- The transition kernel of a stochastic matrix: `finiteChainKernel P x` is the
probability measure on `Fin (M + 1)` putting mass `P.prob x j` on each state `j`.
This is the kernel form of the transition matrix. -/
noncomputable def finiteChainKernel {M : ℕ} (P : StochasticMatrix M) :
    Kernel (Fin (M + 1)) (Fin (M + 1)) :=
  Kernel.ofFunOfCountable (fun x => ∑ j, ENNReal.ofReal (P.prob x j) • Measure.dirac j)

/-- The kernel of a stochastic matrix is a Markov kernel: each row is a
probability measure, by non-negativity and the row-sum condition. -/
instance finiteChainKernel.isMarkovKernel {M : ℕ} (P : StochasticMatrix M) :
    IsMarkovKernel (finiteChainKernel P) where
  isProbabilityMeasure x := by
    refine ⟨?_⟩
    show (∑ j, ENNReal.ofReal (P.prob x j) • Measure.dirac j) Set.univ = 1
    have hsum : (∑ j, ENNReal.ofReal (P.prob x j) • Measure.dirac j) Set.univ
        = ∑ j, ENNReal.ofReal (P.prob x j) := by
      have h := congrFun
        (Measure.coe_finsetSum Finset.univ
          (fun j => ENNReal.ofReal (P.prob x j) • Measure.dirac j)) Set.univ
      simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one] at h
      exact h
    rw [hsum, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => P.nonneg x j), P.row_sum x,
      ENNReal.ofReal_one]

/-- The kernel of a stochastic matrix evaluated at a finite set is the sum of the
transition probabilities into that set. -/
theorem finiteChainKernel_apply {M : ℕ} (P : StochasticMatrix M) (x : Fin (M + 1))
    (B : Finset (Fin (M + 1))) :
    finiteChainKernel P x ↑B = ∑ j ∈ B, ENNReal.ofReal (P.prob x j) := by
  show (∑ j, ENNReal.ofReal (P.prob x j) • Measure.dirac j) ↑B = _
  have h1 : (∑ j, ENNReal.ofReal (P.prob x j) • Measure.dirac j) ↑B
      = ∑ j, ENNReal.ofReal (P.prob x j) * (Measure.dirac j ↑B) := by
    have h := congrFun (Measure.coe_finsetSum Finset.univ
      (fun j => ENNReal.ofReal (P.prob x j) • Measure.dirac j)) ↑B
    simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at h
    exact h
  rw [h1]
  have h2 : ∀ j, Measure.dirac j ↑B = if j ∈ B then (1 : ℝ≥0∞) else 0 := by
    intro j
    rw [Measure.dirac_apply' _ (Finset.measurableSet B)]
    simp [Set.indicator_apply]
  simp_rw [h2]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Bridge: finite-state Markov chains satisfy the general one-step Markov
property.** For a finite Markov chain, the conditional expectation of the
indicator of `X (n+1) ∈ B` given `ℱ n` is the kernel of `P` evaluated at
`X n`, almost surely. This is the one-step form of `v1`'s general
`IsMarkovChain.markov_prop` specialized to the matrix kernel. No measurability
hypothesis on `B` is needed: the indicator is defined for every set, and the
proof only sums over the finite state space. -/
theorem IsFiniteMarkovChain.condExp_indicator {M : ℕ} {X : ℕ → Ω → Fin (M + 1)}
    {P : StochasticMatrix M} {ℱ : Filtration ℕ m} [IsProbabilityMeasure μ]
    (hX : IsFiniteMarkovChain X P ℱ μ) {n : ℕ} {B : Set (Fin (M + 1))} :
    μ[(B.indicator (fun _ => (1 : ℝ))) ∘ (X (n + 1)) | ℱ n] =ᵐ[μ]
      fun ω => (finiteChainKernel P (X n ω) B).toReal := by
  classical
  have hLHS : (B.indicator (fun _ => (1 : ℝ))) ∘ (X (n + 1))
      = ∑ j ∈ B, (fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0) := by
    funext ω
    simp only [Function.comp_apply, Finset.sum_apply, Set.indicator_apply]
    rw [Finset.sum_ite_eq]
    by_cases h : X (n + 1) ω ∈ B <;> simp [h, Set.mem_toFinset]
  have hInt : ∀ j ∈ B.toFinset,
      Integrable (fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0) μ := by
    intro j _
    have hXmeas : Measurable (X (n + 1)) := (hX.adapted (n + 1)).mono (ℱ.le _) le_rfl
    have hEq : (fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0)
        = (X (n + 1) ⁻¹' {j}).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      simp [Set.indicator_apply]
    rw [hEq]
    exact (integrable_const (1 : ℝ)).indicator (hXmeas (measurableSet_singleton j))
  have hRHS : ∀ ω, (finiteChainKernel P (X n ω) B).toReal
      = ∑ j ∈ B, P.prob (X n ω) j := by
    intro ω
    have hApply := finiteChainKernel_apply P (X n ω) B.toFinset
    rw [Set.coe_toFinset] at hApply
    rw [hApply, ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)]
    exact Finset.sum_congr rfl fun j _ => ENNReal.toReal_ofReal (P.nonneg _ _)
  calc μ[(B.indicator (fun _ => (1 : ℝ))) ∘ (X (n + 1)) | ℱ n]
      =ᵐ[μ] μ[∑ j ∈ B, (fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0) | ℱ n] :=
        Filter.EventuallyEq.of_eq (by rw [hLHS])
    _ =ᵐ[μ] ∑ j ∈ B, μ[(fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0) | ℱ n] :=
        condExp_finsetSum hInt (ℱ n)
    _ =ᵐ[μ] ∑ j ∈ B, (fun ω => P.prob (X n ω) j) :=
        eventuallyEq_sum (fun j _ => hX.markov_prop n j)
    _ =ᵐ[μ] fun ω => (finiteChainKernel P (X n ω) B).toReal :=
        Filter.EventuallyEq.of_eq (by
          funext ω
          rw [Finset.sum_apply]
          exact (hRHS ω).symm)

/-- Convert the finite singleton-probability specification to the canonical general
Markov-chain predicate under the probability-space hypotheses of `condExp_indicator`. -/
theorem IsFiniteMarkovChain.toIsMarkovChain {M : ℕ} {X : ℕ → Ω → Fin (M + 1)}
    {P : StochasticMatrix M} {ℱ : Filtration ℕ m} [IsProbabilityMeasure μ]
    (hX : IsFiniteMarkovChain X P ℱ μ) :
    MathlibExt.Probability.MarkovChainChapmanKolmogorov.IsMarkovChain
      X ℱ (finiteChainKernel P) μ where
  adapted := hX.adapted
  markov_prop _ _ _ := hX.condExp_indicator

/-- **One-step forward equation.** The law of `X (n+1)` is the law of `X n`
transported by the transition kernel of `P`. -/
theorem IsFiniteMarkovChain.map_succ_eq_bind {M : ℕ} {X : ℕ → Ω → Fin (M + 1)}
    {P : StochasticMatrix M} {ℱ : Filtration ℕ m} [IsProbabilityMeasure μ]
    (hX : IsFiniteMarkovChain X P ℱ μ) (n : ℕ) :
    μ.map (X (n + 1)) = (μ.map (X n)).bind (finiteChainKernel P) := by
  simpa only [pow_one] using hX.toIsMarkovChain.map_eq_bind_pow n 1

end MathlibExt.Probability.FiniteMarkovChain
