/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Markov chain construction

Given a Markov transition kernel `κ : S → S` and an initial
distribution `μ` on a standard Borel space `S`, there is a probability
measure `P` on path space `ℕ → S` such that the coordinate process
`(X₀, X₁, …)` sampled from `P` is a Markov chain with initial
distribution `μ` and transition kernel `κ`: the law of `X₀` is `μ`,
and for every `n` the conditional law of `X_{n+1}` given the history
`(X₀, …, Xₙ)` is `κ` applied to the current state `Xₙ`.

## Source

This formalizes the target "Theorem (Markov chain construction)"
(Lecture 30/31) of `v1/Atlas/TheoryOfProbability/targets.yaml`:
"`(X₀, X₁, …)` chosen from `P_μ` is a Markov chain." Its v1
formalization is `v1/Atlas/TheoryOfProbability/code/MarkovChainConstruction.lean`
(`markov_chain_construction`, fully proved in v1), ported
here with no statement change.

## Relation to Mathlib

Mathlib has the Ionescu–Tulcea trajectory measure
(`Kernel.trajMeasure`) and its conditional distributions
(`Kernel.condDistrib_trajMeasure`), but no packaged Markov-chain
existence theorem: a search for `markovChainMeasure` /
`markov_chain_construction` in Mathlib finds nothing. This file is
that packaging: the lifted kernel, the canonical path-space measure,
its initial distribution, its conditional distributions, and the
existence theorem assembling them. The companion target "Theorem
(Markov chain finite dimensional distributions)" was ported in an
earlier batch (`MathlibExt.Probability.MarkovChainFDD`), which
explicitly left this construction for a follow-up.

## Main results

* `MathlibExt.Probability.MarkovChainConstruction.markovLiftKernel`:
  the kernel `κ` lifted to finite histories, reading off the last
  coordinate.
* `MathlibExt.Probability.MarkovChainConstruction.markovChainMeasure`:
  the canonical measure `P_μ` on path space `ℕ → S`.
* `MathlibExt.Probability.MarkovChainConstruction.markovChainMeasure_initial_distribution`:
  under `P_μ`, the law of `X₀` is `μ`.
* `MathlibExt.Probability.MarkovChainConstruction.markovChainMeasure_condDistrib`:
  under `P_μ`, the conditional law of `X_{n+1}` given the history
  `(X₀, …, Xₙ)` is the lifted transition kernel.
* `MathlibExt.Probability.MarkovChainConstruction.markov_chain_construction`:
  the book's existence theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Kernel Set

namespace MathlibExt.Probability.MarkovChainConstruction

variable {S : Type*} [MeasurableSpace S]

section LiftKernel

/-- Lift the Markov kernel `κ : S → S` to a kernel on tuples `(x₀, …, xₙ)` by reading off the
last coordinate `xₙ` and applying `κ`. This is the form required by the Ionescu–Tulcea trajectory
construction. -/
noncomputable def markovLiftKernel (κ : Kernel S S) (n : ℕ) :
    Kernel ((i : ↥(Finset.Iic n)) → S) S :=
  κ.comap (fun x => x ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

/-- The lifted kernel `markovLiftKernel κ n` is again a Markov kernel whenever `κ` is. -/
instance markovLiftKernel.instIsMarkovKernel (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (markovLiftKernel κ n) := by
  unfold markovLiftKernel; infer_instance

end LiftKernel

section CanonicalMeasure

variable (κ : Kernel S S) [IsMarkovKernel κ] (μ : Measure S) [IsProbabilityMeasure μ]

/-- The canonical measure `P_μ` on path space `ℕ → S` of the Markov chain with initial
distribution `μ` and transition kernel `κ`, built via the Ionescu–Tulcea trajectory measure. -/
noncomputable def markovChainMeasure : Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ : ℕ => S) μ (markovLiftKernel κ)

/-- `markovChainMeasure κ μ` is a probability measure on path space. -/
instance markovChainMeasure.isProbabilityMeasure :
    IsProbabilityMeasure (markovChainMeasure κ μ) := by
  unfold markovChainMeasure; infer_instance

omit [IsProbabilityMeasure μ] in
/-- Under the canonical Markov-chain measure, the law of the initial state `ω 0` is the initial
distribution `μ`. -/
theorem markovChainMeasure_initial_distribution :
    Measure.map (fun (ω : ℕ → S) => ω 0) (markovChainMeasure κ μ) = μ := by
  have h_decomp : (fun (f : ℕ → S) => f 0) =
    (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic (0 : ℕ)) => S)) ∘
    (Preorder.frestrictLe 0) := by ext ω; rfl
  rw [h_decomp,
    ← Measure.map_map
      (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic (0 : ℕ)) => S)).measurable
      (Preorder.measurable_frestrictLe 0)]
  unfold markovChainMeasure trajMeasure
  rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
    traj_map_frestrictLe, partialTraj_self, MeasureTheory.Measure.id_comp]
  rw [Measure.map_map
    (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic (0 : ℕ)) => S)).measurable
    (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic (0 : ℕ)) => S)).symm.measurable,
    MeasurableEquiv.self_comp_symm, Measure.map_id]

/-- Under the canonical Markov-chain measure, the regular conditional distribution of the next
state `X_{n+1}` given the history `(X₀, …, Xₙ)` agrees almost everywhere with the lifted
transition kernel `markovLiftKernel κ n`. This is the defining Markov property. -/
theorem markovChainMeasure_condDistrib (n : ℕ)
    [StandardBorelSpace S] [Nonempty S] :
    condDistrib (fun (x : ℕ → S) => x (n + 1)) (Preorder.frestrictLe n)
      (markovChainMeasure κ μ)
      =ᵐ[Measure.map (Preorder.frestrictLe n) (markovChainMeasure κ μ)]
        markovLiftKernel κ n := by
  exact Kernel.condDistrib_trajMeasure

end CanonicalMeasure

section ExistenceTheorem

/-- **Markov chain construction theorem.**

Given a Markov transition kernel `κ : S → S` and an initial distribution `μ` on a standard Borel
space `S`, there exists a probability measure `P` on path space `ℕ → S` such that
* the law of `ω 0` under `P` is `μ`, and
* for every `n`, the conditional law of `ω (n+1)` given the past `(ω 0, …, ω n)` is the
  transition kernel `κ` applied to the current state.

That is, the sequence `(X₀, X₁, …)` sampled from `P` is a Markov chain with initial distribution
`μ` and transitions `κ`. -/
theorem markov_chain_construction
    (κ : Kernel S S) [IsMarkovKernel κ]
    (μ : Measure S) [IsProbabilityMeasure μ]
    [StandardBorelSpace S] [Nonempty S] :
    ∃ (P : Measure (ℕ → S)) (_ : IsProbabilityMeasure P),
      P.map (fun (ω : ℕ → S) => ω 0) = μ ∧
      ∀ n : ℕ,
        condDistrib (fun (x : ℕ → S) => x (n + 1)) (Preorder.frestrictLe n) P
          =ᵐ[Measure.map (Preorder.frestrictLe n) P] markovLiftKernel κ n :=
  ⟨markovChainMeasure κ μ, markovChainMeasure.isProbabilityMeasure κ μ,
    markovChainMeasure_initial_distribution κ μ,
    fun n => markovChainMeasure_condDistrib κ μ n⟩

end ExistenceTheorem

end MathlibExt.Probability.MarkovChainConstruction
