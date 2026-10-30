/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainFDD
public import Mathlib.Probability.Kernel.Basic

/-!
# Tests for Markov chain finite-dimensional distributions

Concrete checks on `MathlibExt.Probability.MarkovChainFDD`: the `n = 0`
and `n = 1` cases of `markovFDD`, measurability of `markovFDD` in the
starting state, and an end-to-end instance — the constant chain
`Xₙ = X₀` with the Dirac transition kernel `Kernel.id`, which satisfies
the Markov hypothesis of `markov_chain_finite_dimensional_distributions`.
For the constant chain at `n = 1` this pins down the value
`P(X₀ ∈ A₀ ∧ X₀ ∈ A₁) = (P ∘ X₀⁻¹)(A₀ ∩ A₁)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory ENNReal Set
open MathlibExt.Probability.MarkovChainFDD

namespace MathlibExtTest.Probability.MarkovChainFDD

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- `markovFDD` at `n = 0` is the initial distribution applied to `A 0`. -/
theorem markovFDD_zero (μ : Measure S) (κ : Kernel S S) (A : Fin 1 → Set S) :
    markovFDD μ κ 0 A = μ (A 0) :=
  rfl

/-- `markovFDD` at `n = 1` is a single integral against the transition kernel. -/
theorem markovFDD_one (μ : Measure S) (κ : Kernel S S) (A : Fin 2 → Set S) :
    markovFDD μ κ 1 A = ∫⁻ x in A 0, κ x (A 1) ∂μ := by
  simp [markovFDD]

/-- Measurability of `markovFDD` in the starting state, for the Dirac kernel. -/
theorem markovFDD_measurable_id (n : ℕ) (A : Fin (n + 1) → Set S)
    (hA : ∀ i, MeasurableSet (A i)) :
    Measurable (fun x => markovFDD ((Kernel.id : Kernel S S) x) (Kernel.id : Kernel S S) n A) :=
  markovFDD_measurable Kernel.id n A hA

section ConstantChain

variable {P : Measure Ω} {X₀ : Ω → S}

/-- The constant chain `Xₙ = X₀` satisfies the Markov hypothesis with the
Dirac transition kernel `Kernel.id`: the next state is almost surely the
current state. -/
theorem markov_const_chain :
    ∀ (k : ℕ) (B : Set S), MeasurableSet B →
      ∀ (C : Set Ω),
        @MeasurableSet Ω (MeasurableSpace.comap
          (fun omega => fun i : Fin (k + 1) => (fun _ => X₀) i omega)
            MeasurableSpace.pi) C →
        ∫⁻ omega in C, ((fun _ => X₀) (k + 1) ⁻¹' B).indicator
            (fun _ => (1 : ENNReal)) omega ∂P =
        ∫⁻ omega in C, (Kernel.id : Kernel S S) ((fun _ => X₀) k omega) B ∂P := by
  intro k B hB C _
  have hfun : ∀ ω, ((fun _ => X₀) (k + 1) ⁻¹' B).indicator
        (fun _ => (1 : ENNReal)) ω = (Kernel.id : Kernel S S) ((fun _ => X₀) k ω) B := by
    intro ω
    show (X₀ ⁻¹' B).indicator (fun _ => (1 : ENNReal)) ω =
      (Kernel.id : Kernel S S) (X₀ ω) B
    by_cases h : X₀ ω ∈ B
    · have hω : ω ∈ X₀ ⁻¹' B := h
      simp [Kernel.id_apply, Measure.dirac_apply' _ hB, Set.indicator_of_mem hω,
        Set.indicator_of_mem h]
    · have hω : ω ∉ X₀ ⁻¹' B := fun hh => h hh
      simp [Kernel.id_apply, Measure.dirac_apply' _ hB, Set.indicator_of_notMem hω,
        Set.indicator_of_notMem h]
  exact lintegral_congr fun ω => hfun ω

/-- Finite-dimensional distributions of the constant chain. -/
theorem fdd_const_chain [IsProbabilityMeasure P] (hX₀ : Measurable X₀) (n : ℕ) (A : Fin (n + 1) → Set S)
    (hA : ∀ i, MeasurableSet (A i)) :
    P (⋂ i : Fin (n + 1), (fun _ => X₀) i ⁻¹' A i) =
      markovFDD (P.map X₀) (Kernel.id : Kernel S S) n A :=
  markov_chain_finite_dimensional_distributions P (fun _ => X₀) (fun _ => hX₀)
    (Kernel.id : Kernel S S) n A hA markov_const_chain

/-- The `n = 1` case of the constant chain: `P(X₀ ∈ A₀ ∧ X₀ ∈ A₁)` is the
initial law of `A₀ ∩ A₁`. -/
theorem fdd_const_chain_one [IsProbabilityMeasure P] (hX₀ : Measurable X₀) (A : Fin 2 → Set S)
    (hA : ∀ i, MeasurableSet (A i)) :
    P (X₀ ⁻¹' A 0 ∩ X₀ ⁻¹' A 1) = (P.map X₀) (A 0 ∩ A 1) := by
  have h1 : P (⋂ i : Fin 2, (fun _ => X₀) i ⁻¹' A i) =
      markovFDD (P.map X₀) (Kernel.id : Kernel S S) 1 A :=
    fdd_const_chain hX₀ 1 A hA
  have hInter : ⋂ i : Fin 2, (fun _ => X₀) i ⁻¹' A i = X₀ ⁻¹' (A 0 ∩ A 1) := by
    ext ω
    simp [Fin.forall_fin_two, Set.mem_inter_iff]
  rw [hInter, markovFDD_one] at h1
  have hInt : ∫⁻ x in A 0, (Kernel.id : Kernel S S) x (A 1) ∂(P.map X₀) = (P.map X₀) (A 0 ∩ A 1) := by
    have hfun : ∀ x, (Kernel.id : Kernel S S) x (A 1) = (A 1).indicator 1 x := by
      intro x
      simp [Kernel.id_apply, Measure.dirac_apply' _ (hA 1)]
    rw [setLIntegral_congr_fun (hA 0) (fun x _ => hfun x),
      setLIntegral_indicator (hA 1) (1 : S → ENNReal)]
    show ∫⁻ _ in A 1 ∩ A 0, (1 : ENNReal) ∂(P.map X₀) = (P.map X₀) (A 0 ∩ A 1)
    rw [setLIntegral_const, one_mul, Set.inter_comm (A 1) (A 0)]
  rw [hInt] at h1
  rw [← Set.preimage_inter]
  exact h1

end ConstantChain

end MathlibExtTest.Probability.MarkovChainFDD
