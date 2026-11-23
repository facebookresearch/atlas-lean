/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BackwardsMartingales

/-!
# Canonical backwards-martingale infrastructure

This file extends the canonical API from `BackwardsMartingales.lean` with
integrability, uniform integrability, one-step recurrence and conditional-
expectation construction. Decreasing sigma-algebras use Mathlib's standard
`Filtration ℕᵒᵈ m0`; the tail algebra is the intersection of its levels.

Representative-level strong measurability is the separate canonical
`StronglyAdapted` property. The analytic lemmas use
`MeasureTheory.IsBackwardsMartingale` without that extra representative data.
The conditional-expectation representatives satisfy both properties.

The infrastructure comes from the Lecture 29 material in
`v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean`. The existing
plural module already proves the a.e. and L1 convergence theorems; this file
adds a small API extension and composes with those proofs.
-/

@[expose] public section

open Filter

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

namespace Filtration

/-- The tail sigma-algebra of a decreasing filtration, the intersection of its levels. -/
@[reducible]
def tailAlgebra (ℱ : Filtration ℕᵒᵈ m0) : MeasurableSpace Ω := ⨅ n, ℱ n

/-- The tail sigma-algebra lies in the ambient sigma-algebra. -/
theorem tailAlgebra_le (ℱ : Filtration ℕᵒᵈ m0) : ℱ.tailAlgebra ≤ m0 :=
  le_trans (iInf_le _ 0) (ℱ.le' 0)

/-- The tail sigma-algebra lies in every level of the decreasing filtration. -/
theorem tailAlgebra_le_seq (ℱ : Filtration ℕᵒᵈ m0) (n : ℕᵒᵈ) :
    ℱ.tailAlgebra ≤ ℱ n := iInf_le _ n

/-- A constant decreasing filtration has its constant value as tail algebra. -/
theorem tailAlgebra_const (m : MeasurableSpace Ω) (hm : m ≤ m0) :
    (Filtration.const ℕᵒᵈ m hm).tailAlgebra = m := iInf_const

/-- Conditional-expectation representatives are strongly adapted separately
from their canonical backwards-martingale membership. No integrability of g is needed. -/
theorem stronglyAdapted_condExp (ℱ : Filtration ℕᵒᵈ m0) (g : Ω → ℝ) (μ : Measure Ω) :
    StronglyAdapted ℱ (fun n => μ[g | ℱ n]) := fun _ => stronglyMeasurable_condExp

end Filtration

namespace IsBackwardsMartingale

/-- Every term is integrable by its canonical conditional-expectation representation. -/
theorem integrable {M : ℕ → Ω → ℝ} {m : ℕ → MeasurableSpace Ω}
    (hM : IsBackwardsMartingale M m μ) (n : ℕ) : Integrable (M n) μ :=
  integrable_condExp.congr (hM.2 n).symm

/-- Canonical backwards membership is uniformly integrable in L1 on a finite measure.
The ambient bounds suffice; representative adaptedness and antitonicity are unnecessary. -/
theorem uniformIntegrable [IsFiniteMeasure μ]
    {M : ℕ → Ω → ℝ} {m : ℕ → MeasurableSpace Ω}
    (hM : IsBackwardsMartingale M m μ) (hm0 : ∀ n, m n ≤ m0) :
    UniformIntegrable M 1 μ :=
  (hM.1.uniformIntegrable_condExp hm0).ae_eq (fun n => (hM.2 n).symm)

/-- Conditioning a term on the next, smaller level gives the next term a.e. -/
theorem condExp_succ_ae_eq [IsFiniteMeasure μ]
    {M : ℕ → Ω → ℝ} {m : ℕ → MeasurableSpace Ω}
    (hM : IsBackwardsMartingale M m μ) (hm : Antitone m)
    (hm0 : ∀ n, m n ≤ m0) (n : ℕ) : μ[M n | m (n + 1)] =ᵐ[μ] M (n + 1) := by
  calc μ[M n | m (n + 1)]
      =ᵐ[μ] μ[μ[M 0 | m n] | m (n + 1)] := condExp_congr_ae (hM.2 n)
    _ =ᵐ[μ] μ[M 0 | m (n + 1)] :=
      condExp_condExp_of_le (hm (Nat.le_succ n)) (hm0 n)
    _ =ᵐ[μ] M (n + 1) := (hM.2 (n + 1)).symm

end IsBackwardsMartingale

/-- Conditional expectations of arbitrary g form a canonical backwards martingale
along decreasing sub-sigma-algebras. The nonintegrable-g convention is retained. -/
theorem isBackwardsMartingale_condExp [IsFiniteMeasure μ] (g : Ω → ℝ)
    (m : ℕ → MeasurableSpace Ω) (hm : Antitone m) (hm0 : ∀ n, m n ≤ m0) :
    IsBackwardsMartingale (fun n => μ[g | m n]) m μ := by
  refine ⟨integrable_condExp, fun n => ?_⟩
  exact (condExp_condExp_of_le (hm (Nat.zero_le n)) (hm0 0)).symm

end MeasureTheory
