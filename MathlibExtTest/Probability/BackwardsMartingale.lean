/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BackwardsMartingale

@[expose] public section

open MeasureTheory Filter

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- The tail σ-algebra of a decreasing filtration lies below the ambient σ-algebra
and below every component. -/
example (ℱ : Filtration ℕᵒᵈ m0) (n : ℕ) :
    ℱ.tailAlgebra ≤ m0 ∧ ℱ.tailAlgebra ≤ ℱ.seq n :=
  ⟨ℱ.tailAlgebra_le, ℱ.tailAlgebra_le_seq n⟩

/-- The tail σ-algebra of the constant filtration is the filtration's value. -/
example (m : MeasurableSpace Ω) (hm : m ≤ m0) :
    (Filtration.const ℕᵒᵈ m hm).tailAlgebra = m :=
  Filtration.tailAlgebra_const m hm

/-- The conditional-expectation process along a decreasing filtration is a
backwards martingale, hence integrable, uniformly integrable, and satisfying the
one-step recurrence. -/
example (g : Ω → ℝ) (ℱ : Filtration ℕᵒᵈ m0) [IsFiniteMeasure μ]
    (n : ℕ) :
    Integrable (μ[g | ℱ.seq n]) μ ∧
      UniformIntegrable (fun n => μ[g | ℱ.seq n]) 1 μ ∧
      μ[μ[g | ℱ.seq n] | ℱ.seq (n + 1 : ℕ)] =ᵐ[μ] μ[g | ℱ.seq (n + 1 : ℕ)] := by
  have hm : Antitone (fun n : ℕ => ℱ n) := by
    intro i j hij
    exact ℱ.mono' hij
  have hM : IsBackwardsMartingale (fun n => μ[g | ℱ.seq n]) ℱ.seq μ :=
    isBackwardsMartingale_condExp g ℱ.seq hm ℱ.le'
  exact ⟨hM.integrable n, hM.uniformIntegrable ℱ.le', hM.condExp_succ_ae_eq hm ℱ.le' n⟩

/-- For the constant filtration, every term of the conditional-expectation
backwards martingale equals the `n = 0` term, since all components coincide. -/
example (g : Ω → ℝ) (m : MeasurableSpace Ω) (hm : m ≤ m0) (n : ℕ) :
    μ[g | (Filtration.const ℕᵒᵈ m hm).seq n] = μ[g | m] := rfl

#print axioms IsBackwardsMartingale.integrable
#print axioms IsBackwardsMartingale.uniformIntegrable
#print axioms IsBackwardsMartingale.condExp_succ_ae_eq
#print axioms isBackwardsMartingale_condExp
