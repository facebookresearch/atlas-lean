/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SupermartingaleOptionalStopping
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

open MeasureTheory Filter

namespace MathlibExtTest.Probability.SupermartingaleOptionalStopping

/-- A constant process whose deterministic values are antitone is a
supermartingale with respect to any filtration: conditional expectations
of constants are the constants themselves. -/
theorem supermartingale_const_of_antitone {c : ℕ → ℝ} (hc : Antitone c)
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} :
    Supermartingale (fun (n : ℕ) _ => c n) ℱ μ := by
  refine ⟨fun _ => measurable_const.stronglyMeasurable, fun i j hij => ?_,
    fun _ => integrable_const _⟩
  show μ[fun _ => c j | ℱ i] ≤ᵐ[μ] fun _ => c i
  rw [condExp_const (ℱ.le i)]
  exact Filter.Eventually.of_forall fun _ => hc hij

/-- A constant process with a single deterministic value is a martingale
with respect to any filtration. -/
theorem martingale_const_process (c : ℝ)
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} :
    Martingale (fun _ _ => c) ℱ μ := by
  refine ⟨fun _ => measurable_const.stronglyMeasurable, fun i j _ => ?_⟩
  show μ[fun _ => c | ℱ i] =ᵐ[μ] fun _ => c
  rw [condExp_const (ℱ.le i)]

/-- The trivial (constant) filtration on `Unit`, used for the numeric tests. -/
noncomputable abbrev testFiltration :
    Filtration ℕ (inferInstance : MeasurableSpace Unit) :=
  ⊥

/-- The decreasing deterministic supermartingale `f n = 1 / (n + 1)` on the
Dirac space `Unit`: the stopped value at the constant stopping time `2`
has expectation at most the initial expectation. -/
theorem supermartingale_le_dirac :
    ∫ ω, stoppedValue (fun (n : ℕ) (_ : Unit) => ((n : ℝ) + 1)⁻¹)
        (fun _ => ((2 : ℕ) : WithTop ℕ)) ω ∂(Measure.dirac ()) ≤
      ∫ ω, (fun (n : ℕ) (_ : Unit) => ((n : ℝ) + 1)⁻¹) 0 ω
        ∂(Measure.dirac ()) := by
  have hsuper : Supermartingale (fun (n : ℕ) (_ : Unit) => ((n : ℝ) + 1)⁻¹)
      testFiltration (Measure.dirac ()) :=
    supermartingale_const_of_antitone (fun i j hij =>
      inv_anti₀ (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hij 1))
  exact hsuper.expected_stoppedValue_le (isStoppingTime_const _ _)
    (fun _ => le_refl _)

/-- The stopped value at `τ = 2` computed: its expectation is `1 / 3`. -/
theorem supermartingale_le_dirac_numeric :
    ∫ ω, stoppedValue (fun (n : ℕ) (_ : Unit) => ((n : ℝ) + 1)⁻¹)
        (fun _ => ((2 : ℕ) : WithTop ℕ)) ω ∂(Measure.dirac ()) = 1 / 3 := by
  have hstop : ∀ ω : Unit, stoppedValue (fun (n : ℕ) (_ : Unit) => ((n : ℝ) + 1)⁻¹)
      (fun _ => ((2 : ℕ) : WithTop ℕ)) ω = ((2 : ℝ) + 1)⁻¹ := fun _ => rfl
  simp only [hstop, integral_dirac]
  norm_num

/-- The two-stopping-time form on the decreasing supermartingale:
`E[f_2] = 1 / 3 ≤ 1 / 2 = E[f_1]`. -/
theorem supermartingale_anti_mono_dirac :
    ∫ ω, stoppedValue (fun (n : ℕ) (_ : Unit) => ((n : ℝ) + 1)⁻¹)
        (fun _ => ((2 : ℕ) : WithTop ℕ)) ω ∂(Measure.dirac ()) ≤
      ∫ ω, stoppedValue (fun (n : ℕ) (_ : Unit) => ((n : ℝ) + 1)⁻¹)
        (fun _ => ((1 : ℕ) : WithTop ℕ)) ω ∂(Measure.dirac ()) := by
  have hsuper : Supermartingale (fun (n : ℕ) (_ : Unit) => ((n : ℝ) + 1)⁻¹)
      testFiltration (Measure.dirac ()) :=
    supermartingale_const_of_antitone (fun i j hij =>
      inv_anti₀ (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hij 1))
  exact hsuper.expected_stoppedValue_anti_mono (isStoppingTime_const _ _)
    (isStoppingTime_const _ _)
    (fun _ => WithTop.coe_le_coe.mpr (show (1 : ℕ) ≤ 2 by norm_num))
    (fun _ => le_refl _)

/-- For the constant martingale `f ≡ 5`, the stopped values at the constant
stopping times `1` and `3` have equal expectations. -/
theorem martingale_eq_dirac :
    ∫ ω, stoppedValue (fun _ _ => (5 : ℝ))
        (fun _ => ((1 : ℕ) : WithTop ℕ)) ω ∂(Measure.dirac ()) =
      ∫ ω, stoppedValue (fun _ _ => (5 : ℝ))
        (fun _ => ((3 : ℕ) : WithTop ℕ)) ω ∂(Measure.dirac ()) := by
  have hmart : Martingale (fun _ _ => (5 : ℝ)) testFiltration
      (Measure.dirac ()) :=
    martingale_const_process 5
  exact hmart.expected_stoppedValue_eq (isStoppingTime_const _ _)
    (isStoppingTime_const _ _)
    (fun _ => WithTop.coe_le_coe.mpr (show (1 : ℕ) ≤ 3 by norm_num))
    (fun _ => le_refl _)

/-- The constant-martingale equality with the values computed: both sides
are `5`. -/
theorem martingale_eq_dirac_numeric :
    ∫ ω, stoppedValue (fun _ _ => (5 : ℝ))
        (fun _ => ((1 : ℕ) : WithTop ℕ)) ω ∂(Measure.dirac ()) = 5 := by
  have hstop : ∀ ω : Unit, stoppedValue (fun _ _ => (5 : ℝ))
      (fun _ => ((1 : ℕ) : WithTop ℕ)) ω = (5 : ℝ) := fun _ => rfl
  simp only [hstop, integral_dirac]

/-- For the constant martingale `f ≡ 5`, the stopped value at the constant
stopping time `2` has the same expectation as `f 0`. -/
theorem martingale_eq_zero_dirac :
    ∫ ω, stoppedValue (fun _ _ => (5 : ℝ))
        (fun _ => ((2 : ℕ) : WithTop ℕ)) ω ∂(Measure.dirac ()) =
      ∫ ω, (fun _ _ => (5 : ℝ)) 0 ω ∂(Measure.dirac ()) := by
  have hmart : Martingale (fun _ _ => (5 : ℝ)) testFiltration
      (Measure.dirac ()) :=
    martingale_const_process 5
  exact hmart.expected_stoppedValue_eq_zero (isStoppingTime_const _ _)
    (fun _ => le_refl _)

#print axioms supermartingale_le_dirac
#print axioms supermartingale_le_dirac_numeric
#print axioms supermartingale_anti_mono_dirac
#print axioms martingale_eq_dirac
#print axioms martingale_eq_dirac_numeric
#print axioms martingale_eq_zero_dirac

end MathlibExtTest.Probability.SupermartingaleOptionalStopping
