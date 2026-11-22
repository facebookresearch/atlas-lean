/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConditionalOptionalStopping

/-!
# Conditional optional stopping tests

The clients cover UI only after stopping, migration from whole-process UI,
and finite and infinite stopping values.
-/

@[expose] public section

open MeasureTheory Filter

open scoped Topology

namespace MathlibExtTest.Probability.ConditionalOptionalStopping

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} [SigmaFiniteFiltration μ ℱ] {f : ℕ → Ω → ℝ}

/-- The stopped value of a constant process at the infinite stopping time
is the constant, pointwise. -/
example (c : ℝ) :
    stoppedValueAtTop (fun _ _ => c) (fun _ : Ω => (⊤ : WithTop ℕ)) = fun _ => c := by
  funext ω
  show (if (⊤ : WithTop ℕ) = ⊤ then limUnder atTop (fun n : ℕ => c)
      else stoppedValue (fun _ _ => c) (fun _ => (⊤ : WithTop ℕ)) ω) = c
  rw [ite_eq_left rfl]
  exact tendsto_const_nhds.limUnder_eq

/-- The stopped value of a constant process at a finite constant stopping
time is the constant, pointwise. -/
example (c : ℝ) :
    stoppedValueAtTop (fun _ _ => c) (fun _ : Ω => ((5 : ℕ) : WithTop ℕ))
      = fun _ => c := by
  funext ω
  show (if ((5 : ℕ) : WithTop ℕ) = ⊤ then limUnder atTop (fun n : ℕ => c)
      else stoppedValue (fun (_ : ℕ) (_ : Ω) => c) (fun _ => ((5 : ℕ) : WithTop ℕ)) ω) = c
  rw [ite_eq_right (by simp)]
  rfl

/-- Restatement of the key lemma: the stopped value at an arbitrary
stopping time is the conditional expectation of the `L¹` limit. -/
example (hf : Martingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    stoppedValueAtTop f τ =ᵐ[μ] μ[ℱ.limitProcess f μ | hτ.measurableSpace] :=
  MeasureTheory.Martingale.stoppedValueAtTop_ae_eq_condExp_limitProcess hf hui hτ

/-- Whole-process UI callers explicitly use the existing UI preservation API. -/
example (hf : Martingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    stoppedValueAtTop f L
      =ᵐ[μ] μ[stoppedValueAtTop f M | hL.measurableSpace] :=
  MeasureTheory.Martingale.stoppedValueAtTop_ae_eq_condExp_stoppedValueAtTop
    hf (hf.uniformIntegrable_stoppedProcess_of_uniformIntegrable hui M hM) hL hM hLM

/-- A direct client assumes only UI of the process stopped at `M`. -/
example (hf : Martingale f ℱ μ) {L M : Ω → WithTop ℕ}
    (hui : UniformIntegrable (stoppedProcess f M) 1 μ)
    (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M) (hLM : L ≤ M) :
    stoppedValueAtTop f L
      =ᵐ[μ] μ[stoppedValueAtTop f M | hL.measurableSpace] :=
  hf.stoppedValueAtTop_ae_eq_condExp_stoppedValueAtTop hui hL hM hLM

/-- Stopping any martingale at zero supplies UI without a whole-process UI premise. -/
example (hf : Martingale f ℱ μ) :
    stoppedValueAtTop f (fun _ : Ω => ((0 : ℕ) : WithTop ℕ))
      =ᵐ[μ] μ[stoppedValueAtTop f (fun _ : Ω => ((0 : ℕ) : WithTop ℕ)) |
        (isStoppingTime_const ℱ 0).measurableSpace] := by
  have hui : UniformIntegrable
      (stoppedProcess f (fun _ : Ω => ((0 : ℕ) : WithTop ℕ))) 1 μ := by
    have hzero : stoppedProcess f (fun _ : Ω => ((0 : ℕ) : WithTop ℕ))
        = fun _ : ℕ => f 0 := by
      funext n ω
      exact stoppedProcess_eq_of_ge (WithTop.coe_le_coe.mpr (Nat.zero_le n))
    rw [hzero]
    exact uniformIntegrable_const (ι := ℕ) le_rfl ENNReal.one_ne_top
      (memLp_one_iff_integrable.mpr (hf.integrable 0))
  exact hf.stoppedValueAtTop_ae_eq_condExp_stoppedValueAtTop hui
    (isStoppingTime_const ℱ 0) (isStoppingTime_const ℱ 0) le_rfl

/-- The constant martingale: conditional optional stopping holds for the
constant stopping times `0 ≤ 5`, with both stopped values the constant. -/
example (c : ℝ) :
    let ℱ₀ : Filtration ℕ Real.measurableSpace :=
      ⟨fun _ => ⊥, fun _ _ _ => bot_le, fun _ => bot_le⟩
    let μ₀ : MeasureTheory.Measure ℝ := MeasureTheory.Measure.dirac 0
    stoppedValueAtTop (fun _ _ => c) (fun _ : ℝ => ((0 : ℕ) : WithTop ℕ))
      =ᵐ[μ₀] μ₀[stoppedValueAtTop (fun _ _ => c)
          (fun _ : ℝ => ((5 : ℕ) : WithTop ℕ)) |
        (isStoppingTime_const ℱ₀ 0).measurableSpace] := by
  intro ℱ₀ μ₀
  refine MeasureTheory.Martingale.stoppedValueAtTop_ae_eq_condExp_stoppedValueAtTop
    (martingale_const ℱ₀ μ₀ c)
    (by simpa only [stoppedProcess_const] using
      uniformIntegrable_const (ι := ℕ) le_rfl ENNReal.one_ne_top (memLp_const c))
    (isStoppingTime_const ℱ₀ 0) (isStoppingTime_const ℱ₀ 5)
    (fun ω => by simp)

-- Axiom check for the two main results: only the standard axioms.
#print axioms MeasureTheory.Martingale.stoppedValueAtTop_ae_eq_condExp_limitProcess
#print axioms MeasureTheory.Martingale.stoppedValueAtTop_ae_eq_condExp_stoppedValueAtTop

-- The conditional theorem also handles an actual infinite terminal stopping time.
example :
    let ℱ₀ : Filtration ℕ Real.measurableSpace :=
      ⟨fun _ => ⊥, fun _ _ _ => bot_le, fun _ => bot_le⟩
    let μ₀ : MeasureTheory.Measure ℝ := MeasureTheory.Measure.dirac 0
    stoppedValueAtTop (fun _ _ => (3 : ℝ)) (fun _ : ℝ => ((0 : ℕ) : WithTop ℕ))
      =ᵐ[μ₀] μ₀[stoppedValueAtTop (fun _ _ => (3 : ℝ))
          (fun _ : ℝ => (⊤ : WithTop ℕ)) |
        (isStoppingTime_const ℱ₀ 0).measurableSpace] := by
  intro ℱ₀ μ₀
  have htop : IsStoppingTime ℱ₀ (fun _ : ℝ => (⊤ : WithTop ℕ)) := by
    intro i
    simp
  exact MeasureTheory.Martingale.stoppedValueAtTop_ae_eq_condExp_stoppedValueAtTop
    (martingale_const ℱ₀ μ₀ (3 : ℝ))
    (by simpa only [stoppedProcess_const] using
      uniformIntegrable_const (ι := ℕ) le_rfl ENNReal.one_ne_top (memLp_const (3 : ℝ)))
    (isStoppingTime_const ℱ₀ 0) htop (fun _ => le_top)

/-- Finite stopped-value identification for an arbitrary process. -/
example :
    stoppedValueAtTop (stoppedProcess f (fun _ : Ω => ((5 : ℕ) : WithTop ℕ)))
        (fun _ : Ω => ((2 : ℕ) : WithTop ℕ))
      = stoppedValueAtTop f (fun _ : Ω => ((2 : ℕ) : WithTop ℕ)) :=
  stoppedValueAtTop_stoppedProcess_of_le (fun _ => by norm_num)

/-- Both stopping times may be infinite; the identity needs no convergence assumption. -/
example :
    stoppedValueAtTop (stoppedProcess f (fun _ : Ω => (⊤ : WithTop ℕ)))
        (fun _ : Ω => (⊤ : WithTop ℕ))
      = stoppedValueAtTop f (fun _ : Ω => (⊤ : WithTop ℕ)) :=
  stoppedValueAtTop_stoppedProcess_of_le le_rfl

#check MeasureTheory.Martingale.stoppedValueAtTop_ae_eq_condExp_stoppedValueAtTop
#print axioms MeasureTheory.stoppedValueAtTop_stoppedProcess_of_le

#print axioms MeasureTheory.stoppedValueAtTop
#print axioms MeasureTheory.IsStoppingTime.stoppedFiltration
#print axioms MeasureTheory.IsStoppingTime.stoppedFiltration_apply
#print axioms MeasureTheory.IsStoppingTime.measurableSet_eq_top_iSup_stoppedFiltration
#print axioms MeasureTheory.IsStoppingTime.measurableSet_inter_eq_top_iSup_stoppedFiltration
#print axioms MeasureTheory.IsStoppingTime.iSup_stoppedFiltration

end MathlibExtTest.Probability.ConditionalOptionalStopping
