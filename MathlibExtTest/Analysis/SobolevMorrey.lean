/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SobolevMorrey
import Mathlib.Tactic.NormNum

/-! # Tests for the Sobolev embedding in the Morrey regime -/

namespace MathlibExtTest.SobolevMorrey

open MathlibExt.Analysis.SobolevMorreyWanted.Analysis.SobolevMorreyProblem
open MeasureTheory
open scoped ENNReal

private noncomputable def pointValue (x : E 1) : ℝ := if x = 0 then 1 else 0

private theorem pointValue_ae_zero : pointValue =ᵐ[volume] 0 := by
  filter_upwards [volume.ae_ne (0 : E 1)] with x hx
  simp [pointValue, hx]

private theorem pointValue_memSobolev (k : ℕ) :
    MemSobolevWk k (ENNReal.ofReal 2) pointValue := by
  refine ⟨(locallyIntegrable_const 0).congr pointValue_ae_zero.symm, fun m _ => ⟨0, ?_, by simp⟩⟩
  intro φ _ _
  have h := integral_congr_ae
    (pointValue_ae_zero.mono fun x hx => congrArg (· * mixedDeriv m φ x) hx)
  simpa using h

-- The first-order embedding allows the input to differ pointwise from its representative.
example : ∃ g : E 1 → ℝ, pointValue =ᵐ[volume] g ∧ MemHolder 0 (1 / 4) g := by
  exact sobolev_embedding (p := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    pointValue (pointValue_memSobolev 1)

-- An extra weak derivative allows exponent one. The continuous representative vanishes at zero.
example : ∃ g : E 1 → ℝ, pointValue =ᵐ[volume] g ∧ MemHolder 1 1 g ∧ g 0 = 0 := by
  obtain ⟨g, hae, hg⟩ := sobolev_embedding (r := 1) (α := 1) (p := 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) pointValue (pointValue_memSobolev 3)
  have hg0 : g = 0 :=
    (hg.1.continuous.ae_eq_iff_eq volume continuous_zero).mp (hae.symm.trans pointValue_ae_zero)
  exact ⟨g, hae, hg, congrFun hg0 0⟩

-- Dimension zero admits positive p below one and nonzero constant functions.
example : ∃ g : E 0 → ℝ, (fun _ : E 0 => (3 : ℝ)) =ᵐ[volume] g ∧ MemHolder 1 (1 / 2) g := by
  let : IsFiniteMeasure (volume : Measure (E 0)) := ⟨isCompact_univ.measure_lt_top⟩
  have hf : MemSobolevWk 2 (ENNReal.ofReal (1 / 2)) (fun _ : E 0 => (3 : ℝ)) := by
    refine ⟨locallyIntegrable_const _, fun m _ => ⟨fun _ => 3, ?_, memLp_const _⟩⟩
    rw [show m = 0 from funext (fun i => Fin.elim0 i)]
    intro φ _ _
    simp [mixedDeriv]
  exact sobolev_embedding (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ hf

end MathlibExtTest.SobolevMorrey
