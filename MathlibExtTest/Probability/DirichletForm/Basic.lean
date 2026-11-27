/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletForm.QuasiRegular

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Tests for symmetric forms and Dirichlet forms on `L²`

The `L²` inner product itself, with domain all of `L²(X; m)`, is a Dirichlet form for every
measure `m`: it is closed because `L²` is complete, and Markovian because the unit contraction
does not increase the `L²` norm. Hence it is closable, and the constant nest makes `∅` exceptional
and continuous functions quasi-continuous for it. This shows that the hypotheses of the
definitions are jointly satisfiable by a nonzero form.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
open MathlibExt.Probability.DirichletForm

namespace MathlibExtTest.Probability.DirichletForm.Basic

variable {X : Type*} [MeasurableSpace X]

/-- The `L²` inner product as a symmetric form with full domain. -/
noncomputable def innerForm (m : Measure X) : SymmetricForm m where
  domain := ⊤
  dense := by simp
  form := innerₗ (Lp ℝ 2 m)
  symm := fun u _ v _ => by
    rw [innerₗ, innerₛₗ_apply_apply, innerₛₗ_apply_apply, real_inner_comm]
  nonneg := fun u _ => by rw [innerₗ, innerₛₗ_apply_apply]; exact real_inner_self_nonneg

theorem innerForm_form (m : Measure X) (u v : Lp ℝ 2 m) : (innerForm m).form u v = ⟪u, v⟫ :=
  innerₛₗ_apply_apply ℝ u v

theorem innerForm_energyOne (m : Measure X) (w : Lp ℝ 2 m) :
    (innerForm m).energyOne w w = 2 * ‖w‖ ^ 2 := by
  rw [SymmetricForm.energyOne, innerForm_form, real_inner_self_eq_norm_sq]
  ring

theorem innerForm_isClosed (m : Measure X) : (innerForm m).IsClosed := by
  intro u _ hcau
  have hc : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcau (ε ^ 2) (by positivity)
    refine ⟨N, fun n hn k hk => ?_⟩
    have h := hN n hn k hk
    rw [innerForm_energyOne, dist_eq_norm] at *
    have h0 : 0 ≤ ‖u n - u k‖ := norm_nonneg _
    nlinarith
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨w, Submodule.mem_top, ?_⟩
  have h := (tendsto_iff_norm_sub_tendsto_zero.mp hw).pow 2 |>.const_mul 2
  simpa [innerForm_energyOne] using h

theorem innerForm_unitContractionOperates (m : Measure X) :
    (innerForm m).UnitContractionOperates := by
  intro u _
  refine ⟨Submodule.mem_top, ?_⟩
  rw [innerForm_form, innerForm_form, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have := norm_unitContractionLp_le u
  have h0 := norm_nonneg (unitContractionLp u)
  nlinarith

theorem innerForm_isDirichletForm (m : Measure X) : (innerForm m).IsDirichletForm :=
  ⟨innerForm_isClosed m, innerForm_unitContractionOperates m⟩

example (m : Measure X) : (innerForm m).IsClosable :=
  SymmetricForm.isClosable_of_isClosed _ (innerForm_isClosed m)

example [TopologicalSpace X] (m : Measure X) : (innerForm m).IsExceptional (∅ : Set X) :=
  (innerForm m).isExceptional_empty

example [TopologicalSpace X] (m : Measure X) {f : X → ℝ} (hf : Continuous f) :
    (innerForm m).IsQuasiContinuous f :=
  SymmetricForm.isQuasiContinuous_of_continuous _ hf

end MathlibExtTest.Probability.DirichletForm.Basic
