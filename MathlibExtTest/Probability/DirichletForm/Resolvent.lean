/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.DirichletForm.Resolvent
import MathlibExtTest.Probability.DirichletForm.Basic

/-!
# Tests for the Beurling–Deny resolvent criterion

The inner-product form has resolvent equation (1 + α)u = f. A zero form on the full domain
has αu = f, so its scaled resolvent attains the unit interval bounds.
-/

open MeasureTheory
open scoped RealInnerProductSpace
open MathlibExt.Probability.DirichletForm MathlibExt.Probability.DirichletFormWanted
open MathlibExtTest.Probability.DirichletForm.Basic

namespace MathlibExtTest.Probability.DirichletForm.Resolvent

variable {X : Type*} [MeasurableSpace X] {m : Measure X} [SigmaFinite m]

example (a : ℝ) (ha : 0 < a) (u : Lp ℝ 2 m)
    (hf : ∀ᵐ t ∂m, 0 ≤ ((1 + a) • u : Lp ℝ 2 m) t ∧ ((1 + a) • u : Lp ℝ 2 m) t ≤ 1) :
    ∀ᵐ t ∂m, 0 ≤ a * u t ∧ a * u t ≤ 1 := by
  apply (unitContractionOperates_iff_resolvent (innerForm m) (innerForm_isClosed m)).mp
    (innerForm_unitContractionOperates m) a ha ((1 + a) • u) u Submodule.mem_top _ hf
  intro v _
  rw [innerForm_form, real_inner_smul_left, add_mul, one_mul]

example (E : SymmetricForm m) (hE : E.IsClosed) (hdom : E.domain = ⊤) (hzero : E.form = 0) :
    E.UnitContractionOperates := by
  apply (unitContractionOperates_iff_resolvent E hE).mpr
  intro a _ f u _ heq hf
  have he : a • u = f := by
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    have h := heq (a • u - f) (by simp [hdom])
    rw [inner_sub_left, real_inner_smul_left, sub_eq_zero]
    simpa [hzero] using h
  filter_upwards [hf, Lp.coeFn_smul a u] with t ht hs
  rw [he] at hs
  simpa only [hs, Pi.smul_apply, smul_eq_mul] using ht

end MathlibExtTest.Probability.DirichletForm.Resolvent
