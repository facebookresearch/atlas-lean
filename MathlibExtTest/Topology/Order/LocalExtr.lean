/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Order.LocalExtr
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

open Filter Topology

/-- A two-level integer-valued function on the nonisolated complex plane. -/
private noncomputable def complexStep (z : ℂ) : ℤ := by
  classical
  exact if z = 0 then 0 else 1

/-- Every distinct complex input has strictly larger value than the origin. -/
private theorem complexStep_strictMin : IsStrictLocalMin complexStep 0 := by
  classical
  show ∀ᶠ z in 𝓝[≠] (0 : ℂ), complexStep 0 < complexStep z
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  simp [complexStep, hz0]

/-- The generic bridge works for a complex domain and an integer codomain. -/
example : IsLocalMin complexStep 0 := complexStep_strictMin.isLocalMin

/-- Generic negation changes the integer-valued strict minimum to a maximum. -/
example : IsStrictLocalMax (fun z => -complexStep z) 0 := complexStep_strictMin.neg

example : IsLocalMax (fun z => -complexStep z) 0 :=
  complexStep_strictMin.neg.isLocalMax

example : IsStrictLocalMin complexStep 0 := by
  simpa only [neg_neg] using complexStep_strictMin.neg.neg

/-- This complex-domain test does not rely on an empty punctured neighborhood. -/
example : (𝓝[≠] (0 : ℂ)).NeBot := inferInstance

example : complexStep 0 = 0 ∧ complexStep 1 = 1 := by
  classical
  norm_num [complexStep]

/-- The generalized minimum predicate recovers the original real definition. -/
example (f : ℝ → ℝ) (a : ℝ) :
    IsStrictLocalMin f a ↔ ∀ᶠ x in 𝓝[≠] a, f a < f x := Iff.rfl

/-- The generalized maximum predicate recovers the original real definition. -/
example (f : ℝ → ℝ) (a : ℝ) :
    IsStrictLocalMax f a ↔ ∀ᶠ x in 𝓝[≠] a, f x < f a := Iff.rfl


end MetaMathlibExt
