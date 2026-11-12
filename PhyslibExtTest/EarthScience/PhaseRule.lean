/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.PhaseRule

/-!
# Gibbs phase-rule checks

Concrete consumers of `PhyslibExt.EarthScience.PhaseRule`: a numeric
count for three components and two phases, the public shape of the
dimension theorem, a pure-component boundary case, and the boundary case
where the freedom count is zero.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The pure
component (`C = 1, P = 1`) has freedom `2` (temperature and pressure);
three components in two phases have freedom `3`; one component in three
phases has freedom `0`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric count
- B. Dimension theorem, concrete and abstract
-/

/-- Three components, two phases: `6 - 3 = 3` degrees of freedom. -/
example : (2 : ℤ) * (3 - 1) + 2 - (3 : ℤ) * (2 - 1) = 3 - 2 + 2 :=
  EarthScience.phase_rule_variable_count 3 2

/-- The public statement shape of the dimension form. -/
example (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P) (hF : P ≤ C + 2)
    (f : (Fin (P * (C - 1) + 2) → ℝ) →ₗ[ℝ] (Fin (C * (P - 1)) → ℝ))
    (hf : Function.Surjective f) :
    Module.finrank ℝ (LinearMap.ker f) = C + 2 - P :=
  EarthScience.phase_rule_finrank C P hC hP hF f hf

/-- Pure component, one phase: the constraint space is empty, the kernel
is the whole two-dimensional variable space, and the freedom count is `2`. -/
example :
    Module.finrank ℝ (LinearMap.ker
      (0 : (Fin (1 * (1 - 1) + 2) → ℝ) →ₗ[ℝ] (Fin (1 * (1 - 1)) → ℝ))) = 2 := by
  have hf : Function.Surjective
      (0 : (Fin (1 * (1 - 1) + 2) → ℝ) →ₗ[ℝ] (Fin (1 * (1 - 1)) → ℝ)) := by
    intro y
    exact ⟨0, by ext i; exact Fin.elim0 i⟩
  have h := EarthScience.phase_rule_finrank 1 1 (by norm_num) (by norm_num)
    (by norm_num) _ hf
  exact h

/-- One component, three phases: freedom count `0`, so the kernel of the
identity constraint map is zero-dimensional. -/
example :
    Module.finrank ℝ (LinearMap.ker
      (LinearMap.id : (Fin (3 * (1 - 1) + 2) → ℝ) →ₗ[ℝ]
        (Fin (1 * (3 - 1)) → ℝ))) = 0 := by
  have h := EarthScience.phase_rule_finrank 1 3 (by norm_num) (by norm_num)
    (by norm_num) LinearMap.id Function.surjective_id
  exact h
