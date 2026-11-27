/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.ScottishBook39

open MathlibExt.Analysis.Complex.ScottishBook39Wanted

-- The witness is discontinuous, normalized at one, and not the trivial modulus.
example : ∃ φ : ℂ → ℝ, ¬ Continuous φ ∧ φ 1 = 1 ∧ (∃ z, z ≠ 0 ∧ φ z ≠ 1) := by
  obtain ⟨φ, hdisc, _, hnonzero, hnontrivial, _, hmul⟩ :=
    exists_discontinuous_subadditive_multiplicative
  obtain ⟨z, hz⟩ := not_forall.mp hnonzero
  have h₁ : φ 1 * φ z = 1 * φ z := by
    simpa only [one_mul] using (hmul 1 z).symm
  refine ⟨φ, hdisc, mul_right_cancel₀ hz h₁, ?_⟩
  by_contra! h
  exact hnontrivial h
