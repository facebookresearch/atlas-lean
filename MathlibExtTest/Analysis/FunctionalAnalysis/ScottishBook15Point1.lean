/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook15Point1
import Mathlib.Tactic.Linarith

/-! # Tests for the negative answer to Scottish Book Problem 15.1 -/

open MathlibExt.Analysis.FunctionalAnalysis.ScottishBook15Point1Wanted

-- Recover a single space and sphere satisfying all the counterexample properties.
example : ∃ (E : Type) (_ : TopologicalSpace E) (_ : AddCommGroup E) (_ : Module ℝ E),
    IsTypeF E ∧ ∃ K : Set E, IsSphere E K ∧ IsBoundedSet E K ∧ ¬ AdmitsBanachNorm E := by
  classical
  by_contra h
  apply boundedSphereFImpliesB_refuted
  intro E t g m hF ⟨K, hK, hB⟩
  by_contra hN
  exact h ⟨E, t, g, m, hF, K, hK, hB, hN⟩

-- A set meeting just the positive half of the real line misses the opposite ray.
example : ¬ IsSphere ℝ {1} := by
  intro h
  obtain ⟨t, ⟨ht, hmem⟩, _⟩ := h.2 (-1) (by norm_num)
  change t * (-1) = 1 at hmem
  linarith
