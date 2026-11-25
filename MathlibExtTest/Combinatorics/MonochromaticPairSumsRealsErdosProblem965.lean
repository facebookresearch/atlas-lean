/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MonochromaticPairSumsRealsErdosProblem965
import Mathlib.Analysis.Real.Cardinality

/-! # Tests for the refutation of Erdős Problem 965 -/

open MathlibExt.Combinatorics.MonochromaticPairSumsRealsErdosProblem965Wanted

-- Recover a single colouring witnessing each requested colour on a distinct pair.
example : ∃ c : ℝ → Fin 2, ∀ A : Set ℝ, Cardinal.mk A = Cardinal.aleph 1 →
    ∀ i : Fin 2, ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ c (a + b) = i := by
  have h := alephOneMonochromaticPairSums_refuted
  unfold alephOneMonochromaticPairSums at h
  push Not at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun A hA i => ?_⟩
  obtain ⟨a, ha, b, hb, hab, hk⟩ := hc A hA (if i = 0 then 1 else 0)
  refine ⟨a, ha, b, hb, hab, ?_⟩
  split at hk <;> omega

-- A constant colouring does admit a monochromatic set of exactly the required cardinality.
example : ∃ A : Set ℝ, Cardinal.mk A = Cardinal.aleph 1 ∧ ∃ i : Fin 2,
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (fun _ : ℝ => (0 : Fin 2)) (a + b) = i := by
  obtain ⟨A, hA⟩ := Cardinal.le_mk_iff_exists_set.mp
    (Cardinal.mk_real ▸ Cardinal.aleph_one_le_continuum : Cardinal.aleph 1 ≤ Cardinal.mk ℝ)
  exact ⟨A, hA, 0, fun _ _ _ _ _ => rfl⟩
