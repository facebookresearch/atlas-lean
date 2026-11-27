/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fin.VecNotation
import MathlibExt.GameTheory.NimPassIndicator

open MetaMathlibExt

-- Both the step sections and the constant sections have the NS property.
example : ∀ (x : Fin 2 → ℕ) i,
    HasNSProperty fun t ↦ nimPassIndicator ![2, 4] (Function.update x i t) :=
  (nimPassIndicator_sections_hasNSProperty_iff (m := ![2, 4]) (by decide)).mpr (by decide)

-- One odd threshold suffices for some section to fail the NS property.
example : ¬ ∀ (x : Fin 2 → ℕ) i,
    HasNSProperty fun t ↦ nimPassIndicator ![3, 4] (Function.update x i t) := by
  intro h
  have heven := (nimPassIndicator_sections_hasNSProperty_iff (m := ![3, 4]) (by decide)).mp h 0
  exact (by decide : ¬ Even 3) heven

-- A saturated second pile masks the odd threshold of the first pile.
example (t : ℕ) : nimPassIndicator ![3, 4] (Function.update ![0, 4] 0 t) = 1 := by
  unfold nimPassIndicator
  exact ite_eq_left ⟨1, by simp⟩
