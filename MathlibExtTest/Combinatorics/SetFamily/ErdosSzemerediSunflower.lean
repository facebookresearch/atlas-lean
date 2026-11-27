/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.ErdosSzemerediSunflower
import Mathlib.Data.Fintype.Powerset

/-!
# Tests for the Erdős–Szemerédi sunflower bound

The first case of the theorem uses one base for all large ground sets. The examples also
check a four-petal sunflower with a nonempty core and a small sunflower-free Boolean cube.
-/

open MathlibExt.Combinatorics.ErdosProblem857WeakSunflowerWanted

example : ∃ c : ℝ, 0 < c ∧ c < 2 ∧ ∀ᶠ n : ℕ in Filter.atTop,
    ∀ F : Finset (Finset (Fin n)), IsKSunflowerFree 4 F → (F.card : ℝ) ≤ c ^ n :=
  conjecture_holds 4 (by decide)

example : ContainsKSunflower 4 ({{0}, {0, 1}, {0, 2}, {0, 3}} : Finset (Finset (Fin 4))) := by
  refine ⟨_, Finset.Subset.rfl, by decide, ?_⟩
  decide

example : IsKSunflowerFree 4 (Finset.univ : Finset (Finset (Fin 1))) := by
  rintro ⟨T, hT, hcard, _⟩
  have h := Finset.card_le_card hT
  simp [hcard] at h
