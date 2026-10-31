/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.PercoSubcriticalDecay

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.PercoSubcriticalDecay`

* `subcritical_decay_of_lt_tildeBetaCPerco` applied below `β̃_c^{perc}`;
* the decay bound specialised at `n = 0` gives `crossProb ≤ C`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.PercoSubcriticalDecay

open _root_.StatMech _root_.StatMech.Sharpness

-- Exponential decay of the one-arm probability below `β̃_c^{perc}`.
example (d : ℕ) (β : ℝ) (hβ : β < tildeBetaCPerco d) :
    ∃ c > 0, ∃ C > 0, ∀ n : ℕ,
      Percolation.crossProb d (bondParam β) (bondParam_le_one β) n ≤ C * Real.exp (-c * n) :=
  subcritical_decay_of_lt_tildeBetaCPerco hβ

-- At `n = 0` the bound is the constant `C`.
example (d : ℕ) (β : ℝ) (hβ : β < tildeBetaCPerco d) :
    ∃ C > 0, Percolation.crossProb d (bondParam β) (bondParam_le_one β) 0 ≤ C := by
  obtain ⟨c, -, C, hC, h⟩ := subcritical_decay_of_lt_tildeBetaCPerco hβ
  exact ⟨C, hC, by simpa using h 0⟩

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.PercoSubcriticalDecay
