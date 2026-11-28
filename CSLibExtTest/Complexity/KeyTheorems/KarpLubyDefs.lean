/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.KeyTheorems.KarpLubyDefs

namespace MetaMathlibExt.Complexity.KeyTheorems.KarpLuby

/-- The empty disjunction is unsatisfiable. -/
example (a : ℕ → Bool) : ¬ dnfSat a [] := by
  simp [dnfSat]

/-- The empty term is satisfied by every assignment. -/
example (a : ℕ → Bool) : dnfSat a [[]] := by
  simp [dnfSat]

/-- `x₀ ∧ ¬x₁` holds under the assignment `x₀ = true`, `x₁ = false`. -/
example : dnfSat (fun v => v == 0) [[(0, true), (1, false)]] := by
  unfold dnfSat
  decide

/-- `(x₀ ∧ x₁) ∨ ¬x₀` fails under the assignment `x₀ = true`, `x₁ = false`. -/
example : ¬ dnfSat (fun v => v == 0) [[(0, true), (1, true)], [(0, false)]] := by
  unfold dnfSat
  decide

end MetaMathlibExt.Complexity.KeyTheorems.KarpLuby
