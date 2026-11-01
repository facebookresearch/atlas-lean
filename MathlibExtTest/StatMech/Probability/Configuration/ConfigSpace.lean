/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Configuration.ConfigSpace

import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Constructions

/-!
# Tests for `MathlibExt.Probability.Configuration.ConfigSpace`

* `StatMech.ConfigSpace` and `StatMech.ConfigSpace.eval`: evaluated on concrete configurations
  of `Fin 3`; the coordinatewise order is checked.
* `measurable_pi_apply`, `continuous_apply`: applied.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.Configuration.ConfigSpace

open _root_.StatMech _root_.StatMech.ConfigSpace

/-- Evaluating the configuration `![true, false, true]` at site `1`. -/
example : eval (1 : Fin 3) (![true, false, true] : ConfigSpace (Fin 3)) = false := rfl

/-- The coordinatewise order: `![false, false, true] ≤ ![true, false, true]`, but not
conversely. -/
example : (![false, false, true] : ConfigSpace (Fin 3)) ≤ ![true, false, true] ∧
    ¬ (![true, false, true] : ConfigSpace (Fin 3)) ≤ ![false, false, true] := by
  decide

/-- The full configuration `⊤` is `true` at every site. -/
example (e : ℕ) : eval e (⊤ : ConfigSpace ℕ) = true := rfl

/-- Coordinate projections are measurable and continuous. -/
example (e : ℕ) : Measurable (eval (E := ℕ) e) ∧ Continuous (eval (E := ℕ) e) :=
  ⟨measurable_pi_apply e, continuous_apply e⟩

end MathlibExtTest.StatMech.Probability.Configuration.ConfigSpace
