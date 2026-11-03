/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.Pivotal

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.Pivotal`

On `ConfigSpace (Fin 2)` with the increasing event `both = {ω | ω 0 ∧ ω 1}`:
* `setOpen` and `setClosed` computed;
* `IsPivotal` computed: coordinate `0` is pivotal for `both` at `(0, 1)` and not at `(0, 0)`;
* `isPivotal_iff_of_isIncreasing` applied with `IsIncreasing both` proved.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.Pivotal

open _root_.StatMech

/-- The event "both coordinates are open". -/
def both : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true ∧ ω 1 = true}

-- `both` is increasing.
theorem isIncreasing_both : IsIncreasing both := by
  rintro x y hxy ⟨h0, h1⟩
  have e0 := hxy 0
  have e1 := hxy 1
  rw [h0] at e0
  rw [h1] at e1
  exact ⟨top_le_iff.mp e0, top_le_iff.mp e1⟩

-- `setOpen 0` opens coordinate `0`.
example : setOpen 0 (![false, true] : ConfigSpace (Fin 2)) = ![true, true] := by
  funext i
  fin_cases i <;> rfl

-- `setClosed 1` closes coordinate `1`.
example : setClosed 1 (![true, true] : ConfigSpace (Fin 2)) = ![true, false] := by
  funext i
  fin_cases i <;> rfl

-- Coordinate `0` is pivotal for `both` at `(0, 1)`.
example : IsPivotal 0 both ![false, true] := by
  simp [IsPivotal, setOpen, setClosed, both]

-- Coordinate `0` is not pivotal for `both` at `(0, 0)`.
example : ¬ IsPivotal 0 both ![false, false] := by
  simp [IsPivotal, setOpen, setClosed, both]

-- For increasing `both`, pivotality means: closed gives `∉`, open gives `∈`.
example (ω : ConfigSpace (Fin 2)) :
    IsPivotal 0 both ω ↔ (setClosed 0 ω ∉ both ∧ setOpen 0 ω ∈ both) :=
  isPivotal_iff_of_isIncreasing isIncreasing_both ω

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.Pivotal
