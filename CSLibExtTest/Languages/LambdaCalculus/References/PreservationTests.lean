/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.References.Preservation
public import CSLibExtTest.Languages.LambdaCalculus.References.ProgressTests

/-!
# Tests for preservation and type safety of the calculus with references

* Allocation forces the store typing to grow: after `ref unit` steps to
  `loc 0`, the result is not typable under the old (empty) store typing, and
  preservation supplies the extension `[Unit]`.
* Type safety for the sample programs of `ProgressTests`: every configuration
  reachable from them is a value or can step.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References.Tests

/-- The allocation step `ref unit | [] → loc 0 | [unit]`. -/
theorem alloc_step : Step (.ref .unit : Term Empty) [] (.loc 0) [.unit] :=
  Step.refValue .unit

/-- `loc 0` has no type under the empty store typing: preservation with
`Σ' = Σ` would be false for E-RefV. -/
theorem loc0_untypable_empty (T : Ty Empty) : ¬ HasType [] [] (.loc 0 : Term Empty) T := by
  intro h
  cases h with
  | loc hl => simp at hl

/-- Preservation supplies a store typing extending `[]` under which the
result and the new store are well typed; here it is `[Unit]`. -/
example : ∃ S', [] <+: S' ∧ HasType [] S' (.loc 0 : Term Empty) (.ref .unit) ∧
    StoreTyped [] S' ([.unit] : Store Empty) :=
  preservation (.ref .unit) .nil alloc_step

example : HasType [] [Ty.unit] (.loc 0 : Term Empty) (.ref .unit) ∧
    StoreTyped [] [Ty.unit] ([.unit] : Store Empty) :=
  ⟨.loc rfl, .cons ⟨.unit, .unit⟩ .nil⟩

/-- Every configuration reachable from `readFresh` is a value or can step. -/
example (t' : Term Empty) (μ' : Store Empty) (h : Steps readFresh [] t' μ') :
    t'.Value ∨ ∃ t'' μ'', Step t' μ' t'' μ'' :=
  typeSafety_empty readFresh_hasType h

/-- Every configuration reachable from `writeThenRead` is well typed, with
type `Unit → Unit`, under some extension of the empty store typing. -/
example (t' : Term Empty) (μ' : Store Empty) (h : Steps writeThenRead [] t' μ') :
    ∃ S', [] <+: S' ∧ HasType [] S' t' (.arr .unit .unit) ∧ StoreTyped [] S' μ' :=
  h.preservation writeThenRead_hasType .nil

end Cslib.Languages.LambdaCalculus.References.Tests
