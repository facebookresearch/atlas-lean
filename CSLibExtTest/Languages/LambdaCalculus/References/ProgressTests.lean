/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.References.Progress
public import CSLibExt.Languages.LambdaCalculus.References.Embedding

/-!
# Tests for the simply typed lambda calculus with references

* A closed program that allocates a cell, passes it to a function and
  dereferences it: its typing derivation and its evaluation to `unit`.
* Evaluation is driven by the store: a cell allocated with one function value
  and overwritten with another is read back with the new value.
* The hypotheses of `progress` are needed: `!unit` is stuck and untypable, and
  `!(loc 0)` is stuck in the empty store although it is typable under a store
  typing that the empty store does not satisfy.
* The embedding of intrinsically typed STLC terms.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References.Tests

open Term

/-- `(λ x : Ref Unit. !x) (ref unit)`. -/
def readFresh : Term Empty :=
  .app (.lam (.ref .unit) (.deref (.var 0))) (.ref .unit)

theorem readFresh_hasType : HasType [] [] readFresh .unit :=
  .app (.lam (.deref (.var rfl))) (.ref .unit)

/-- `readFresh` evaluates to `unit`, leaving one cell holding `unit`. -/
theorem readFresh_steps : Steps readFresh [] .unit [.unit] :=
  .head (Step.appRight (.lam _ _) (.refValue .unit)) <|
  .head (Step.appAbs (.loc 0)) <|
  .single (Step.derefLoc rfl)

/-- The first step of `readFresh` is determined. -/
example (t' : Term Empty) (μ' : Store Empty) (h : Step readFresh [] t' μ') :
    t' = .app (.lam (.ref .unit) (.deref (.var 0))) (.loc 0) ∧ μ' = [.unit] :=
  Step.deterministic h (Step.appRight (.lam _ _) (.refValue .unit))

/-- `λx:Unit. x`. -/
def idU : Term Empty := .lam .unit (.var 0)

/-- `λx:Unit. unit`, a second value of type `Unit → Unit`. -/
def constU : Term Empty := .lam .unit .unit

example : idU ≠ constU := by decide

/-- `(λr : Ref (Unit → Unit). (λ_ : Unit. !r) (r := constU)) (ref idU)`:
allocate a cell holding `idU`, overwrite it with `constU`, then read it.
Sequencing is the application of a function that ignores its argument. -/
def writeThenRead : Term Empty :=
  .app (.lam (.ref (.arr .unit .unit))
      (.app (.lam .unit (.deref (.var 1))) (.assign (.var 0) constU)))
    (.ref idU)

theorem writeThenRead_hasType : HasType [] [] writeThenRead (.arr .unit .unit) :=
  .app (.lam (.app (.lam (.deref (.var rfl))) (.assign (.var rfl) (.lam .unit))))
    (.ref (.lam (.var rfl)))

/-- After allocation the cell holds `idU`. -/
theorem writeThenRead_alloc :
    Step writeThenRead []
      (.app (.lam (.ref (.arr .unit .unit))
          (.app (.lam .unit (.deref (.var 1))) (.assign (.var 0) constU))) (.loc 0))
      [idU] :=
  Step.appRight (.lam _ _) (.refValue (.lam _ _))

/-- The program reads back `constU`, not the initial `idU`, and leaves the
store `[constU]`: assignment changed what the dereference returns. -/
theorem writeThenRead_steps : Steps writeThenRead [] constU [constU] :=
  .head writeThenRead_alloc <|
  .head (Step.appAbs (.loc 0)) <|
  .head (Step.appRight (.lam _ _) (Step.assignLoc (.lam _ _) (by decide))) <|
  .head (Step.appAbs .unit) <|
  .single (Step.derefLoc rfl)

/-- `!unit` is stuck. -/
theorem deref_unit_stuck : ¬ (Term.deref (.unit : Term Empty)).Value ∧
    ∀ t' μ', ¬ Step (.deref .unit) ([] : Store Empty) t' μ' := by
  refine ⟨(fun h => nomatch h), fun t' μ' h => ?_⟩
  cases h with
  | deref h => exact Step.not_of_value .unit h

/-- `!unit` has no type, so `progress` does not apply to it. -/
theorem deref_unit_untypable (S : List (Ty Empty)) (T : Ty Empty) :
    ¬ HasType [] S (.deref .unit) T := by
  intro h
  cases h with
  | deref h => cases h

/-- `!(loc 0)` is stuck in the empty store. -/
theorem deref_loc_stuck : ¬ (Term.deref (.loc 0 : Term Empty)).Value ∧
    ∀ t' μ', ¬ Step (.deref (.loc 0)) ([] : Store Empty) t' μ' := by
  refine ⟨(fun h => nomatch h), fun t' μ' h => ?_⟩
  cases h with
  | deref h => exact Step.not_of_value (.loc 0) h
  | derefLoc hl => simp at hl

/-- `!(loc 0)` is typable under the store typing `[Unit]`, which the empty
store does not satisfy: `progress` needs its store hypothesis. -/
example : HasType [] [Ty.unit] (Term.deref (.loc 0 : Term Empty)) .unit ∧
    ¬ StoreTyped [] [Ty.unit] ([] : Store Empty) :=
  ⟨.deref (.loc rfl), fun h => by simpa using h.length_eq⟩

/-- The store `[unit]` is well typed under `[Unit]`. -/
example : StoreTyped [] [Ty.unit] ([.unit] : Store Empty) :=
  .cons ⟨.unit, .unit⟩ .nil

/-- A store entry must be a value: `[(λx:Unit. x) unit]` has an entry of type
`Unit` but is not a well-typed store. -/
example : ¬ StoreTyped [] [Ty.unit] ([.app idU .unit] : Store Empty) := by
  intro h
  cases h with
  | cons hv _ => exact nomatch hv.1

/-- The intrinsic identity on a base type embeds as `λ x : b. x`. -/
example (b : Unit) :
    Term.ofRaw (Stlc.Tm.lam (Γ := []) (A := .base b) (.var .zero)).erase =
      (.lam (.base b) (.var 0) : Term Unit) := rfl

/-- The intrinsic term `λ f : b → b. λ x : b. f x`. -/
def applyStlc (b : Unit) : Stlc.Tm [] (.arr (.arr (.base b) (.base b)) (.arr (.base b) (.base b))) :=
  .lam (.lam (.app (.var (.succ .zero)) (.var .zero)))

/-- Its erasure has the embedded type. -/
example (b : Unit) : HasType [] [] (Term.ofRaw (applyStlc b).erase)
    (.arr (.arr (.base b) (.base b)) (.arr (.base b) (.base b))) :=
  HasType.ofStlc (applyStlc b) []

end Cslib.Languages.LambdaCalculus.References.Tests
