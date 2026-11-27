/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.ClassicalProcesses.Typing

/-!
# Tests for Classical Processes typing

Concrete typing derivations and rejection statements for the
exponential- and quantifier-free fragment of classical processes, plus
calculations for erasure, free names, renaming, and substitution.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.ClassicalProcesses

namespace TypingTests

/-- Two test atoms. -/
inductive TestAtom where
  | left : TestAtom
  | right : TestAtom
deriving DecidableEq, Repr

/-- The proposition `A` used in the tests. -/
def propA : Logic.CLL.Proposition TestAtom := .atom .left

/-- The proposition `B` used in the tests. -/
def propB : Logic.CLL.Proposition TestAtom := .atom .right

/-- The tensor-commutation process `w(y).x[z].(w↔z | y↔x)`. Here `w` is
constant `0`, `x` is constant `1`, `y` is the variable bound by the outer
input, and `z` is the variable bound by the output in its first
component. -/
def tensorComm : Proc TestAtom :=
  .input (.const 0)
    (.output (.const 1)
      (.link (.const 0) (.var 0))
      (.link (.var 0) (.const 1)))

/-- A cut of a tensor output against a par input. The cut proposition is
`A ⊗ A⊥`; the remaining channels are constants `0` and `1`. -/
def tensorParrRedex : Proc TestAtom :=
  .cut (.tensor propA propA.dual)
    (.output (.var 0)
      (.link (.const 0) (.var 0))
      (.link (.const 1) (.var 0)))
    (.input (.var 0) (.link (.var 0) (.var 1)))

/-- A cut of empty output against empty input, with a link as the body of
the empty input. -/
def unitCut : Proc TestAtom :=
  .cut .one (.emptyOutput (.var 0))
    (.emptyInput (.var 0) (.link (.const 0) (.const 1)))

/-- The same unit forms cut at an atomic proposition instead of `1`. -/
def mismatchedUnitCut : Proc TestAtom :=
  .cut propA (.emptyOutput (.var 0))
    (.emptyInput (.var 0) (.link (.const 0) (.const 1)))

/-- Swap free channels `0` and `1`, leaving every other name unchanged. -/
def swap01 : PiCalculus.Name → PiCalculus.Name
  | .const 0 => .const 1
  | .const 1 => .const 0
  | n => n

/-- The source's tensor-commutation derivation is typed by
`w : A⊥ ⅋ B⊥` and `x : B ⊗ A`. -/
theorem tensor_comm_typed :
    HasType
      (((∅ : Context TestAtom).insert (.const 1)
          (.tensor propB propA)).insert (.const 0)
        (.parr propA.dual propB.dual))
      tensorComm := by
  refine HasType.parr ?_ (by decide)
  convert HasType.tensor (Γ := (∅ : Context TestAtom).insert (.const 0) propB.dual)
    (Δ := (∅ : Context TestAtom).insert (.var 0) propA.dual) (x := .const 1)
    (HasType.ax (w := .const 0) (x := .var 0) (a := propB) (by decide))
    (HasType.ax (w := .var 0) (x := .const 1) (a := propA) (by decide))
    (by decide) (by decide) (by decide) using 1
  decide

/-- A tensor/par cut redex is typed with dual remaining channels. -/
theorem tensor_parr_redex_typed :
    HasType
      (((∅ : Context TestAtom).insert (.const 0) propA.dual).insert
        (.const 1) propA)
      tensorParrRedex := by
  have h := HasType.cut
    (Γ := ((∅ : Context TestAtom).insert (.const 0) propA.dual).insert (.const 1) propA)
    (Δ := ∅) (a := .tensor propA propA.dual)
    (p := .output (.var 0) (.link (.const 0) (.var 0)) (.link (.const 1) (.var 0)))
    (q := .input (.var 0) (.link (.var 0) (.var 1)))
    (by
      convert HasType.tensor (Γ := (∅ : Context TestAtom).insert (.const 0) propA.dual)
        (Δ := (∅ : Context TestAtom).insert (.const 1) propA) (x := .var 0)
        (HasType.ax (w := .const 0) (x := .var 0) (a := propA) (by decide))
        (HasType.ax (w := .const 1) (x := .var 0) (a := propA.dual) (by decide))
        (by decide) (by decide) (by decide) using 1
      decide)
    (HasType.parr (HasType.ax (by decide)) (by decide))
    (Finmap.Disjoint.symm _ _ (Finmap.disjoint_empty _))
  rw [Finmap.union_empty] at h
  exact h

/-- A cut of the multiplicative units `1` and `⊥` is typed. -/
theorem unit_cut_typed :
    HasType
      (((∅ : Context TestAtom).insert (.const 0) propA.dual).insert
        (.const 1) propA)
      unitCut := by
  rw [← Finmap.empty_union (s₁ := ((∅ : Context TestAtom).insert (.const 0) propA.dual).insert
    (.const 1) propA)]
  refine HasType.cut HasType.one ?_ (Finmap.disjoint_empty _)
  refine HasType.bot ?_ (by decide)
  exact HasType.ax (w := .const 0) (x := .const 1) (a := propA) (by decide)

/-- Empty choice admits an arbitrary additional environment under the
`⊤` rule. -/
theorem top_arbitrary_context_typed :
    HasType
      ((((∅ : Context TestAtom).insert (.const 0) propA).insert
          (.const 1) propB).insert (.const 2) .top)
      (.emptyChoice (.const 2)) := by
  exact HasType.top (by decide)

/-- A link from a channel to itself is not typable in any environment. -/
theorem self_link_not_typed (Γ : Context TestAtom) :
    ¬ HasType Γ (.link (.const 0) (.const 0)) := by
  intro h
  cases h with
  | ax hneq => exact hneq rfl

/-- The unit output and input forms cannot be cut at an atomic
proposition. -/
theorem mismatched_unit_cut_not_typed (Γ : Context TestAtom) :
    ¬ HasType Γ mismatchedUnitCut := by
  intro h
  cases h with
  | @cut Γ0 Δ0 a0 p0 q0 hp hq hd =>
    generalize hE : (Context.lift Γ0).insert (.var 0) propA = Θ at hp
    cases hp
    have hl := congrArg (Finmap.lookup (.var 0)) hE
    simp only [Finmap.lookup_insert] at hl
    cases hl

/-- Empty choice is not an introduction form for additive disjunction. -/
theorem empty_choice_not_oplus_typed :
    ¬ HasType
      ((∅ : Context TestAtom).insert (.const 0) (.oplus propA propB))
      (.emptyChoice (.const 0)) := by
  intro h
  generalize hC : ((∅ : Context TestAtom).insert (.const 0)
    (.oplus propA propB)) = C at h
  cases h
  have hl := congrArg (Finmap.lookup (.const 0)) hC
  simp only [Finmap.lookup_insert] at hl
  cases hl

/-- Erasing the axiom environment gives the two dual propositions. -/
theorem erase_ax_context :
    Context.eraseNames
      (((∅ : Context TestAtom).insert (.const 0) propA.dual).insert
        (.const 1) propA) = {propA, propA.dual} := by
  decide

/-- Erasing the tensor-commutation environment gives its two
propositions. -/
theorem erase_tensor_comm_context :
    Context.eraseNames
      (((∅ : Context TestAtom).insert (.const 1)
          (.tensor propB propA)).insert (.const 0)
        (.parr propA.dual propB.dual)) =
      {(.tensor propB propA), (.parr propA.dual propB.dual)} := by
  decide

/-- The free channels of tensor commutation are exactly `w` and `x`. -/
theorem tensor_comm_free_names :
    tensorComm.freeNames = {(.const 0), (.const 1)} := by
  decide

/-- Renaming swaps the two ends of a link. -/
theorem rename_link_swap01 :
    (Proc.link (.const 0) (.const 1) : Proc TestAtom).rename swap01 =
      .link (.const 1) (.const 0) := by
  rfl

/-- Substitution replaces the innermost bound variable. -/
theorem subst_link_var_zero :
    (Proc.link (.var 0) (.const 0) : Proc TestAtom).subst (.const 1) =
      .link (.const 1) (.const 0) := by
  rfl

end TypingTests

end Cslib.ClassicalProcesses
