/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.StlcExtended.Safety

/-!
# Programs in the extended simply typed lambda calculus

Closed programs over the unit and boolean types, evaluated by explicit call-by-value reduction
sequences:

* swapping the summands of `bool + unit`;
* currying a conjunction on pairs of booleans and uncurrying the result;
* a `let` whose body tests the bound boolean.

Each result is a value, and it is the only value the program reduces to (`Steps.value_unique`).
A swap whose case branches are exchanged maps `inl tt` to `inl tt` and so fails the swap
specification; the same uniqueness statement rules out a second result value. The safety
corollaries `final_or_step` and `not_stuck` are applied along the reductions, and their
statements are pinned.
-/

@[expose] public section

universe u

namespace Cslib.Languages.LambdaCalculus.StlcExtended.ProgramsTests

open Cslib.Languages.LambdaCalculus.StlcExtended
open scoped CslibStlcExtended

/-! ### Swapping the summands of a sum -/

/-- Swap the summands of `bool + unit`. -/
def swap : Tm (Base := Unit) [] (.sum .bool .unit ⇒ .sum .unit .bool) :=
  .lam (.case (.var .zero) (.inr (.var .zero)) (.inl (.var .zero)))

/-- `swap (inl tt)` reduces to `inr tt`. -/
theorem swap_inl : Steps (.app swap (.inl .tt)) (.inr .tt) :=
  .head (.beta (.inl .tt)) (.single (.caseInl .tt))

/-- `swap (inr ⟨⟩)` reduces to `inl ⟨⟩`. -/
theorem swap_inr : Steps (.app swap (.inr .unit)) (.inl .unit) :=
  .head (.beta (.inr .unit)) (.single (.caseInr .unit))

/-- `inr tt` is the only value that `swap (inl tt)` reduces to. -/
theorem swap_inl_unique {v : Tm (Base := Unit) [] (.sum .unit .bool)}
    (h : Steps (.app swap (.inl .tt)) v) (hv : Value v) : v = .inr .tt :=
  Steps.value_unique h swap_inl hv (.inr .tt)

/-- `inl ⟨⟩` is the only value that `swap (inr ⟨⟩)` reduces to. -/
theorem swap_inr_unique {v : Tm (Base := Unit) [] (.sum .unit .bool)}
    (h : Steps (.app swap (.inr .unit)) v) (hv : Value v) : v = .inl .unit :=
  Steps.value_unique h swap_inr hv (.inl .unit)

/-- A second result value is refuted: `swap (inl tt)` does not reduce to `inr ff`. -/
theorem swap_inl_not_inr_ff : ¬ Steps (.app swap (.inl .tt)) (.inr .ff) := by
  intro h
  have heq := Steps.value_unique h swap_inl (.inr .ff) (.inr .tt)
  cases heq

/-! ### A swap with exchanged branches

The control uses the homogeneous sum `bool + bool`, where exchanging the branches still
type-checks. -/

/-- Swap the summands of `bool + bool`. -/
def swapBB : Tm (Base := Unit) [] (.sum .bool .bool ⇒ .sum .bool .bool) :=
  .lam (.case (.var .zero) (.inr (.var .zero)) (.inl (.var .zero)))

/-- The same function with its case branches exchanged. -/
def swapBBExchanged : Tm (Base := Unit) [] (.sum .bool .bool ⇒ .sum .bool .bool) :=
  .lam (.case (.var .zero) (.inl (.var .zero)) (.inr (.var .zero)))

/-- The swap maps `inl tt` to `inr tt`. -/
theorem swapBB_inl : Steps (.app swapBB (.inl .tt)) (.inr .tt) :=
  .head (.beta (.inl .tt)) (.single (.caseInl .tt))

/-- The exchanged version maps `inl tt` to `inl tt`. -/
theorem swapBBExchanged_inl : Steps (.app swapBBExchanged (.inl .tt)) (.inl .tt) :=
  .head (.beta (.inl .tt)) (.single (.caseInl .tt))

/-- The exchanged version does not meet the swap specification. -/
theorem swapBBExchanged_not_swap : ¬ Steps (.app swapBBExchanged (.inl .tt)) (.inr .tt) := by
  intro h
  have heq := Steps.value_unique h swapBBExchanged_inl (.inr .tt) (.inl .tt)
  cases heq

/-! ### Currying and uncurrying -/

/-- Conjunction on a pair of booleans. -/
def andPair : Tm (Base := Unit) [] (.prod .bool .bool ⇒ .bool) :=
  .lam (.ite (.fst (.var .zero)) (.snd (.var .zero)) .ff)

/-- Currying: `λ f. λ a. λ b. f ⟨a, b⟩`. -/
def curry {A B C : Ty Unit} : Tm [] ((.prod A B ⇒ C) ⇒ A ⇒ B ⇒ C) :=
  .lam (.lam (.lam (.app (.var (.succ (.succ .zero))) (.pair (.var (.succ .zero)) (.var .zero)))))

/-- Uncurrying: `λ g. λ p. g (fst p) (snd p)`. -/
def uncurry {A B C : Ty Unit} : Tm [] ((A ⇒ B ⇒ C) ⇒ .prod A B ⇒ C) :=
  .lam (.lam (.app (.app (.var (.succ .zero)) (.fst (.var .zero))) (.snd (.var .zero))))

/-- The curried conjunction applied to `tt` and `ff` reduces to `ff`. -/
theorem curry_and_tt_ff : Steps (.app (.app (.app curry andPair) .tt) .ff) .ff :=
  .head (.appFun (.appFun (.beta (.lam _)))) <|
  .head (.appFun (.beta .tt)) <|
  .head (.beta .ff) <|
  .head (.beta (.pair .tt .ff)) <|
  .head (.ite (.fstPair .tt .ff)) <|
  .head .iteTt <|
  .single (.sndPair .tt .ff)

/-- `ff` is the only value that the curried conjunction applied to `tt` and `ff` reduces to. -/
theorem curry_and_tt_ff_unique {v : Tm (Base := Unit) [] .bool}
    (h : Steps (.app (.app (.app curry andPair) .tt) .ff) v) (hv : Value v) : v = .ff :=
  Steps.value_unique h curry_and_tt_ff hv .ff

/-- Uncurrying the curried conjunction and applying it to `⟨tt, tt⟩` reduces to `tt`. -/
theorem uncurry_curry_and :
    Steps (.app (.app uncurry (.app curry andPair)) (.pair .tt .tt)) .tt :=
  .head (.appFun (.appArg (.lam _) (.beta (.lam _)))) <|
  .head (.appFun (.beta (.lam _))) <|
  .head (.beta (.pair .tt .tt)) <|
  .head (.appFun (.appArg (.lam _) (.fstPair .tt .tt))) <|
  .head (.appFun (.beta .tt)) <|
  .head (.appArg (.lam _) (.sndPair .tt .tt)) <|
  .head (.beta .tt) <|
  .head (.beta (.pair .tt .tt)) <|
  .head (.ite (.fstPair .tt .tt)) <|
  .head .iteTt <|
  .single (.sndPair .tt .tt)

/-- `tt` is the only value that the uncurried conjunction applied to `⟨tt, tt⟩` reduces to. -/
theorem uncurry_curry_and_unique {v : Tm (Base := Unit) [] .bool}
    (h : Steps (.app (.app uncurry (.app curry andPair)) (.pair .tt .tt)) v) (hv : Value v) :
    v = .tt :=
  Steps.value_unique h uncurry_curry_and hv .tt

/-! ### `let` and conditionals -/

/-- `let x = tt in (if x then ff else tt)` reduces to `ff`. -/
theorem let_ite : Steps (.letIn .tt (.ite (.var .zero) .ff .tt) : Tm (Base := Unit) [] .bool) .ff :=
  .head (.letValue .tt) (.single .iteTt)

/-- `ff` is the only value that the `let` program reduces to. -/
theorem let_ite_unique {v : Tm (Base := Unit) [] .bool}
    (h : Steps (.letIn .tt (.ite (.var .zero) .ff .tt)) v) (hv : Value v) : v = .ff :=
  Steps.value_unique h let_ite hv .ff

/-! ### Safety along the programs -/

/-- Every term reachable from `swap (inl tt)` is a value or reduces. -/
example {t' : Tm (Base := Unit) [] (.sum .unit .bool)} (h : Steps (.app swap (.inl .tt)) t') :
    Value t' ∨ ∃ t'', Step t' t'' :=
  final_or_step h

/-- No term reachable from the curried conjunction program is stuck. -/
example {t' : Tm (Base := Unit) [] .bool}
    (h : Steps (.app (.app (.app curry andPair) .tt) .ff) t') :
    ¬ (¬ Value t' ∧ Relation.Normal Step t') :=
  not_stuck h

/-- Safety at the result of the uncurrying program. -/
example : Value (.tt : Tm (Base := Unit) [] .bool) ∨
    ∃ t'' : Tm (Base := Unit) [] .bool, Step .tt t'' :=
  final_or_step uncurry_curry_and

/-- Safety at the result of the `let` program. -/
example : ¬ (¬ Value (.ff : Tm (Base := Unit) [] .bool) ∧
    Relation.Normal (@Step Unit [] .bool) .ff) :=
  not_stuck let_ite

/-! ### Statement pins -/

section Pins

variable {Base : Type u} {A : Ty Base}

/-- Pin: closed terms reduce only to values or reducible terms. -/
theorem final_or_step_pin {t t' : Tm [] A} (h : Steps t t') : Value t' ∨ ∃ t'', Step t' t'' :=
  final_or_step h

/-- Pin: closed terms never reach a stuck term. -/
theorem not_stuck_pin {t t' : Tm [] A} (h : Steps t t') :
    ¬ (¬ Value t' ∧ Relation.Normal Step t') :=
  not_stuck h

end Pins

end Cslib.Languages.LambdaCalculus.StlcExtended.ProgramsTests
