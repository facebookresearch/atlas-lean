/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.RegularExpressionEquiv
public meta import CSLibExt.Computability.Decidability.RegularExpressionEquiv

/-!
# Tests for the equivalence of encoded regular expressions

* The state-count pass: `(true + false)*` has counts `[2, 2, 4, 5]`; an encoding that doubles a
  shared node three times has `16` Thompson states from four nodes.
* `Thompson.numStates` agrees with the pass on `flatten`ed expressions.
* The search bound: `true*` and `true**` give `2 ^ (3 + 4) = 128`.
* `eqB` run in the kernel, where the bound is small or a short word tells the expressions
  apart: `0 = 0 true`, `ε = 0*` (true); `true ≠ false`, `ε ≠ true*` (false). `ε = ε + ε`
  (bound `8`, `255` words) by `#guard`.
* Where the bound makes the search infeasible, `eqB_iff` turns a proof of language equality
  into `eqB = true`: `true* = true**` (`kstar_idem`) and `(true + false)* = (false + true)*`.
* The multi-stack decidability statement (EQ_REX) instantiated over `Bool`.
-/

@[expose] public section

namespace Cslib.Language.EncodedRegex.EquivTests

open Cslib.Automata Cslib.Decidability

/-- The alphabet `Bool`, listed as `[false, true]`. -/
local instance : FinEnum Bool := FinEnum.ofList [false, true] (by decide)

/-- `0`, one node. -/
def zeroE : EncodedRegex Bool := ⟨[.zero]⟩

/-- `ε`, one node. -/
def epsE : EncodedRegex Bool := ⟨[.epsilon]⟩

/-- The letter `true`. -/
def trueE : EncodedRegex Bool := ⟨[.char true]⟩

/-- The letter `false`. -/
def falseE : EncodedRegex Bool := ⟨[.char false]⟩

/-- `0 true`: nodes `0 = 0`, `1 = true`, `2 = 0 1`. -/
def zeroTrueE : EncodedRegex Bool := ⟨[.zero, .char true, .comp 0 1]⟩

/-- `0*`: nodes `0 = 0`, `1 = 0*`. -/
def zeroStarE : EncodedRegex Bool := ⟨[.zero, .star 0]⟩

/-- `true*`: nodes `0 = true`, `1 = 0*`. -/
def trueStarE : EncodedRegex Bool := ⟨[.char true, .star 0]⟩

/-- `true**`: nodes `0 = true`, `1 = 0*`, `2 = 1*`. -/
def trueStarStarE : EncodedRegex Bool := ⟨[.char true, .star 0, .star 1]⟩

/-- `(true + false)*`: nodes `0 = true`, `1 = false`, `2 = 0 + 1`, `3 = 2*`. -/
def anyE : EncodedRegex Bool := ⟨[.char true, .char false, .plus 0 1, .star 2]⟩

/-- `(false + true)*`: nodes `0 = false`, `1 = true`, `2 = 0 + 1`, `3 = 2*`. -/
def anyE' : EncodedRegex Bool := ⟨[.char false, .char true, .plus 0 1, .star 2]⟩

/-- Shared subterms: `0 = true`, `1 = 0 + 0`, `2 = 1 + 1`, `3 = 2 + 2`, a tree with eight
leaves. -/
def doubledE : EncodedRegex Bool := ⟨[.char true, .plus 0 0, .plus 1 1, .plus 2 2]⟩

/-! ## The state-count pass and the bound -/

example : stateCounts anyE.nodes = [2, 2, 4, 5] := by decide
example : anyE.numThompsonStates = 5 := by decide
example : stateCounts doubledE.nodes = [2, 4, 8, 16] := by decide
example : doubledE.numThompsonStates = 16 := by decide
example : zeroE.numThompsonStates = 0 := by decide
example : (⟨[]⟩ : EncodedRegex Bool).numThompsonStates = 0 := by decide

example : (flatten (.star (.plus (.char true) (.char false)))).nodes = anyE.nodes := rfl
example : Thompson.numStates (RegularExpression.star (.plus (.char true) (.char false))) =
    anyE.numThompsonStates := by
  rw [show anyE = flatten (.star (.plus (.char true) (.char false))) from rfl, numThompsonStates_eq,
    toRegex_flatten]

example : eqBound trueStarE trueStarStarE = 128 := by decide
example : eqBound zeroE zeroTrueE = 4 := by decide

/-! ## The decider run in the kernel -/

example : eqB zeroE zeroTrueE = true := by decide +kernel
example : eqB epsE zeroStarE = true := by decide +kernel
example : eqB trueE falseE = false := by decide +kernel
example : eqB epsE trueStarE = false := by decide +kernel

/-- `ε + ε`: nodes `0 = ε`, `1 = 0 + 0`. -/
def epsPlusE : EncodedRegex Bool := ⟨[.epsilon, .plus 0 0]⟩

-- Bound `8`: all `255` words of length `< 8`, checked by the compiled decider.
#guard eqBound epsE epsPlusE == 8 && eqB epsE epsPlusE

/-! Arguments that are not earlier nodes read as `0`: a self-reference and a forward
reference. -/

/-- `star 0` at node `0` refers to itself: it reads as `0∗`, with one Thompson state. -/
example : (⟨[.star 0]⟩ : EncodedRegex Bool).numThompsonStates = 1 := by decide

/-- Node `0` is `plus 1 1` with forward arguments, so it reads as `0 + 0`, with no states; the
root `star 0` adds one state. -/
example : (⟨[.plus 1 1, .char true, .star 0]⟩ : EncodedRegex Bool).numThompsonStates = 1 := by
  decide

/-- The self-referencing `star 0` is equivalent to `ε`. -/
example : eqB (⟨[.star 0]⟩ : EncodedRegex Bool) ⟨[.epsilon]⟩ = true := by decide +kernel

example : zeroE.toRegex.matches' = zeroTrueE.toRegex.matches' := eqB_iff.1 (by decide +kernel)
example : trueE.toRegex.matches' ≠ falseE.toRegex.matches' := fun h => by
  have := eqB_iff.2 h
  revert this
  decide +kernel

/-! ## Through `eqB_iff` -/

example : eqB trueStarE trueStarStarE = true := by
  refine eqB_iff.2 ?_
  rw [show trueStarE = flatten (.star (.char true)) from rfl,
    show trueStarStarE = flatten (.star (.star (.char true))) from rfl, toRegex_flatten,
    toRegex_flatten, RegularExpression.matches'_star, RegularExpression.matches'_star,
    RegularExpression.matches'_star, kstar_idem]

example : eqB anyE anyE' = true := by
  refine eqB_iff.2 ?_
  rw [show anyE = flatten (.star (RegularExpression.char true + .char false)) from rfl,
    show anyE' = flatten (.star (RegularExpression.char false + .char true)) from rfl,
    toRegex_flatten,
    toRegex_flatten, RegularExpression.matches'_star, RegularExpression.matches'_star,
    RegularExpression.matches'_add, RegularExpression.matches'_add, add_comm]

/-! ## EQ_REX -/

example : TM2Decidable fun p : EncodedRegex Bool × EncodedRegex Bool =>
    p.1.toRegex.matches' = p.2.toRegex.matches' :=
  tm2Decidable_matches_eq

end Cslib.Language.EncodedRegex.EquivTests
