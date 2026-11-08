/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.EncodedReduced

/-!
# Tests for the computable reduction of encoded grammars

The grammar `g` has `0 → 1 2`, `1 → ε | true`, `2 → 1 | false`, so its language is
`{ε, t, f, tt, tf}` (writing `t`, `f` for `true`, `false`).

* All three nonterminals are nullable.
* `reduce g` has no empty and no unit right-hand sides; it contains the expected copied
  productions `0 → true`, `0 → false`, `2 → true`.
* Membership, decided by the A_CFG procedure `memLanguageB`: the empty word is in `g` but not in
  `reduce g`; the other words agree.
* `language_reduce`, `isReduced_reduce` and `primrec_reduce` instantiated.
-/

@[expose] public section

namespace Cslib.Language.EncodedCFG.ReducedTests

/-- `0 → 1 2`, `1 → ε | true`, `2 → 1 | false`. -/
def g : EncodedCFG Bool :=
  ⟨0, [(0, [.inl 1, .inl 2]), (1, []), (1, [.inr true]), (2, [.inl 1]), (2, [.inr false])]⟩

example : ∀ i ∈ [0, 1, 2], i ∈ g.nullable := by decide

example : 3 ∉ g.nullable := by decide

example : g.reduce.rules.all (fun e => decide (0 < e.2.length) && (unitTarget e.2).isNone) =
    true := by decide

example : g.reduce.rules = [(0, [.inl 1, .inl 2]), (0, [.inr true]), (0, [.inr false]),
    (1, [.inr true]), (2, [.inr true]), (2, [.inr false])] := by decide

example : g.memLanguageB [] = true ∧ g.reduce.memLanguageB [] = false := by decide +kernel

example : ∀ w ∈ [[true], [false], [true, true], [true, false]],
    g.memLanguageB w = true ∧ g.reduce.memLanguageB w = true := by decide +kernel

example : ∀ w ∈ [[false, true], [false, false]],
    g.memLanguageB w = false ∧ g.reduce.memLanguageB w = false := by decide +kernel

example : [] ∉ g.reduce.language := fun h => ((language_reduce g).le h).2 rfl

example : IsReduced g.reduce.toCFG := isReduced_reduce g

example : Primrec (reduce (T := Bool)) := primrec_reduce

end Cslib.Language.EncodedCFG.ReducedTests
