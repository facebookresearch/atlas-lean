/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.ContextFree

/-!
# Tests for emptiness of encoded context-free grammars

Over the alphabet `Bool`, with nonterminal `0` as the start:

* `S → true S false | ε` is nonempty; its generating nonterminals are `[0, 0]` (one entry per
  production found).
* `S → S` is empty, though it has a production.
* `S → A`, `A → A true`, `B → false`: `B` is generating but unreachable and `A` never finishes,
  so the language is empty; the procedure finds `B` and not `S`.
* `S → A B`, `A → true`, `B → false` needs two rounds and is nonempty.
* Emptiness is decidable by `decide` and computable as a predicate on encoded grammars.
* Membership (A_CFG): `anbn` contains `[]`, `[true, false]` and `[true, true, false, false]` and
  not `[true, false, false]` or `[false, true]`; `cyc` (`S → A`, `A → S | true`, a unit cycle)
  contains `[true]` and not `[]`. The multi-stack decidability statements are instantiated.
* Infiniteness (INFINITE_CFG): `S → true` and `S → ε` are finite by `decide +kernel` on
  `infiniteB`; `S → true S | true` has pumping bound `4` and is infinite, from a derivation of
  `true^4` and `infinite_of_mem_of_le`; `wordsOver` on a two-letter alphabet. For
  `S → true true true true`, `terminals` lists `true` once, so the words of length `pumpBound = 16`
  are a single word, not `4^16` copies of it.
-/

@[expose] public section

namespace Cslib.Language.EncodedCFG.EmptinessTests

/-- `S → true S false | ε`. -/
def anbn : EncodedCFG Bool := ⟨0, [(0, [.inr true, .inl 0, .inr false]), (0, [])]⟩

/-- `S → S`. -/
def loop : EncodedCFG Bool := ⟨0, [(0, [.inl 0])]⟩

/-- `S → A`, `A → A true`, `B → false`, with `S, A, B = 0, 1, 2`. -/
def stuck : EncodedCFG Bool := ⟨0, [(0, [.inl 1]), (1, [.inl 1, .inr true]), (2, [.inr false])]⟩

/-- `S → A B`, `A → true`, `B → false`, with `S, A, B = 0, 1, 2`. -/
def twoRounds : EncodedCFG Bool := ⟨0, [(0, [.inl 1, .inl 2]), (1, [.inr true]), (2, [.inr false])]⟩

example : anbn.generating = [0, 0] := by decide
example : anbn.isEmptyB = false := by decide
example : anbn.language ≠ 0 := by decide

example : loop.isEmptyB = true := by decide
example : loop.language = 0 := (isEmptyB_iff loop).1 (by decide)

example : stuck.generating = [2] := by decide
example : stuck.language = 0 := by decide

example : (genStep twoRounds.rules []) = [1, 2] := by decide
example : twoRounds.generating = [0, 1, 2] := by decide
example : twoRounds.language ≠ 0 := by decide

example : ComputablePred fun g : EncodedCFG Bool => g.language = 0 :=
  computablePred_language_eq_zero

example : memLanguageB anbn [] = true := by decide +kernel
example : memLanguageB anbn [true, false] = true := by decide +kernel
example : [true, true, false, false] ∈ anbn.language := memLanguageB_iff.1 (by decide +kernel)
example : memLanguageB anbn [true, false, false] = false := by decide +kernel
example : memLanguageB anbn [false, true] = false := by decide +kernel

/-- `S → A`, `A → S | true`, with `S, A = 0, 1`: a cycle of unit productions. -/
def cyc : EncodedCFG Bool := ⟨0, [(0, [.inl 1]), (1, [.inl 0]), (1, [.inr true])]⟩

example : [true] ∈ cyc.language := memLanguageB_iff.1 (by decide +kernel)
example : memLanguageB cyc [] = false := by decide +kernel

example : Cslib.Decidability.TM2Decidable
    fun p : EncodedCFG Bool × List Bool => p.2 ∈ p.1.language :=
  tm2Decidable_mem_language

example : Cslib.Decidability.TM2Decidable fun g : EncodedCFG Bool => g.language = 0 :=
  tm2Decidable_language_eq_zero

/-- `S → true`. -/
def one : EncodedCFG Bool := ⟨0, [(0, [.inr true])]⟩

/-- `S → ε`. -/
def eps : EncodedCFG Bool := ⟨0, [(0, [])]⟩

/-- `S → true S | true`. -/
def plus : EncodedCFG Bool := ⟨0, [(0, [.inr true, .inl 0]), (0, [.inr true])]⟩

example : one.infiniteB = false := by decide +kernel
example : ¬ one.language.Infinite := fun h => by
  have := infiniteB_iff.2 h
  revert this
  decide +kernel
example : eps.infiniteB = false := by decide +kernel

example : plus.pumpBound = 4 := by decide

theorem replicate_mem_plus (n : ℕ) : List.replicate (n + 1) true ∈ plus.language := by
  change _ ∈ plus.toCFG.language
  rw [mem_language_iff_yields]
  induction n with
  | zero =>
      exact yields_of_rule (g := plus.toCFG) (r := ⟨0, [.terminal true]⟩)
        (mem_toCFG_rules.2 ⟨(0, [.inr true]), List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩)
        (Yields.terminal true Yields.nil)
  | succ n ih =>
      exact yields_of_rule (g := plus.toCFG) (r := ⟨0, [.terminal true, .nonterminal 0]⟩)
        (mem_toCFG_rules.2 ⟨(0, [.inr true, .inl 0]), List.mem_cons_self, rfl⟩)
        (by
          rw [List.replicate_succ]
          exact Yields.terminal true ih)

example : plus.language.Infinite :=
  infinite_of_mem_of_le (replicate_mem_plus 3) (by decide)

example :
    wordsOver [true, false] 2 = [[true, true], [false, true], [true, false], [false, false]] := by
  decide

/-- `S → true true true true`. -/
def four : EncodedCFG Bool := ⟨0, [(0, [.inr true, .inr true, .inr true, .inr true])]⟩

example : four.terminals = [true] := by decide
example : four.pumpBound = 16 := by decide
example : (wordsOver four.terminals four.pumpBound).length = 1 := by decide

/-- Four copies of `S → true false`: the bound counts distinct left-hand sides, so it stays
`2 ^ 2`. -/
def dup : EncodedCFG Bool :=
  ⟨0, [(0, [.inr true, .inr false]), (0, [.inr true, .inr false]), (0, [.inr true, .inr false]),
    (0, [.inr true, .inr false])]⟩

example : dup.pumpBound = 4 := by decide

example : Cslib.Decidability.TM2Decidable fun g : EncodedCFG Bool => g.language.Infinite :=
  tm2Decidable_language_infinite

end Cslib.Language.EncodedCFG.EmptinessTests
