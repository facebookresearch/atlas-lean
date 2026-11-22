/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Encoded

/-!
# Tests for encoded context-free grammars

* The grammar `S → true S false | ε` as an encoded grammar generates
  `[true, false]`, through its decoded `ContextFreeGrammar`.
* Encoded grammars are `Primcodable`: encoding and decoding round-trip, and
  building a grammar from a start symbol and productions is primitive
  recursive, as is reading off the number of productions.
* Every context-free language has an encoded grammar.
-/

@[expose] public section

namespace Cslib.Language.EncodedCFG.Tests

/-- `S → true S false | ε`, with `S` numbered `0`. -/
def anbn : EncodedCFG Bool :=
  ⟨0, [(0, [.inr true, .inl 0, .inr false]), (0, [])]⟩

example : [true, false] ∈ anbn.language := by
  rw [mem_language_iff]
  have h₁ : decodeRule (0, [.inr true, .inl 0, .inr false]) ∈ anbn.toCFG.rules :=
    mem_toCFG_rules.2 ⟨_, List.mem_cons_self .., rfl⟩
  have h₂ : decodeRule ((0, []) : ℕ × List (ℕ ⊕ Bool)) ∈ anbn.toCFG.rules :=
    mem_toCFG_rules.2 ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl⟩
  have hmid : anbn.toCFG.Produces [Symbol.nonterminal anbn.start]
      [.terminal true, .nonterminal 0, .terminal false] :=
    ⟨_, h₁, ContextFreeRule.Rewrites.input_output⟩
  have hend : anbn.toCFG.Produces [.terminal true, .nonterminal 0, .terminal false]
      ([true, false].map Symbol.terminal) :=
    ⟨_, h₂, ContextFreeRule.rewrites_of_exists_parts _ [.terminal true] [.terminal false]⟩
  exact hmid.single.trans_produces hend

example : Encodable.decode (Encodable.encode anbn) = some anbn :=
  Encodable.encodek anbn

example : Primrec₂ (EncodedCFG.mk (T := Bool)) := primrec₂_mk

/-- The number of productions of an encoded grammar is primitive recursive. -/
example : Primrec fun g : EncodedCFG Bool => g.rules.length :=
  Primrec.list_length.comp primrec_rules

example {L : Language Bool} (hL : L.IsContextFree) : ∃ g : EncodedCFG Bool, g.language = L :=
  isContextFree_iff.1 hL

end Cslib.Language.EncodedCFG.Tests
