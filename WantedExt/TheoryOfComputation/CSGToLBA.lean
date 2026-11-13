/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Languages.ContextSensitive.LBA

@[expose] public section

set_option autoImplicit false

namespace Cslib.CSGToLBAWanted

/-- **Every context-sensitive grammar over a finite alphabet has an LBA
recognizing it**: for every grammar `g` over a finite `Γ` with
`IsContextSensitive g`, there is a finite tape alphabet `Sigma` with an
input embedding `emb : Γ → Sigma` (the machine reads inputs as embedded
symbols and writes only symbols of `Sigma`) and a nondeterministic
linear bounded automaton over `Sigma` whose language, read back through
the embedding, is exactly the grammar's language. The finiteness of the
terminal alphabet is part of the statement, following the textbook
convention that alphabets are finite: quantifying an injection from an
arbitrary `Γ` into a finite type would have forced `Γ` to be finite
anyway, which a vacuous grammar over `Γ = ℕ` would have made false.
`CSGrammar` itself is the unrestricted grammar structure, so the
context-sensitivity hypothesis is essential: without it the claim
would cover shrinking (type-0) grammars, whose languages need not be
LBA-recognizable. The tape alphabet is quantified because the cited
reverse-derivation construction must store grammar nonterminals and
auxiliary markers on the tape, which the input terminals plus one blank
cannot hold: the machine's writable alphabet is `Option Sigma`, not
`Option Γ`. This is the context-sensitive-grammar-to-LBA direction of
the LBA/context-sensitive equivalence (the reverse-derivation LBA: the
machine nondeterministically runs the grammar's productions backwards
from the input word to the start symbol, staying inside the input's
`n` cells). The LBA observes the tape boundaries: its transition
function sees the boundary tag (`LBABoundary`) of the head position,
and the grammar-construction cells carry the same tag. This is
essential, not incidental: a boundary-blind machine has every
accepting run on `w` replay on every `w ++ v`, so it could not
recognize e.g. the `[true]`-only language of the sole-rule grammar
`S → true`.
The opposite direction is partly proved in
`CSLibExt/Computability/Languages/ContextSensitive/LBA.lean`
(`lba_accepts_implies_grammar_derives`: an LBA accepting a nonempty word
implies the grammar derives it). The other half of that direction
(if the grammar derives a nonempty word, the LBA accepts it) is the
separate wanted theorem `lba_grammar_derives_implies_accepts` in
`WantedExt/TheoryOfComputation/LBAGrammarSoundness.lean`; no
soundness invariant for it is claimed in `CSLibExt`.
Source: Sipser, *Introduction to the Theory of Computation*, 3rd ed.,
Cengage, 2013, §5.1; Hopcroft-Motwani-Ullman, *Introduction to Automata
Theory, Languages, and Computation*, 3rd ed., Pearson, 2007, §11.1. -/
theorem_wanted csg_implies_lba :
  ∀ {Γ N : Type*} [DecidableEq Γ] [Finite Γ] (g : Cslib.Language.CSGrammar Γ N),
    Cslib.Language.IsContextSensitive g →
    ∃ (Sigma : Type*) (_ : DecidableEq Sigma) (_ : Finite Sigma) (emb : Γ → Sigma),
      Function.Injective emb ∧
      ∃ (Q : Type*) (_ : Finite Q)
      (M : Cslib.Language.LinearBoundedAutomaton Q Sigma),
        Cslib.Language.language g =
          {w | ∃ w' : List Sigma, w' = w.map emb ∧
            Cslib.Language.LinearBoundedAutomaton.Accepts (M := M) w'}

end Cslib.CSGToLBAWanted
