/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Languages.ContextFree.GreibachNormalForm

/-!
# Greibach normal form: every context-free grammar has an equivalent one

The statement is registered here as a `theorem_wanted`. The predicate
`Cslib.Language.IsGreibachNormalForm` and the head-symbol lemma
`Cslib.Language.exists_terminal_head_of_output_ne_nil` are proved in
`CSLibExt`. The standard proof goes from Chomsky normal form (proved
in `CSLibExt`, `Cslib.Language.exists_chomskyNormalForm`) through
elimination of left recursion and substitution: order the
nonterminals, substitute earlier nonterminals into later productions,
eliminate direct left recursion with fresh nonterminals, then
back-substitute. Carrying the two language inclusions through those
grammar transformations in Lean is a large construction, beyond the
scope of this lane, so the full equivalence is left as a `theorem_wanted`.
-/

@[expose] public section

namespace Cslib.GreibachNormalFormWanted

open Cslib.Language

/-- Every context-free grammar has an equivalent grammar in Greibach
normal form.
Source: Hopcroft and Ullman, Introduction to Automata Theory,
Languages, and Computation, Addison-Wesley, 1979, Chapter 7
(Greibach normal form); Harrison, Introduction to Formal Language
Theory, Addison-Wesley, 1978, Chapter 4. -/
public theorem_wanted exists_greibachNormalForm {T : Type*}
    (g : ContextFreeGrammar T) :
    ∃ (g' : ContextFreeGrammar T), g'.language = g.language ∧
      IsGreibachNormalForm g'

end Cslib.GreibachNormalFormWanted
