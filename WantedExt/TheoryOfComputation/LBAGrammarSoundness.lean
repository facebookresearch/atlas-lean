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

namespace Cslib.LBAGrammarSoundnessWanted

/-- **Soundness of the grammar of an LBA**: if the grammar
`M.lbaGrammar` derives a nonempty word `w`, the LBA accepts `w`.
Together with `lba_accepts_implies_grammar_derives` in
`CSLibExt/Computability/Languages/ContextSensitive/LBA.lean` (the
proved completeness inclusion), this gives equality of the LBA
language and the grammar language on nonempty words. Not proved
here: a proof would need an invariant over grammar derivations
tracking a reachable configuration through every interleaving of
generation, activation, simulation, and conversion, with the
boundary tags of the cells read against the eventual word length;
no such invariant is claimed in `CSLibExt`. Source: Sipser,
*Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013,
§5.1; Hopcroft-Motwani-Ullman, *Introduction to Automata Theory,
Languages, and Computation*, 3rd ed., Pearson, 2007, §11.1. -/
theorem_wanted lba_grammar_derives_implies_accepts :
  ∀ {Q Γ : Type*} [DecidableEq Q] [DecidableEq Γ] [Fintype Q] [Fintype Γ]
    (M : Cslib.Language.LinearBoundedAutomaton Q Γ) {w : List Γ},
    w ≠ [] → w ∈ Cslib.Language.language M.lbaGrammar →
    Cslib.Language.LinearBoundedAutomaton.Accepts (M := M) w

end Cslib.LBAGrammarSoundnessWanted
