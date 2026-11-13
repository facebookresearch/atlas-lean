/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Languages.ContextFree.InherentAmbiguity

@[expose] public section

set_option autoImplicit false

namespace Cslib.InherentAmbiguityWanted

/-- **Inherent ambiguity of `{a ^ i b ^ j c ^ k | i = j or j = k}`**: every context-free
grammar generating `Cslib.Language.inherentlyAmbiguousLang` is ambiguous, in the sense
of `Cslib.Language.IsAmbiguous` (some word has two different leftmost derivations).
The context-free half is proved in CSLibExt as
`Cslib.Language.inherentlyAmbiguousLang_isContextFree`; what remains is the
derivation-tree pumping argument (a grammar for the language must give two different
parse trees to some word `a ^ n b ^ n c ^ n`).
Source: S. Ginsburg, The Mathematical Theory of Context-Free Languages, McGraw-Hill, 1966;
J. E. Hopcroft and J. D. Ullman, Introduction to Automata Theory, Languages, and
Computation, Addison-Wesley, 1979, Chapter 7. -/
theorem_wanted inherently_ambiguous_example :
  ∀ g : ContextFreeGrammar (Fin 3), g.language =
    Cslib.Language.inherentlyAmbiguousLang → Cslib.Language.IsAmbiguous g

end Cslib.InherentAmbiguityWanted
