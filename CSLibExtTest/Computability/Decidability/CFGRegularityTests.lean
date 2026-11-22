/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.CFGRegularity

@[expose] public section

/-!
# Tests for the undecidability of regularity of context-free languages
-/

set_option autoImplicit false

open Cslib.Language Cslib.Decidability Cslib.Decidability.Regularity

namespace CSLibExtTest.Computability.Decidability.CFGRegularity

/-- `{0ⁿ1ⁿ}` is not regular. -/
example : ¬zeroOne.IsRegular := not_isRegular_zeroOne

/-- `a # 01` is in `regLang ∅`, through the `0ⁿ1ⁿ` branch. -/
example : [tl true, sep, bl false, bl true] ∈ regLang (0 : Language Bool) :=
  ⟨[true], [false, true], rfl, Or.inr ⟨1, rfl⟩⟩

/-- `regLang L` is regular iff `L` is every word: `regLang ∅` is not regular. -/
example : ¬(regLang (0 : Language Bool)).IsRegular := fun h ↦
  (isRegular_regLang_iff.mp h []).elim

/-- The grammar of all words maps to a grammar with a regular language. -/
example : (regGrammar (allWordsCFG (T := Bool))).language.IsRegular :=
  (univ_iff_isRegular _).mp mem_language_allWordsCFG

/-- The language of `regGrammar g` is `regLang L(g)`. -/
example (g : EncodedCFG Bool) : (regGrammar g).language = regLang g.language :=
  language_regGrammar g

/-- Regularity of context-free languages is undecidable. -/
example : ∃ (T : Type) (_ : Fintype T) (_ : Primcodable T) (_ : DecidableEq T),
    ¬TM2Decidable fun g : EncodedCFG T ↦ g.language.IsRegular :=
  exists_not_tm2Decidable_isRegular

end CSLibExtTest.Computability.Decidability.CFGRegularity
