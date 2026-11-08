/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.ContextFree.Yields

/-!
# Ordinary-client tests for the yields characterization
-/

public section

namespace Cslib.Language.ContextFreeYieldsTests

theorem nil_yields (g : ContextFreeGrammar ℕ) : Yields g [] [] :=
  Yields.nil

theorem yields_iff (g : ContextFreeGrammar ℕ) (u : List (Symbol ℕ g.NT)) (w : List ℕ) :
    Yields g u w ↔ g.Derives u (w.map Symbol.terminal) :=
  yields_iff_derives

theorem mem_language (g : ContextFreeGrammar ℕ) (w : List ℕ) :
    w ∈ g.language ↔ Yields g [Symbol.nonterminal g.initial] w :=
  mem_language_iff_yields

theorem append_yields (g : ContextFreeGrammar ℕ)
    {u v : List (Symbol ℕ g.NT)} {w₁ w₂ : List ℕ}
    (hu : Yields g u w₁) (hv : Yields g v w₂) : Yields g (u ++ v) (w₁ ++ w₂) :=
  hu.append hv

end Cslib.Language.ContextFreeYieldsTests
