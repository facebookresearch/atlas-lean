/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tarski's undefinability of truth
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.FirstOrder.Arithmetic
public import WantedExt.TheoryOfComputation.ChurchUndecidabilityWanted

@[expose] public section

namespace Cslib.Logic.TarskiWanted

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

/-- Tarski's undefinability of truth: no formula `τ` with one free variable defines
truth for arithmetic sentences in the standard model `ℕ`, in the semantic sense that
`τ(⌜σ⌝)` holds in `ℕ` exactly when `σ` holds in `ℕ`, for every sentence `σ`. This is
the standard statement: a merely proof-theoretic version (PA proves every
biconditional `τ(⌜σ⌝) ↔ σ`) would not exclude a semantic truth predicate whose
biconditionals happen not to be provable in PA, so the semantic condition is the
one stated here.
The coding `⌜·⌝` is the concrete effective Gödel numbering
`Cslib.Logic.ChurchWanted.codeSentence` (pairing numbering with disjoint constructor
tags, primitive-recursive and computably decodable by unpairing), not an arbitrary
injective code: injectivity alone does not supply the effective substitution and
diagonal properties the proof needs. The proof goes through the diagonal lemma for
this coding to a liar sentence; the diagonal lemma is the missing step, not
formalized here.
Source: A. Tarski, "Der Wahrheitsbegriff in den formalisierten Sprachen", Studia
Philosophica 1 (1936), 261-405; see also H. Enderton, A Mathematical Introduction to
Logic, 2nd ed., Academic Press, 2001, §3.5, and G. Boolos, J. Burgess, R. Jeffrey,
Computability and Logic, 5th ed., Cambridge University Press, 2007, Chapter 19. -/
public theorem_wanted tarski_undefinability_of_truth
    (τ : ArithmeticLanguage.BoundedFormula Empty 1) :
    ¬ ∀ σ : ArithmeticLanguage.Sentence,
      ((ℕ ⊨ instantiate
        (Arithmetic.numeral (Cslib.Logic.ChurchWanted.codeSentence σ)) τ) ↔ (ℕ ⊨ σ))

end Cslib.Logic.TarskiWanted
