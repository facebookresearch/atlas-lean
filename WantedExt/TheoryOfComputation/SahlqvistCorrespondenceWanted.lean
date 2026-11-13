/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sahlqvist correspondence
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.Modal.Sahlqvist
public import CSLibExt.Logics.Modal.StandardTranslation
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace Cslib.Logic.SahlqvistWanted

open FirstOrder FirstOrder.Language Cslib.Modal

/-- Sahlqvist correspondence: every Sahlqvist modal formula has a first-order frame
correspondent. "Sahlqvist" here is `IsSahlqvist`: Sahlqvist implications closed
under `∧`, `□`, and `∨` with disjoint atoms (`Formula.atoms`); there is no outer `◇`
closure and no arbitrary disjunction. For a Sahlqvist formula `φ`, there is a
sentence `ψ` over the frame language (binary `R` only) such that, for every frame
`(W, rel)`, `ψ` holds in the
frame iff `φ` holds at every world under every valuation on that frame. The
quantification over valuations `val` and worlds `w` is on the right side of the
`iff`: `ψ` is a fixed frame sentence, and it must not depend on a single pointed
model (a single valuation can flip `φ`, e.g. axiom B on a non-symmetric frame).
Correspondence alone is what is stated here: canonicity and completeness are
separate claims, not asserted by this statement.
Source: H. Sahlqvist, "Completeness and Correspondence in the First and Second Order
Semantics for Modal Logic", in Proceedings of the Third Scandinavian Logic Symposium,
North-Holland, 1975, 110-143; see also P. Blackburn, M. de Rijke, Y. Venema, Modal
Logic, Cambridge University Press, 2001, §3.6. -/
public theorem_wanted sahlqvist_correspondence {Atom : Type}
    (φ : Cslib.Modal.Formula Atom) (hφ : IsSahlqvist φ) :
    ∃ ψ : frameLanguage.Sentence,
      ∀ (W : Type) (rel : W → W → Prop),
        @Sentence.Realize frameLanguage W (frameStructure rel) ψ ↔
        ∀ (val : W → Atom → Prop) (w : W),
          (⟨⟨w⟩, rel, val⟩ : Cslib.Modal.KripkeModel W Atom).Satisfies w φ

end Cslib.Logic.SahlqvistWanted
