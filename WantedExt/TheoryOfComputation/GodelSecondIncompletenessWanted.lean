/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gödel's second incompleteness theorem for Peano arithmetic
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.FirstOrder.Arithmetic
public import CSLibExt.Logics.FirstOrder.Consistency
public import WantedExt.TheoryOfComputation.ChurchUndecidabilityWanted

@[expose] public section

namespace Cslib.Logic.GodelSecondWanted

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

/-- PA provability over the infinite free-variable type `ℕ`: PA's sentences, embedded
as formulas over `ℕ` by `Formula.relabel Empty.elim`, prove a sentence relabeled the
same way. Stating provability over the sentence type itself (`Provable PATheory`) would
instantiate the calculus's free-variable type as `Empty`, and `Derivable.allI` needs an
eigenvariable of that type, so universal introduction would be unavailable and the
relation would not be PA provability. The relabeled form is the repository's standard
provability for theories (`Completeness.lean`, `Provable.models`,
`provable_iff_models`), and it is sound and complete for semantic consequence over
`PATheory`. -/
abbrev PAProvable (σ : ArithmeticLanguage.Sentence) : Prop :=
  Provable (Formula.relabel (Empty.elim : Empty → ℕ) '' Arithmetic.PATheory)
    (Formula.relabel (Empty.elim : Empty → ℕ) σ)

/-- PA consistency, as `¬ PAProvable ⊥`: PA does not prove falsity (in the relabeled
calculus above). -/
abbrev PAConsistent : Prop := ¬ PAProvable ⊥

/-- PA's concrete Gödel coding: the pairing numbering
`Cslib.Logic.ChurchWanted.codeSentence` (disjoint constructor tags, primitive-recursive
and computably decodable by unpairing). -/
abbrev PACode : ArithmeticLanguage.Sentence → ℕ :=
  Cslib.Logic.ChurchWanted.codeSentence

/-- Gödel's second incompleteness theorem for Peano arithmetic, as concrete
arithmetization. There exist a provability formula `prov` (one free variable, the
code of the sentence) and a PA sentence `ConPA` such that, with the concrete coding
`PACode`:
* `prov` represents PA provability: for every sentence `σ`, `PAProvable σ` iff
  `PAProvable (prov(⌜σ⌝))`, and moreover `prov(⌜σ⌝)` is true in `ℕ` iff
  `PAProvable σ` (the formula is a correct truth predicate for PA provability in the
  standard model);
* `prov` satisfies the Hilbert–Bernays–Löb derivability conditions D1–D3, stated
  with `PAProvable` so that they are about actual PA proofs (D1: PA proves
  `prov(⌜σ⌝)` whenever it proves `σ`; D2: PA proves the internalized modus ponens
  for `prov`; D3: PA proves `prov(⌜σ⌝) → prov(⌜prov(⌜σ⌝)⌝)`);
* there is a diagonal fixed point `G` for unprovability,
  `PAProvable (G ↔ ¬ prov(⌜G⌝))`;
* `ConPA` is the concrete consistency sentence `¬ prov(⌜⊥⌝)`;
* if PA is consistent, then PA does not prove `ConPA`.

This is not a wrapper around the already-proved abstract schema
`MetaMathlibExt.hilbert_bernays_lob_second_incompleteness` (`MathlibExt/Logic/
HilbertBernaysLob.lean`): that theorem takes an arbitrary provability operator and
a fixed point as hypotheses, so instantiating it proves only the conditional
implication from D1–D3 + diagonal to unprovability. The content of Gödel's second
theorem for PA is the existence of a provability formula for PA itself satisfying
those conditions, together with the diagonal lemma for PA's concrete coding; that
existence is what is stated here, and it is the arithmetization gap. The proof would
construct `prov` from a formalized proof predicate for PA (e.g. a primitive-recursive
proof-checking predicate, represented in PA) and verify D1–D3 and the diagonal
lemma for it; none of that is formalized here.
Source: K. Gödel, "Über formal unentscheidbare Sätze der Principia Mathematica und
verwandter Systeme I", Monatshefte für Mathematik und Physik 38 (1931), 173-198; see also
H. Enderton, A Mathematical Introduction to Logic, 2nd ed., Academic Press, 2001, §3.5, and
G. Boolos, J. Burgess, R. Jeffrey, Computability and Logic, 5th ed., Cambridge University
Press, 2007, Chapter 18 (Hilbert–Bernays–Löb conditions and the second theorem). -/
public theorem_wanted godel_second_incompleteness :
    ∃ prov : ArithmeticLanguage.BoundedFormula Empty 1,
      ∃ ConPA : ArithmeticLanguage.Sentence,
        (∀ σ : ArithmeticLanguage.Sentence,
          PAProvable σ ↔
            PAProvable (instantiate (Arithmetic.numeral (PACode σ)) prov)) ∧
        (∀ σ : ArithmeticLanguage.Sentence,
          (ℕ ⊨ instantiate (Arithmetic.numeral (PACode σ)) prov) ↔ PAProvable σ) ∧
        (∀ σ : ArithmeticLanguage.Sentence,
          PAProvable σ →
            PAProvable (instantiate (Arithmetic.numeral (PACode σ)) prov)) ∧
        (∀ σ τ : ArithmeticLanguage.Sentence,
          PAProvable
            ((instantiate (Arithmetic.numeral (PACode (σ.imp τ))) prov).imp
              ((instantiate (Arithmetic.numeral (PACode σ)) prov).imp
                (instantiate (Arithmetic.numeral (PACode τ)) prov)))) ∧
        (∀ σ : ArithmeticLanguage.Sentence,
          PAProvable
            ((instantiate (Arithmetic.numeral (PACode σ)) prov).imp
              (instantiate (Arithmetic.numeral
                (PACode (instantiate (Arithmetic.numeral (PACode σ)) prov))) prov))) ∧
        (∃ G : ArithmeticLanguage.Sentence,
          PAProvable
            (G.iff (instantiate (Arithmetic.numeral (PACode G)) prov).not)) ∧
        (ConPA = (instantiate (Arithmetic.numeral (PACode ⊥)) prov).not) ∧
        (PAConsistent → ¬ PAProvable ConPA)

end Cslib.Logic.GodelSecondWanted
