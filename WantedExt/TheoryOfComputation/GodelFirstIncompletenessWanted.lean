/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gödel's first incompleteness theorem for Peano arithmetic
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.FirstOrder.Arithmetic
public import CSLibExt.Logics.FirstOrder.Consistency

@[expose] public section

namespace Cslib.Logic.GodelFirstWanted

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

/-- Gödel's first incompleteness theorem: if Peano arithmetic is consistent, there is a
sentence true in the standard model `ℕ` that PA neither proves nor refutes. The
sentence is the Gödel sentence, which asserts its own unprovability; its truth
follows from its unprovability together with soundness of PA in `ℕ`. Provability and
consistency are the relabeled relations `PAProvable` / `PAConsistent` above, over the
infinite free-variable type `ℕ`.
Source: K. Gödel, "Über formal unentscheidbare Sätze der Principia Mathematica und
verwandter Systeme I", Monatshefte für Mathematik und Physik 38 (1931), 173-198; see also
H. Enderton, A Mathematical Introduction to Logic, 2nd ed., Academic Press, 2001, §3.5, and
G. Boolos, J. Burgess, R. Jeffrey, Computability and Logic, 5th ed., Cambridge University
Press, 2007, Chapter 17. -/
public theorem_wanted godel_first_incompleteness
    (hcons : PAConsistent) :
    ∃ σ : ArithmeticLanguage.Sentence, (ℕ ⊨ σ) ∧ ¬ PAProvable σ ∧
      ¬ PAProvable σ.not

end Cslib.Logic.GodelFirstWanted
