/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.DecidableModelChecking

/-!
# LTL satisfiability by Büchi nonemptiness

An LTL formula is satisfiable iff its Büchi automaton accepts some word, iff that automaton has
a lasso; with a finite alphabet and a decidable valuation this gives an executable
satisfiability test. Validity is unsatisfiability of the negation.

* `Cslib.LTL.Satisfiable`, `Cslib.LTL.Valid`: satisfiability and validity of a formula under a
  valuation of its atoms on the letters.
* `Cslib.LTL.valid_iff_not_satisfiable_not`: validity is unsatisfiability of the negation.
* `Cslib.LTL.satisfiable_iff_language_ne_bot`, `Cslib.LTL.satisfiable_iff_hasLasso`:
  satisfiability is nonemptiness of the formula's Büchi automaton, and the lasso criterion.
* `Cslib.LTL.satB`, `Cslib.LTL.satB_iff`: an executable satisfiability test.

No complexity bound is claimed; the PSPACE-completeness of LTL satisfiability (Sistla and
Clarke) is not formalized.

## References

* M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for
  Concurrency: Structure versus Automata*, LNCS 1043, Springer, 1996, pp. 238-266,
  Section 4.1 (author's posted version `banff94rj.pdf`).
-/

@[expose] public section

namespace Cslib.LTL

open Automata.NA Automata.ωAcceptor

variable {Atom Symbol : Type*}

/-- **Satisfiable LTL formula.** An LTL formula is satisfiable, for a valuation of its atoms on
the letters, if some infinite word satisfies it (Vardi, "An automata-theoretic approach to
linear temporal logic", LNCS 1043, 1996, Section 4.1, where letters are sets of atoms). -/
def Satisfiable (valuation : Symbol → Atom → Prop) (φ : Formula Atom) : Prop :=
  ∃ w : ωSequence Symbol, Word.Satisfies valuation w φ

/-- **Valid LTL formula.** An LTL formula is valid, for a valuation of its atoms on the
letters, if every infinite word satisfies it (Vardi, "An automata-theoretic approach to linear
temporal logic", LNCS 1043, 1996, Section 4.1). -/
def Valid (valuation : Symbol → Atom → Prop) (φ : Formula Atom) : Prop :=
  ∀ w : ωSequence Symbol, Word.Satisfies valuation w φ

/-- **Validity is unsatisfiability of the negation.** A formula is valid iff its negation is not
satisfiable. -/
theorem valid_iff_not_satisfiable_not (valuation : Symbol → Atom → Prop) (φ : Formula Atom) :
    Valid valuation φ ↔ ¬ Satisfiable valuation (.not φ) := by
  simp only [Valid, Satisfiable, Word.Satisfies.not_iff, not_exists, not_not]

/-- **LTL satisfiability is Büchi nonemptiness.** A formula is satisfiable iff its Büchi
automaton accepts some word (Vardi, "An automata-theoretic approach to linear temporal logic",
LNCS 1043, 1996, Section 4.1, proof of Theorem 24). -/
theorem satisfiable_iff_language_ne_bot (valuation : Symbol → Atom → Prop) (φ : Formula Atom) :
    Satisfiable valuation φ ↔ language (Tableau.buchi valuation φ) ≠ ⊥ := by
  rw [Tableau.language_buchi]
  constructor
  · rintro ⟨w, hw⟩ h
    have hmem : w ∈ Word.language valuation φ := Word.mem_language.mpr hw
    rw [h] at hmem
    exact hmem
  · intro h
    by_contra hn
    apply h
    apply ωLanguage.mem_ext
    intro w
    exact ⟨fun hw => hn ⟨w, Word.mem_language.mp hw⟩, False.elim⟩

/-- **LTL satisfiability by the lasso criterion.** A formula is satisfiable iff its Büchi
automaton has an accepting state reachable from an initial state and lying on a nonempty cycle
(Vardi, "An automata-theoretic approach to linear temporal logic", LNCS 1043, 1996, Theorem 24
with Proposition 13). -/
theorem satisfiable_iff_hasLasso (valuation : Symbol → Atom → Prop) (φ : Formula Atom) :
    Satisfiable valuation φ ↔ (Tableau.buchi valuation φ).HasLasso := by
  rw [← Buchi.language_nonempty_iff_hasLasso]
  exact ⟨fun ⟨w, hw⟩ => ⟨w, (Tableau.mem_buchi_iff valuation φ w).mpr hw⟩,
    fun ⟨w, hw⟩ => ⟨w, (Tableau.mem_buchi_iff valuation φ w).mp hw⟩⟩

section Decidable

variable [Fintype Symbol] (valuation : Symbol → Atom → Prop) [∀ x a, Decidable (valuation x a)]
  (φ : Formula Atom)

/-- **Executable LTL satisfiability test.** For a finite alphabet and a decidable valuation, the
Boolean `satB valuation φ` runs the Büchi emptiness test on the automaton of `φ`. -/
def satB : Bool := by
  letI : DecidablePred (· ∈ (Tableau.buchi valuation φ).start) :=
    Tableau.buchiStartDecidable valuation φ
  letI : DecidablePred (· ∈ (Tableau.buchi valuation φ).accept) :=
    Tableau.buchiAcceptDecidable valuation φ
  exact !(Tableau.buchi valuation φ).isEmptyB

/-- **Correctness of the executable satisfiability test.** `satB valuation φ = true` iff `φ` is
satisfiable. -/
theorem satB_iff : satB valuation φ = true ↔ Satisfiable valuation φ := by
  let : DecidablePred (· ∈ (Tableau.buchi valuation φ).start) :=
    Tableau.buchiStartDecidable valuation φ
  let : DecidablePred (· ∈ (Tableau.buchi valuation φ).accept) :=
    Tableau.buchiAcceptDecidable valuation φ
  rw [satB, Bool.not_eq_true', Bool.eq_false_iff, Ne, Buchi.isEmptyB_iff,
    satisfiable_iff_language_ne_bot]

end Decidable

end Cslib.LTL
