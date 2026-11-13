/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equality-free pH ∧ ¬pH has the finite model property (Open Problem Garden 37863)

Open Problem Garden, Finite entailment of Positive Horn logic (node 37863; B. Martin): Positive Horn
logic (pH) is the fragment of FO involving exactly `∃, ∀, ∧, =`. Does the fragment `pH ∧ ¬pH` have
the finite model property? The page explains: the question is whether there is an infinity axiom of
the form `φ ∧ ¬ψ` with `φ, ψ` in pH, i.e. whether entailment of pH is equivalent to finite
entailment (`φ → ψ` true on all models iff true on all finite models).
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.ModelTheory.Semantics

@[expose] public section

namespace MathlibExt.ModelTheory.PositiveHornFiniteEntailmentOpenGardenProblem37863Wanted

/-!
Source: Open Problem Garden, Finite entailment of Positive Horn logic (node 37863; B. Martin, posted
by L. Segoufin),
http://www.openproblemgarden.org/op/finite_satisfiability_of_positive_horn_logic_entailment.
UnsolvedMath record UM-00003342 (`OPG-37863`), dataset ulamai/UnsolvedMath v1.8.0.

Reading: stated for relational languages (the setting of Chen, Madelaine and Martin, cited by the
page) and for equality-free positive Horn sentences, built from relational atoms by `⊓`, `∀` and
`∃`. This is the fragment covered by the resolving theorem: Bova and Mogavero's positive Herbrand
logic PH (quantified conjunctions of atoms, no equality; its relational fragment is the logic of
quantified conjunctive queries, which Chen, Madelaine and Martin call positive Horn). Not stated:
sentences of pH containing `=` (the page says equality 'may mostly be propagated out by
substitution'), and vocabularies with function or constant symbols. Models are nonempty structures,
as in first-order semantics; a sentence satisfiable in some structure is satisfiable in one whose
carrier is in `Type`.
-/

open FirstOrder FirstOrder.Language

/-- Equality-free positive Horn formulas: the formulas built from relational atoms `R(t₁, …, tₗ)`
by conjunction `⊓` and the quantifiers `∀` (`BoundedFormula.all`) and `∃` (`BoundedFormula.ex`).
No `=`, `⊥`, `¬`, `∨` or `→` occurs (Mathlib encodes `⊓` and `∃` through `→` and `⊥`; this
predicate only admits those encodings of conjunctions and existential quantifiers). -/
inductive IsPositiveHorn {L : Language} {α : Type*} : {n : ℕ} → L.BoundedFormula α n → Prop
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      IsPositiveHorn (BoundedFormula.rel R ts)
  | inf {n : ℕ} {φ ψ : L.BoundedFormula α n} :
      IsPositiveHorn φ → IsPositiveHorn ψ → IsPositiveHorn (φ ⊓ ψ)
  | all {n : ℕ} {φ : L.BoundedFormula α (n + 1)} : IsPositiveHorn φ → IsPositiveHorn φ.all
  | ex {n : ℕ} {φ : L.BoundedFormula α (n + 1)} : IsPositiveHorn φ → IsPositiveHorn φ.ex

/-- Open Problem Garden 37863 (B. Martin), equality-free form: the fragment `pH ∧ ¬pH` has the
finite model property. For every relational language `L` and equality-free positive Horn sentences
`φ`, `ψ`, if `φ ∧ ¬ψ` holds in some nonempty `L`-structure then it holds in a finite nonempty
`L`-structure; equivalently, `φ` entails `ψ` as soon as `φ → ψ` holds in every finite nonempty
structure. -/
def positiveHornFiniteModelProperty : Prop :=
  ∀ (L : FirstOrder.Language.{0, 0}) [L.IsRelational] (φ ψ : L.Sentence),
    IsPositiveHorn φ → IsPositiveHorn ψ →
    (∃ (M : Type) (_ : L.Structure M), Nonempty M ∧ M ⊨ φ ∧ ¬ M ⊨ ψ) →
    ∃ (M : Type) (_ : L.Structure M), Finite M ∧ Nonempty M ∧ M ⊨ φ ∧ ¬ M ⊨ ψ

/--
Resolved true: entailment and finite entailment coincide for equality-free positive Horn sentences,
so every satisfiable sentence `φ ∧ ¬ψ` with `φ, ψ` equality-free positive Horn has a finite model.
Source: Open Problem Garden, Finite entailment of Positive Horn logic (node 37863; B. Martin, posted
by L. Segoufin),
http://www.openproblemgarden.org/op/finite_satisfiability_of_positive_horn_logic_entailment;
resolution: S. Bova and F. Mogavero, Herbrand property, finite quasi-Herbrand models, and a
Chandra-Merlin theorem for quantified conjunctive queries, 32nd Annual ACM/IEEE Symposium on Logic
in Computer Science (LICS 2017), doi:10.1109/LICS.2017.8005073; author copy
https://www.fabiomogavero.com/publications/carticles/2017/bm(lics17).pdf, Section V.A: 'We now prove
that (i) general and finite entailment in PH coincide'; Theorem 9 (PH Entailment) and its proof: for
PH sentences φ₁, φ₂, φ₁ ⊭ φ₂ implies φ₁ ⊭_fin φ₂; Section I: whether entailment and finite
entailment in QCQ coincide 'was left open in [13]' (Chen, Madelaine and Martin, Quantified
constraints and containment problems, the paper cited on the Open Problem Garden page), and footnote
1: PH is the fragment [13] calls positive Horn. The Open Problem Garden page carries the comment
'Solved in LICS 2017' naming this paper, https://doi.org/10.1109/LICS.2017.8005073.
-/
public theorem_wanted positiveHornFiniteModelProperty_holds : positiveHornFiniteModelProperty

end MathlibExt.ModelTheory.PositiveHornFiniteEntailmentOpenGardenProblem37863Wanted
