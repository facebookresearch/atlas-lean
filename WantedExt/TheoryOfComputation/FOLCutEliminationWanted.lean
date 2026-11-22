/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gentzen cut elimination for first-order logic
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Logics.FirstOrder.Syntax
public import Mathlib.ModelTheory.Syntax

@[expose] public section

namespace Cslib.Logic.FOLCutEliminationWanted

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

variable {L : FirstOrder.Language} {α : Type*} [DecidableEq α] [Infinite α]

/-- A Gentzen sequent calculus for classical first-order logic over the repository's
natural deduction syntax (`BoundedFormula`), with an explicit cut rule. The rules mirror
the repository's natural deduction calculus `Derivable`: `ax`, `botE`, `impR`/`impL`,
`allR`/`allL`, classical reductio (`byContra`, matching `Derivable.byContra`), and the
equality rules (`refl`, `subst`, matching `Derivable.refl`/`Derivable.subst`) for
Mathlib's built-in equality. Contexts are lists of formulas. -/
inductive Sequent : List (L.Formula α) → L.Formula α → Prop
  /-- Assumption. -/
  | ax {Γ : List (L.Formula α)} {φ : L.Formula α} : φ ∈ Γ → Sequent Γ φ
  /-- Ex falso: from `⊥` in the context, conclude anything. -/
  | botE {Γ : List (L.Formula α)} {φ : L.Formula α} : ⊥ ∈ Γ → Sequent Γ φ
  /-- `⟹`-introduction: discharge the antecedent. -/
  | impR {Γ : List (L.Formula α)} {φ ψ : L.Formula α} :
      Sequent (φ :: Γ) ψ → Sequent Γ (φ.imp ψ)
  /-- `⟹`-elimination on the left. -/
  | impL {Γ : List (L.Formula α)} {φ ψ χ : L.Formula α} :
      Sequent Γ φ → Sequent (ψ :: Γ) χ → Sequent ((φ.imp ψ) :: Γ) χ
  /-- `∀`-introduction with an eigenvariable free neither in the context nor in the body. -/
  | allR {Γ : List (L.Formula α)} {φ : L.BoundedFormula α 1} {x : α} :
      (∀ ψ ∈ Γ, x ∉ ψ.freeVarFinset) → x ∉ φ.freeVarFinset →
        Sequent Γ (instantiate (Term.var x) φ) → Sequent Γ φ.all
  /-- `∀`-elimination on the left. -/
  | allL {Γ : List (L.Formula α)} {φ : L.BoundedFormula α 1} {ψ : L.Formula α}
      (t : L.Term α) :
      Sequent ((instantiate t φ) :: Γ) ψ → Sequent (φ.all :: Γ) ψ
  /-- Classical reductio ad absurdum. -/
  | byContra {Γ : List (L.Formula α)} {φ : L.Formula α} :
      Sequent (φ.not :: Γ) ⊥ → Sequent Γ φ
  /-- Reflexivity of equality. -/
  | refl {Γ : List (L.Formula α)} (t : L.Term α) : Sequent Γ (t.equal t)
  /-- Substitution of equals into a one-variable body. -/
  | subst {Γ : List (L.Formula α)} {φ : L.BoundedFormula α 1} {s t : L.Term α} :
      Sequent Γ (s.equal t) → Sequent Γ (instantiate s φ) → Sequent Γ (instantiate t φ)
  /-- Cut: a lemma may be used as a hypothesis. -/
  | cut {Γ : List (L.Formula α)} {φ ψ : L.Formula α} :
      Sequent Γ φ → Sequent (φ :: Γ) ψ → Sequent Γ ψ

/-- The cut-free fragment of the sequent calculus: the same rules with the cut rule
removed (classical reductio and the equality rules stay: they are not cuts). -/
inductive CutFreeSequent : List (L.Formula α) → L.Formula α → Prop
  /-- Assumption. -/
  | ax {Γ : List (L.Formula α)} {φ : L.Formula α} : φ ∈ Γ → CutFreeSequent Γ φ
  /-- Ex falso: from `⊥` in the context, conclude anything. -/
  | botE {Γ : List (L.Formula α)} {φ : L.Formula α} : ⊥ ∈ Γ → CutFreeSequent Γ φ
  /-- `⟹`-introduction: discharge the antecedent. -/
  | impR {Γ : List (L.Formula α)} {φ ψ : L.Formula α} :
      CutFreeSequent (φ :: Γ) ψ → CutFreeSequent Γ (φ.imp ψ)
  /-- `⟹`-elimination on the left. -/
  | impL {Γ : List (L.Formula α)} {φ ψ χ : L.Formula α} :
      CutFreeSequent Γ φ → CutFreeSequent (ψ :: Γ) χ → CutFreeSequent ((φ.imp ψ) :: Γ) χ
  /-- `∀`-introduction with an eigenvariable free neither in the context nor in the body. -/
  | allR {Γ : List (L.Formula α)} {φ : L.BoundedFormula α 1} {x : α} :
      (∀ ψ ∈ Γ, x ∉ ψ.freeVarFinset) → x ∉ φ.freeVarFinset →
        CutFreeSequent Γ (instantiate (Term.var x) φ) → CutFreeSequent Γ φ.all
  /-- `∀`-elimination on the left. -/
  | allL {Γ : List (L.Formula α)} {φ : L.BoundedFormula α 1} {ψ : L.Formula α}
      (t : L.Term α) :
      CutFreeSequent ((instantiate t φ) :: Γ) ψ → CutFreeSequent (φ.all :: Γ) ψ
  /-- Classical reductio ad absurdum. -/
  | byContra {Γ : List (L.Formula α)} {φ : L.Formula α} :
      CutFreeSequent (φ.not :: Γ) ⊥ → CutFreeSequent Γ φ
  /-- Reflexivity of equality. -/
  | refl {Γ : List (L.Formula α)} (t : L.Term α) : CutFreeSequent Γ (t.equal t)
  /-- Substitution of equals into a one-variable body. -/
  | subst {Γ : List (L.Formula α)} {φ : L.BoundedFormula α 1} {s t : L.Term α} :
      CutFreeSequent Γ (s.equal t) → CutFreeSequent Γ (instantiate s φ) →
        CutFreeSequent Γ (instantiate t φ)

/-- Gentzen's Hauptsatz (cut elimination) for the classical sequent calculus above:
every sequent derivable with cut is derivable without cut. The usual proof is by
double induction on the rank (complexity of the cut formula) and the height of the
derivation, eliminating a topmost cut.
Source: G. Gentzen, "Untersuchungen über das logische Schließen I", Mathematische
Zeitschrift 39 (1935), 176-210; see also H. Enderton, A Mathematical Introduction to
Logic, 2nd ed., Academic Press, 2001, §2.5, and S. Buss, "An Introduction to Proof
Theory", in Handbook of Proof Theory, Elsevier, 1998, §2. -/
public theorem_wanted fol_cut_elimination {Γ : List (L.Formula α)} {φ : L.Formula α}
    (h : Sequent Γ φ) : CutFreeSequent Γ φ

end Cslib.Logic.FOLCutEliminationWanted
