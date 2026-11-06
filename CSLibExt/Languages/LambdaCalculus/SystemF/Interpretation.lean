/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.LambdaCalculus.SystemF.Relations
public import CSLibExt.Languages.LambdaCalculus.SystemF.Syntax

/-!
# Impredicative binary interpretation of System F types

A type variable denotes its arbitrary binary relation. Arrows test all related
arguments. A universal type quantifies *all* beta-invariant relations on the
fixed syntactic term model, including interpretations of quantified types.
The quantifier lives in impredicative Prop, without a universe ladder for the
object-language types. No typing or parametricity assumption defines a relation.

## Provenance and adaptation

The variable, arrow, and polymorphic relation clauses adapt Reynolds (1983,
Sections 3 and 8), in the related-environment formulation of Wadler (1989,
Section 6). Here both sides use the same fixed CSLib model of erased untyped
terms: arrows use model application, and forall quantifies all beta-invariant
binary relations on that carrier. This is a syntactic-model interpretation,
not Reynolds' proposed set-theoretic semantics or an all-universes set model.
Its fundamental theorem concerns erased terms modulo full-beta conversion;
no CBV termination or normalization claim is made.

## References

* John C. Reynolds, *Types, Abstraction and Parametric Polymorphism*,
  *Information Processing 83*, R. E. A. Mason (ed.), North-Holland, 1983,
  pp. 513-523, Sections 3 and 8.
* Philip Wadler, *Theorems for free!*, *FPCA '89*, ACM Press, 1989,
  pp. 347-359, Section 6. <https://doi.org/10.1145/99370.99404>
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF.Ty

/-- **Binary logical relation of a System F type.**
The impredicative binary logical relation denoted by a System F type. -/
@[simp] def interpret {n : Nat} : Ty n → (Fin n → Rel) → Rel
  | .var i, ρ => ρ i
  | .arr A B, ρ => Rel.arrow (interpret A ρ) (interpret B ρ)
  | .all B, ρ => Rel.universal (fun R : Rel => interpret B (Fin.cases R ρ))

/-- **Relational interpretation of a renamed System F type.**
Interpreting a renamed type precomposes the relation environment. -/
theorem interpret_rename {n k : Nat} (η : Fin n → Fin k) (A : Ty n)
    (ρ : Fin k → Rel) :
    interpret (rename η A) ρ = interpret A (ρ ∘ η) := by
  induction A generalizing k with
  | var => rfl
  | arr A B ihA ihB => simp only [rename, interpret, ihA, ihB]
  | all B ih =>
    simp only [rename, interpret]
    congr 1
    funext R
    rw [ih]
    congr 1
    funext i
    induction i using Fin.cases <;> rfl

/-- **Relational interpretation of a substituted System F type.**
Type substitution is interpreted by substituting arbitrary relations. -/
theorem interpret_subst {n k : Nat} (σ : Fin n → Ty k) (A : Ty n)
    (ρ : Fin k → Rel) :
    interpret (subst σ A) ρ = interpret A (fun i => interpret (σ i) ρ) := by
  induction A generalizing k with
  | var => rfl
  | arr A B ihA ihB => simp only [subst, interpret, ihA, ihB]
  | all B ih =>
    simp only [subst, interpret]
    congr 1
    funext R
    rw [ih]
    congr 1
    funext i
    induction i using Fin.cases with
    | zero => rfl
    | succ i =>
      simp only [liftSub_succ, interpret_rename]
      rfl

/-- **Relational interpretation of an instantiated System F type.**
Universal instantiation inserts the argument's whole logical relation. -/
theorem interpret_instantiate {n : Nat} (B : Ty (n + 1)) (A : Ty n)
    (ρ : Fin n → Rel) :
    interpret (instantiate B A) ρ =
      interpret B (Fin.cases (interpret A ρ) ρ) := by
  rw [instantiate, interpret_subst]
  congr 1
  funext i
  induction i using Fin.cases <;> rfl

/-- **Relational interpretation of a weakened System F type.**
Weakening a type does not make it depend on the new arbitrary relation. -/
@[simp] theorem interpret_weaken {n : Nat} (A : Ty n) (ρ : Fin n → Rel)
    (R : Rel) : interpret (rename Fin.succ A) (Fin.cases R ρ) =
      interpret A ρ := by
  rw [interpret_rename]
  rfl

end Cslib.Languages.LambdaCalculus.SystemF.Ty
