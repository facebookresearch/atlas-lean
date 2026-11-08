/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.FirstOrder.NaturalDeduction

@[expose] public section

/-!
# Tests for first-order natural deduction

Derivations in the pure-equality language over variables `ℕ`: `∀x. x = x`, an instance of a
universal hypothesis, symmetry and transitivity, and `∃`-introduction. Soundness then
refutes `∀x ∀y. x = y` in the two-element model and shows that `[]` does not derive `⊥`.
-/

set_option autoImplicit false

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

namespace CSLibExtTest.Logics.FirstOrder.NaturalDeduction

/-- Formulas of the pure-equality language with free variables in `ℕ`. -/
abbrev F := Language.empty.Formula ℕ

/-- The body `x = x` of `∀x. x = x`, with `x` the bound variable `0`. -/
private def reflBody : Language.empty.BoundedFormula ℕ 1 :=
  .equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))

private theorem instantiate_reflBody (t : Language.empty.Term ℕ) :
    instantiate t reflBody = t.equal t := by
  simp only [reflBody, instantiate_equal, instantiateTerm_var_zero]
  rfl

/-- `⊢ ∀x. x = x`, by `∀`-introduction at the eigenvariable `0`. -/
example : Derivable ([] : List F) reflBody.all :=
  Derivable.allI (x := 0) (by simp) (by simp [reflBody])
    (instantiate_reflBody _ ▸ Derivable.refl (Term.var 0))

/-- From `∀x. x = x` derive its instance at the variable `7`. -/
example : Derivable [(reflBody.all : F)] ((Term.var 7).equal (Term.var 7)) :=
  instantiate_reflBody _ ▸ Derivable.allE (Term.var 7) (Derivable.ax List.mem_cons_self)

/-- Symmetry and transitivity of equality. -/
example (Γ : List F) (r s t : Language.empty.Term ℕ) (h₁ : Derivable Γ (r.equal s))
    (h₂ : Derivable Γ (t.equal s)) : Derivable Γ (r.equal t) :=
  h₁.trans h₂.symm

/-- `∃`-introduction: `⊢ ∃x. x = x`. -/
example : Derivable ([] : List F) reflBody.ex :=
  Derivable.exI (Term.var 0) (instantiate_reflBody _ ▸ Derivable.refl (Term.var 0))

/-- Weakening with a hypothesis that mentions the eigenvariable `0` of the derivation of
`∀x. x = x`: the eigenvariable is renamed apart. -/
example : Derivable [(Term.var 0).equal (Term.var 1)] (reflBody.all : F) :=
  (Derivable.allI (x := 0) (by simp) (by simp [reflBody])
    (instantiate_reflBody _ ▸ Derivable.refl (Term.var 0))).mono (List.nil_subset _)

/-- The body of `∀x ∀y. x = y`. -/
private def allEqBody : Language.empty.BoundedFormula ℕ 2 :=
  .equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))

/-- Soundness refutes `⊢ ∀x ∀y. x = y` in the two-element model `Bool`. -/
example : ¬ Derivable ([] : List F) allEqBody.all.all := fun h ↦ by
  let _ : Language.empty.Structure Bool := Language.emptyStructure
  have := h.sound (M := Bool) (fun _ ↦ true) (by simp)
  simp only [Formula.Realize, allEqBody, BoundedFormula.Realize, Term.realize_var,
    Sum.elim_inr] at this
  have h01 := this false true
  simp [Fin.snoc] at h01

/-- Relabeling free variables injectively (Mathlib's `Formula.relabel`) keeps derivations. -/
example : Derivable [((Term.var 0).equal (Term.var 1) : F).relabel fun x ↦ x + 5]
    (((Term.var 1).equal (Term.var 0) : F).relabel fun x ↦ x + 5) := by
  have h : Derivable [((Term.var 0).equal (Term.var 1) : F)] ((Term.var 1).equal (Term.var 0)) :=
    (Derivable.ax List.mem_cons_self).symm
  simpa using h.relabel (f := fun x ↦ x + 5) (add_left_injective 5)

/-- Instantiation under a quantifier: the outer bound variable stays index `0`, the inner one
shifts from `1` to `0`. -/
example (t : Language.empty.Term ℕ) :
    instantiate t ((Term.var (Sum.inr 0)).bdEqual (Term.var (Sum.inr 1)) :
      Language.empty.BoundedFormula ℕ 2).all =
      ((t.relabel Sum.inl).bdEqual (Term.var (Sum.inr 0))).all := by
  simp only [instantiate_all, Term.bdEqual, instantiate_equal, instantiateTerm_var_zero]
  rfl

/-- The empty context is consistent. -/
example : ¬ Derivable ([] : List F) ⊥ := not_derivable_nil_bot

end CSLibExtTest.Logics.FirstOrder.NaturalDeduction
