/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.FirstOrder.Consistency

@[expose] public section

/-!
# Tests for consistency, Lindenbaum's lemma and Henkin witnesses

In the pure-equality language over variables `ℕ`: the empty set is consistent, so it has a
maximal consistent extension; that extension contains `x = x`, decides every formula, and
stays consistent after a Henkin axiom with a witness fresh for a consistent set.
-/

set_option autoImplicit false

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

namespace CSLibExtTest.Logics.FirstOrder.Consistency

/-- Formulas of the pure-equality language with free variables in `ℕ`. -/
abbrev F := Language.empty.Formula ℕ

/-- The empty set of hypotheses is consistent. -/
theorem consistent_empty : Consistent (∅ : Set F) := fun ⟨Γ, hΓ, hd⟩ ↦ by
  have : Γ = [] := List.eq_nil_iff_forall_not_mem.mpr fun ψ hψ ↦ hΓ ψ hψ
  subst this
  exact not_derivable_nil_bot hd

/-- A maximal consistent extension of `∅` contains `x = x` and decides `x = y`. -/
example : ∃ Δ : Set F, MaximalConsistent Δ ∧ (Term.var 0).equal (Term.var 0) ∈ Δ ∧
    ((Term.var 0).equal (Term.var 1) ∈ Δ ∨ ((Term.var 0).equal (Term.var 1)).not ∈ Δ) := by
  obtain ⟨Δ, -, hΔ⟩ := exists_maximalConsistent consistent_empty
  refine ⟨Δ, hΔ, hΔ.equal_refl _, ?_⟩
  by_cases h : (Term.var 0).equal (Term.var 1) ∈ Δ
  · exact Or.inl h
  · exact Or.inr (hΔ.not_mem_iff.mpr h)

/-- The body `x = 5` of `∀x. x = 5`. -/
private def body : Language.empty.BoundedFormula ℕ 1 :=
  .equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl 5))

/-- A Henkin axiom for `∀x. x = 5` with the fresh witness `0` keeps `{3 = 3}` consistent. -/
example : Consistent (insert (henkinAxiom body 0)
    ({(Term.var 3).equal (Term.var 3)} : Set F)) := by
  refine Consistent.insert_henkinAxiom ?_ (by simp [Term.equal, Term.bdEqual, Term.varFinsetLeft])
    (by simp [body])
  -- `{3 = 3}` is consistent: it holds in every structure
  rintro ⟨Γ, hΓ, hd⟩
  let _ : Language.empty.Structure Unit := Language.emptyStructure
  have := hd.sound (M := Unit) (fun _ ↦ ()) fun ψ hψ ↦ by
    rw [Set.mem_singleton_iff.mp (hΓ ψ hψ)]
    exact Formula.realize_equal.mpr rfl
  exact Formula.realize_bot.mp this

end CSLibExtTest.Logics.FirstOrder.Consistency
