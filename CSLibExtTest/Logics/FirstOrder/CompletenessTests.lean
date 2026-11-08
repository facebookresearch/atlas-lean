/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.FirstOrder.Completeness

@[expose] public section

/-!
# Tests for Henkin completeness of first-order natural deduction

In the pure-equality language: completeness turns semantic arguments into derivations,
including Peirce's law, which needs the classical rule, and a consequence of hypotheses that
use every variable. Model existence gives a model of a consistent set, and
`provable_iff_models` packages soundness with completeness.
-/

set_option autoImplicit false

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

namespace CSLibExtTest.Logics.FirstOrder.Completeness

/-- Formulas of the pure-equality language with free variables in `ℕ`. -/
abbrev F := Language.empty.Formula ℕ

/-- The empty theory. -/
abbrev T₀ : Language.empty.Theory := ∅

/-- The empty theory's sentences, embedded as formulas over `ℕ`. -/
abbrev H₀ : Set F := Formula.relabel Empty.elim '' T₀

/-- `x = x` is provable, by completeness from its validity. -/
example : Provable H₀ ((Term.var 0).equal (Term.var 0) : F) :=
  provable_of_models (Theory.models_formula_iff.mpr fun _ _ ↦ Formula.realize_equal.mpr rfl)

/-- Peirce's law `((p ⟹ q) ⟹ p) ⟹ p` for atomic `p`, `q` is provable: it is a classical
tautology. -/
example : Provable H₀
    ((((Term.var 0).equal (Term.var 1)).imp ((Term.var 1).equal (Term.var 2))).imp
      ((Term.var 0).equal (Term.var 1)) |>.imp ((Term.var 0).equal (Term.var 1)) : F) :=
  provable_of_models (Theory.models_formula_iff.mpr fun _ _ ↦ by
    simp only [Formula.realize_imp]
    tauto)

/-- `x = y` is not provable: soundness and completeness agree that it fails in `Bool`. -/
example : ¬ Provable H₀ ((Term.var 0).equal (Term.var 1) : F) := by
  rw [provable_iff_models]
  intro h
  let _ : Language.empty.Structure Bool := Language.emptyStructure
  have : (T₀ : Language.empty.Theory).Model Bool := ⟨by simp⟩
  have := Theory.models_formula_iff.mp h ((Theory.ModelType.of T₀ Bool).ulift)
    (fun n ↦ ULift.up (decide (n = 0)))
  have h01 := Formula.realize_equal.mp this
  exact Bool.true_eq_false_eq_False (congrArg ULift.down h01 : true = false)

/-- Model existence for the consistent set `{x₀ = x₁}`. -/
example : ∃ (M : Type) (_ : Language.empty.Structure M) (v : ℕ → M), Nonempty M ∧
    ∀ ψ ∈ ({(Term.var 0).equal (Term.var 1)} : Set F), ψ.Realize v := by
  refine exists_model_of_consistent ?_
  rintro ⟨Γ, hΓ, hd⟩
  let _ : Language.empty.Structure Unit := Language.emptyStructure
  have := hd.sound (M := Unit) (fun _ ↦ ()) fun ψ hψ ↦ by
    rw [Set.mem_singleton_iff.mp (hΓ ψ hψ)]
    exact Formula.realize_equal.mpr rfl
  exact Formula.realize_bot.mp this

/-- Strong completeness with infinitely many free variables in the hypotheses: from
`xᵢ = xᵢ₊₁` for every `i`, derive `x₀ = x₂`. -/
example : Provable (Set.range fun i : ℕ ↦ ((Term.var i).equal (Term.var (i + 1)) : F))
    ((Term.var 0).equal (Term.var 2)) :=
  provable_of_entails fun _ _ v hv ↦ by
    have h₀ := Formula.realize_equal.mp (hv _ ⟨0, rfl⟩)
    have h₁ := Formula.realize_equal.mp (hv _ ⟨1, rfl⟩)
    exact Formula.realize_equal.mpr (h₀.trans h₁)

end CSLibExtTest.Logics.FirstOrder.Completeness
