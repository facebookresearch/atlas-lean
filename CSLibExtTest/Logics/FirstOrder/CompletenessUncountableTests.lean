/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.FirstOrder.CompletenessUncountable

@[expose] public section

/-!
# Tests for completeness for arbitrary (possibly uncountable) languages

The language below has uncountably many nullary relation symbols (one per subset of ℕ), so no `Countable` instance for its symbols exists; the general
completeness theorem applies anyway, with no countability hypothesis.
-/

set_option autoImplicit false

open FirstOrder FirstOrder.Language Cslib.Logic.FOL

namespace CSLibExtTest.Logics.FirstOrder.CompletenessUncountable

/-- A language with uncountably many nullary relation symbols, one per subset of ℕ. -/
def uncountableLang : Language where
  Functions _ := Empty
  Relations n := match n with
    | 0 => Set ℕ
    | _ => Empty

/-- The empty set of formulas in the uncountable language is consistent. -/
example : Consistent (∅ : Set (uncountableLang.Formula ℕ)) := by
  rintro ⟨Γ, hΓ, hd⟩
  cases Γ with
  | nil => exact not_derivable_nil_bot hd
  | cons ψ _ => exact (by simp : ψ ∉ (∅ : Set (uncountableLang.Formula ℕ))) (hΓ ψ List.mem_cons_self)

/-- Model existence in the uncountable language, with no countability hypothesis. -/
example : ∃ (M : Type) (_ : uncountableLang.Structure M) (v : ℕ → M), Nonempty M ∧
    ∀ ψ ∈ (∅ : Set (uncountableLang.Formula ℕ)), ψ.Realize v := by
  refine exists_model_of_consistent_general ?_
  rintro ⟨Γ, hΓ, hd⟩
  cases Γ with
  | nil => exact not_derivable_nil_bot hd
  | cons ψ _ => exact (by simp : ψ ∉ (∅ : Set (uncountableLang.Formula ℕ))) (hΓ ψ List.mem_cons_self)

/-- `x = x` is provable in the uncountable language, by general completeness. -/
example : Provable (Formula.relabel Empty.elim '' (∅ : uncountableLang.Theory))
    ((Term.var 0).equal (Term.var 0) : uncountableLang.Formula ℕ) :=
  provable_of_models_general (Theory.models_formula_iff.mpr fun _ _ ↦ Formula.realize_equal.mpr rfl)

end CSLibExtTest.Logics.FirstOrder.CompletenessUncountable
