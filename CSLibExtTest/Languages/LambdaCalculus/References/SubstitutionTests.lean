/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.References.Substitution

/-!
# Tests for renaming and substitution in the calculus with references

* `simp` evaluates substitution through binders with the constructor
  equations: substituting a location for variable `0` reaches the occurrence
  under a `λ` (index `1` there), and locations are untouched.
* The composition laws on a concrete term.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.References.SubstitutionTests

open Term

example : (Term.app (.var 0) (.lam .unit (.var 1)) : Term Empty).instantiate (.loc 3) =
    .app (.loc 3) (.lam .unit (.loc 3)) := by
  simp [instantiate]

/-- Variable `0` under a binder is the bound variable and is not replaced. -/
example : (Term.lam .unit (.var 0) : Term Empty).instantiate (.loc 3) =
    .lam .unit (.var 0) := by
  simp [instantiate]

/-- Locations are not variables. -/
example (σ : Nat → Term Empty) (ρ : Nat → Nat) :
    subst σ (rename ρ (.assign (.loc 1) .unit)) = .assign (.loc 1) .unit := by
  simp

example (ρ ρ' : Nat → Nat) :
    rename ρ' (rename ρ (.lam .unit (.app (.var 0) (.var 2)) : Term Empty)) =
      rename (ρ' ∘ ρ) (.lam .unit (.app (.var 0) (.var 2))) :=
  rename_rename ρ ρ' _

example (σ τ : Nat → Term Empty) (t : Term Empty) :
    subst τ (subst σ t) = subst (fun x => subst τ (σ x)) t :=
  subst_subst σ τ t

end Cslib.Languages.LambdaCalculus.References.SubstitutionTests
