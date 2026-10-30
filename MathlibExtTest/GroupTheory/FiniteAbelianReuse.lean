/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
Canonical finite and finitely generated abelian decompositions. These tests do not assert
invariant-factor order or uniqueness.
-/

set_option autoImplicit false
noncomputable section
open scoped DirectSum

example (A : Type*) [AddCommGroup A] [Finite A] :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime (p i))
      (e : ι → ℕ), Nonempty (A ≃+ ⨁ i : ι, ZMod (p i ^ e i)) :=
  AddCommGroup.equiv_directSum_zmod_of_finite A

example (A : Type*) [AddCommGroup A] [AddGroup.FG A] :
    ∃ (n : ℕ) (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, Nat.Prime (p i))
      (e : ι → ℕ), Nonempty (A ≃+ (Fin n →₀ ℤ) × ⨁ i : ι, ZMod (p i ^ e i)) :=
  AddCommGroup.equiv_free_prod_directSum_zmod A

#print axioms AddCommGroup.equiv_directSum_zmod_of_finite
#print axioms AddCommGroup.equiv_free_prod_directSum_zmod

end
