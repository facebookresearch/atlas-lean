/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FiniteAbelian.Torsion

open scoped DirectSum

set_option autoImplicit false

-- The torsion-free and finite examples both use the public importing-client API.
example : Finite (AddCommGroup.torsion ℤ) := AddCommGroup.finite_torsion_of_fg ℤ
example : Finite (AddCommGroup.torsion (ZMod 6)) := AddCommGroup.finite_torsion_of_fg (ZMod 6)

example : ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, 0 < d i),
    Nonempty (AddCommGroup.torsion (ZMod 6) ≃+ (⨁ i : Fin n, ZMod (d i))) :=
  AddCommGroup.torsion_equiv_directSum_zmod_of_fg (ZMod 6)

-- Exact archived theorem type, now discharged by the topic-library result.
example (A : Type*) [AddCommGroup A] [AddGroup.FG A] :
    ∃ (n : ℕ) (d : Fin n → ℕ) (_ : ∀ i, 0 < d i),
      Nonempty (AddCommGroup.torsion A ≃+ (⨁ i : Fin n, ZMod (d i))) :=
  AddCommGroup.torsion_equiv_directSum_zmod_of_fg A

#print axioms AddCommGroup.fg_torsion
#print axioms AddCommGroup.finite_torsion_of_fg
#print axioms AddCommGroup.torsion_equiv_directSum_zmod_of_fg
