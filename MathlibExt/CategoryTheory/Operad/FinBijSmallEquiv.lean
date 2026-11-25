/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Operad.FinBijSmallCoreMonoidal

/-!
# Finite coordinates of small finite-bijection arrows

This elementary coordinate equivalence depends only on the small finite-bijection
monoidal groupoid. Tensor powers and degree inclusion share this definition.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory
namespace CategoryTheory.Operad.SmallFinBijGroupoid

/-- The finite equivalence represented by a morphism of the small
finite-bijection groupoid. -/
noncomputable def smallEquivOfHom {A B : SmallFinBijGroupoid}
    (f : A ⟶ B) : Fin A.of.len ≃ Fin B.of.len :=
  (Equiv.ulift.symm : Fin A.of.len ≃ ULift (Fin A.of.len)).trans
    ((FinBijGroupoid.equivOfHom
      (smallFinBijEquivalence.functor.map f)).trans
        (Equiv.ulift : ULift (Fin B.of.len) ≃ Fin B.of.len))

/-- The original symmetric identity has the literal identity finite bijection. -/
@[simp]
theorem smallEquivOfHom_id (A : SmallFinBijGroupoid) :
    smallEquivOfHom (𝟙 A) = Equiv.refl (Fin A.of.len) := by
  apply Equiv.ext
  intro i
  change ULift.down (FinBijGroupoid.equivOfHom
      (smallFinBijEquivalence.functor.map (𝟙 A)) (ULift.up i)) = i
  rw [smallFinBijEquivalence.functor.map_id, FinBijGroupoid.equivOfHom_id]
  rfl

/-- The original symmetric composition is the same source-first finite composition. -/
theorem smallEquivOfHom_comp {A B C : SmallFinBijGroupoid}
    (f : A ⟶ B) (g : B ⟶ C) :
    smallEquivOfHom (f ≫ g) =
      (smallEquivOfHom f).trans (smallEquivOfHom g) := by
  apply Equiv.ext
  intro i
  change ULift.down (FinBijGroupoid.equivOfHom
      (smallFinBijEquivalence.functor.map (f ≫ g)) (ULift.up i)) = _
  rw [smallFinBijEquivalence.functor.map_comp, FinBijGroupoid.equivOfHom_comp]
  rfl

end CategoryTheory.Operad.SmallFinBijGroupoid
