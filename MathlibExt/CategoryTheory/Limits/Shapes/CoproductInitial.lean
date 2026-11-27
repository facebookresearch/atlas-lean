/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Coproducts with initial summands

These constructions use the actual coproduct desc and coprojection maps.
They assume only the particular coproduct and initiality of its designated
summands, in an arbitrary category with independent object and Hom universes.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe vC uC

namespace CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C]

/-- A coproduct of initial objects is initial. -/
noncomputable def coproductIsInitialOfEach
    {β : Type*} (F : β → C) [HasCoproduct F]
    (hF : ∀ b, IsInitial (F b)) : IsInitial (∐ F) :=
  IsInitial.ofUniqueHom
    (fun Y => Sigma.desc fun b => (hF b).to Y)
    (fun Y f => by
      apply Sigma.hom_ext
      intro b
      exact (hF b).hom_ext _ _)

/-- A coproduct with only one possibly noninitial summand identifies with that summand. -/
noncomputable def coproductIsoOfInitialExcept
    {β : Type*} (F : β → C) [HasCoproduct F] (b₀ : β)
    (hF : ∀ b, b ≠ b₀ → IsInitial (F b)) : (∐ F) ≅ F b₀ := by
  classical
  let leg (b : β) : F b ⟶ F b₀ :=
    if hb : b = b₀ then eqToHom (congrArg F hb) else (hF b hb).to _
  let hom : (∐ F) ⟶ F b₀ := Sigma.desc leg
  let inv : F b₀ ⟶ ∐ F := Sigma.ι F b₀
  exact
    { hom := hom
      inv := inv
      hom_inv_id := by
        apply Sigma.hom_ext
        intro b
        by_cases hb : b = b₀
        · subst b
          simp [hom, inv, leg]
        · exact (hF b hb).hom_ext _ _
      inv_hom_id := by
        simp [hom, inv, leg] }

end CategoryTheory.Limits
