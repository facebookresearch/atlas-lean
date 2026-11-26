/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Comonoid descent along an epimorphism

In a monoidal category, let `X` be a comonoid and let `q : X → Y` be epic. Suppose maps `δ_Y :
Y → Y ⊗ Y` and `ε_Y : Y → 𝟙` satisfy `q ≫ δ_Y = δ_X ≫ (q ⊗ q)` and `q ≫ ε_Y = ε_X`.

The source comonoid equations imply the counit and coassociativity laws on `Y`, giving a
comonoid structure with the specified descended maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe v u

namespace CategoryTheory.ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y : C} [ComonObj X]

/-- The comonoid structure descended along an epimorphism.

For an epic `q : X → Y` from a comonoid, target comultiplication and counit maps commuting
with `q` inherit both counit laws and coassociativity. -/
def ofEpi (q : X ⟶ Y) [Epi q] (delta : Y ⟶ Y ⊗ Y) (epsilon : Y ⟶ 𝟙_ C)
    (hδ : q ≫ delta = (ComonObj.comul (X := X)) ≫ (q ⊗ₘ q))
    (hε : q ≫ epsilon = (ComonObj.counit (X := X))) : ComonObj Y where
  comul := delta
  counit := epsilon
  counit_comul := by
    apply (cancel_epi q).mp
    calc
      q ≫ (delta ≫ (epsilon ▷ Y)) = (ComonObj.comul (X := X)) ≫ (q ⊗ₘ q) ≫ (epsilon ▷ Y) := by
        rw [← Category.assoc, hδ, Category.assoc]
      _ = (ComonObj.comul (X := X)) ≫ ((q ≫ epsilon) ⊗ₘ q) := by
        rw [tensorHom_comp_whiskerRight]
      _ = (ComonObj.comul (X := X)) ≫ ((ComonObj.counit (X := X)) ⊗ₘ q) := by rw [hε]
      _ = q ≫ (λ_ Y).inv := ComonObj.counit_comul_hom q
  comul_counit := by
    apply (cancel_epi q).mp
    calc
      q ≫ (delta ≫ (Y ◁ epsilon)) = (ComonObj.comul (X := X)) ≫ (q ⊗ₘ q) ≫ (Y ◁ epsilon) := by
        rw [← Category.assoc, hδ, Category.assoc]
      _ = (ComonObj.comul (X := X)) ≫ (q ⊗ₘ (q ≫ epsilon)) := by
        rw [tensorHom_comp_whiskerLeft]
      _ = (ComonObj.comul (X := X)) ≫ (q ⊗ₘ (ComonObj.counit (X := X))) := by rw [hε]
      _ = q ≫ (ρ_ Y).inv := ComonObj.comul_counit_hom q
  comul_assoc := by
    apply (cancel_epi q).mp
    have hleft : (q ⊗ₘ q) ≫ (Y ◁ delta) =
        (X ◁ (ComonObj.comul (X := X))) ≫ (q ⊗ₘ (q ⊗ₘ q)) := by
      rw [tensorHom_comp_whiskerLeft, hδ, ← id_tensorHom,
        tensorHom_comp_tensorHom, Category.id_comp]
    have hright : (q ⊗ₘ q) ≫ (delta ▷ Y) ≫ (α_ Y Y Y).hom =
        ((ComonObj.comul (X := X)) ▷ X) ≫ (α_ X X X).hom ≫ (q ⊗ₘ (q ⊗ₘ q)) := by
      rw [← Category.assoc, tensorHom_comp_whiskerRight, hδ]
      rw [← associator_naturality q q q, ← Category.assoc,
        ← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
    rw [← Category.assoc q delta (Y ◁ delta), hδ, Category.assoc,
      ← Category.assoc q delta ((delta ▷ Y) ≫ (α_ Y Y Y).hom), hδ, Category.assoc,
      hleft, hright]
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ (q ⊗ₘ (q ⊗ₘ q))) (ComonObj.comul_assoc X)

end CategoryTheory.ComonObj
