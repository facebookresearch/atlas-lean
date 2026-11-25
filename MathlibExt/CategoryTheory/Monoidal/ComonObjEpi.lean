/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Monoidal.Comon_

/-!
# Descending comonoid laws along epimorphisms

An epimorphism compatible with the source counit and coproduct transfers
the comonoid laws to the target. The target counit and coassociativity
identities follow from the source identities and the two descent
equations.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

universe v u

namespace CategoryTheory.ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {X Y : C} [ComonObj X]

/-- An actual descended comultiplication and counit inherit all comonoid laws from an epic source. -/
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
