/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Limits.Shapes.IteratedProducts

open CategoryTheory Limits

noncomputable section

universe u v w₁ w₂

namespace IteratedProductsClients

variable {C : Type u} [Category.{v} C]
  {I : Type w₁} {K : I → Type w₂} {X : (i : I) → K i → C}
  [∀ i, HasProduct (X i)] [HasProduct (fun i => ∏ᶜ X i)]
  [HasProduct (fun p : Σ i, K i => X p.1 p.2)]

-- The complete maps and isomorphism agree with the canonical Mathlib data,
-- with all original existence hypotheses and universe parameters present.
example : chosenPiPiHom (X := X) = (piPiIso K X).inv := rfl

example : chosenPiPiInv (X := X) = (piPiIso K X).hom := rfl

example : chosenPiPiIso (X := X) = (piPiIso K X).symm := rfl

-- The remaining first-projection rule and Mathlib's lift rule normalize both
-- generic two-projection expressions without the redundant simp attributes.
example (i : I) (j : K i) {Z : C} (f : X i j ⟶ Z) :
    chosenPiPiHom (X := X) ≫ Pi.π (fun i => ∏ᶜ X i) i ≫ Pi.π (X i) j ≫ f =
      Pi.π (fun p : Σ i, K i => X p.1 p.2) ⟨i, j⟩ ≫ f := by
  simp only [chosenPiPiHom_π_assoc, Pi.lift_comp_π_assoc]

example (i : I) (j : K i) :
    chosenPiPiHom (X := X) ≫ Pi.π (fun i => ∏ᶜ X i) i ≫ Pi.π (X i) j =
      Pi.π (fun p : Σ i, K i => X p.1 p.2) ⟨i, j⟩ := by
  simp only [chosenPiPiHom_π_assoc, Pi.lift_comp_π]

-- Naturality is exercised with actual componentwise product maps. No
-- invertibility of the component morphisms or supplied comparison is assumed.
example {Y : (i : I) → K i → C}
    [∀ i, HasProduct (Y i)] [HasProduct (fun i => ∏ᶜ Y i)]
    [HasProduct (fun p : Σ i, K i => Y p.1 p.2)]
    (f : ∀ i j, X i j ⟶ Y i j) :
    Limits.Pi.map (fun p : Σ i, K i => f p.1 p.2) ≫ chosenPiPiHom (X := Y) =
      chosenPiPiHom (X := X) ≫ Limits.Pi.map (fun i => Limits.Pi.map (f i)) := by
  apply chosenPiPiHom_naturality (Equiv.refl I) (fun i => Equiv.refl (K i)) f
  · intro i j
    dsimp only [Equiv.refl]
    simp only [Pi.map_π]
    rfl
  · intro i j
    dsimp only [Equiv.refl]
    simp only [Pi.map_π_assoc, Pi.map_π]
    rfl

end IteratedProductsClients

namespace UniqueProductClients

variable {C : Type u} [Category.{v} C] {β : Type w₁} [Unique β]

-- Every index is permitted, including one supplied independently of default.
example (f : β → C) (b : β) :
    (productUniqueIso f).hom =
      Pi.π f b ≫ eqToHom (congrArg f (Subsingleton.allEq b default)) := by
  obtain rfl := Subsingleton.allEq b default
  simp only [productUniqueIso_hom, eqToHom_refl, Category.comp_id]

example (f : β → C) (b : β) {Z : C} (g : f default ⟶ Z) :
    (productUniqueIso f).hom ≫ g =
      Pi.π f b ≫ eqToHom (congrArg f (Subsingleton.allEq b default)) ≫ g := by
  obtain rfl := Subsingleton.allEq b default
  simp only [productUniqueIso_hom, eqToHom_refl, Category.id_comp]

end UniqueProductClients

namespace EmptyFiberClients

variable {C : Type u} [Category.{v} C] [HasProducts C]

-- One fiber has no elements, while the other has one. The map still retains
-- the genuine nonempty leaf and its original inner and outer projections.
private def fiber : Bool → Type
  | false => Empty
  | true => Unit

example (Z : C) :
    chosenPiPiHom (X := fun b (_ : fiber b) => Z) ≫
        Pi.π (fun b => ∏ᶜ fun (_ : fiber b) => Z) true ≫
        Pi.π (fun (_ : fiber true) => Z) () =
      Pi.π (fun _p : Σ b, fiber b => Z) ⟨true, ()⟩ := by
  exact chosenPiPiHom_π_π (X := fun b (_ : fiber b) => Z) true ()

end EmptyFiberClients
