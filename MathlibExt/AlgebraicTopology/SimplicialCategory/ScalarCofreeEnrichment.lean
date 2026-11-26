/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategoryFunctoriality

/-!
# Cofree scalar enrichment on the complete ordinal-operator family

Every Hom in scalar degree n is the full family of ordinary
Homs indexed by ALL operators n→q. Operators act by their 
precomposition. Identity and composition use the same 
ordinary maps at each operator. Hom and object universes are independent.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace SSet.ScalarCofree

variable (q : SimplexCategoryᵒᵖ) (E : Type v) [Category.{u} E]

/-- The same Hom family at every ordinal operator. -/
def homObject (x y : E) : SSet.{u} where
  obj n := (n ⟶ q) → (x ⟶ y)
  map f := ↾fun h θ => h (f ≫ θ)
  map_id _n := by
    apply ConcreteCategory.hom_ext
    intro h
    funext θ
    exact congrArg h (Category.id_comp θ)
  map_comp _f _g := by
    apply ConcreteCategory.hom_ext
    intro h
    funext θ
    exact congrArg h (Category.assoc _ _ _)

/-- Every coefficient operator is its full precomposition map. -/
theorem homObject_map (x y : E) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (h : (homObject q E x y).obj n) (θ : m ⟶ q) :
    (homObject q E x y).map f h θ = h (f ≫ θ) := rfl

/-- The same identity at every ordinal operator. -/
def identity (x : E) : 𝟙_ SSet.{u} ⟶ homObject q E x x where
  app _n := ↾fun _ _θ => 𝟙 x
  naturality _n _m _f := by
    apply ConcreteCategory.hom_ext
    intro h
    rfl

/-- The same composition at every complete ordinal operator. -/
def composition (x y z : E) : homObject q E x y ⊗ homObject q E y z ⟶ homObject q E x z where
  app _n := ↾fun h θ => h.1 θ ≫ h.2 θ
  naturality _n _m _f := by
    apply ConcreteCategory.hom_ext
    intro h
    rfl

/-- The full left-unit equation holds at every coefficient. -/
theorem identity_comp (x y : E) :
    (λ_ (homObject q E x y)).inv ≫ identity q E x ▷ _ ≫ composition q E x x y = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro h
  funext θ
  exact Category.id_comp (h θ)

/-- The full right-unit equation holds at every coefficient. -/
theorem comp_identity (x y : E) :
    (ρ_ (homObject q E x y)).inv ≫ _ ◁ identity q E y ≫ composition q E x y y = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro h
  funext θ
  exact Category.comp_id (h θ)

/-- The complete associativity equation holds at every operator. -/
theorem composition_assoc (a b c d : E) :
    (α_ _ _ _).inv ≫ composition q E a b c ▷ _ ≫ composition q E a c d =
      _ ◁ composition q E b c d ≫ composition q E a b d := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro h
  funext θ
  exact Category.assoc (h.1 θ) (h.2.1 θ) (h.2.2 θ)

/-- The cofree scalar enrichment, retaining every complete ordinary Hom family. -/
@[instance_reducible]
def enrichment : EnrichedCategory SSet.{u} E where
  Hom := homObject q E
  id := identity q E
  comp := composition q E
  id_comp := identity_comp q E
  comp_id := comp_identity q E
  assoc := composition_assoc q E

/-- Evaluate the same complete cofree coefficient at the identity operator. -/
def evaluation :
    let _ : EnrichedCategory SSet.{u} E := enrichment q E
    ScalarObject E q ⥤ E := by
  let _ : EnrichedCategory SSet.{u} E := enrichment q E
  exact {
    obj x := x.obj
    map h := h (𝟙 q)
    map_id _x := rfl
    map_comp _f _g := rfl }

end SSet.ScalarCofree
