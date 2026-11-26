/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingHom

/-!
# The actual disjoint sum of original simplicial enrichments

Objects are the SAME two original object families with their disjoint
labels. Each original full Hom, identity and composition is retained.
Cross-family Homs are the canonical original empty coefficient object.
All simplex operators and complete enriched laws are preserved, with
independent coefficient, source and target object universes.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory

namespace SSet.DisjointSum
variable {C : Type v} {D : Type w} [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} D]

/-- The full original coefficient at each SAME disjoint object pair. -/
def homObject : C ⊕ D → C ⊕ D → SSet.{u}
  | .inl x, .inl y => x ⟶[SSet.{u}] y
  | .inl _x, .inr _y => WalkingHom.emptyHom
  | .inr _x, .inl _y => WalkingHom.emptyHom
  | .inr x, .inr y => x ⟶[SSet.{u}] y

/-- Each original identity is retained at its SAME disjoint object label. -/
def identity : (x : C ⊕ D) → 𝟙_ SSet.{u} ⟶ homObject x x
  | .inl x => eId SSet.{u} x
  | .inr x => eId SSet.{u} x

private def fromEmptyLeft (X Y : SSet.{u}) : WalkingHom.emptyHom ⊗ X ⟶ Y where
  app _q := ↾fun p => PEmpty.elim p.1
  naturality _q _r _f := by
    apply ConcreteCategory.hom_ext
    intro p
    exact PEmpty.elim p.1

private def fromEmptyRight (X Y : SSet.{u}) : X ⊗ WalkingHom.emptyHom ⟶ Y where
  app _q := ↾fun p => PEmpty.elim p.2
  naturality _q _r _f := by
    apply ConcreteCategory.hom_ext
    intro p
    exact PEmpty.elim p.2

/-- Original complete composition is unchanged on each family and has its genuine empty domain at every crossing. -/
def composition : (x y z : C ⊕ D) → homObject x y ⊗ homObject y z ⟶ homObject x z
  | .inl x, .inl y, .inl z => eComp SSet.{u} x y z
  | .inl x, .inl y, .inr _z => fromEmptyRight (x ⟶[SSet.{u}] y) WalkingHom.emptyHom
  | .inl x, .inr _y, .inl z => fromEmptyLeft WalkingHom.emptyHom (x ⟶[SSet.{u}] z)
  | .inl _x, .inr y, .inr z => fromEmptyLeft (y ⟶[SSet.{u}] z) WalkingHom.emptyHom
  | .inr _x, .inl y, .inl z => fromEmptyLeft (y ⟶[SSet.{u}] z) WalkingHom.emptyHom
  | .inr x, .inl _y, .inr z => fromEmptyLeft WalkingHom.emptyHom (x ⟶[SSet.{u}] z)
  | .inr x, .inr y, .inl _z => fromEmptyRight (x ⟶[SSet.{u}] y) WalkingHom.emptyHom
  | .inr x, .inr y, .inr z => eComp SSet.{u} x y z

/-- The SAME original disjoint identities satisfy the complete original left unit law. -/
theorem identity_comp (x y : C ⊕ D) :
    (λ_ (homObject x y)).inv ≫ identity x ▷ homObject x y ≫ composition x x y =
      𝟙 (homObject x y) := by
  cases x <;> cases y
  case inl.inl x y => exact e_id_comp SSet.{u} x y
  case inr.inr x y => exact e_id_comp SSet.{u} x y
  all_goals
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    exact PEmpty.elim p

/-- The SAME original disjoint identities satisfy the complete original right unit law. -/
theorem comp_identity (x y : C ⊕ D) :
    (ρ_ (homObject x y)).inv ≫ homObject x y ◁ identity y ≫ composition x y y =
      𝟙 (homObject x y) := by
  cases x <;> cases y
  case inl.inl x y => exact e_comp_id SSet.{u} x y
  case inr.inr x y => exact e_comp_id SSet.{u} x y
  all_goals
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    exact PEmpty.elim p

/-- All original disjoint composable coefficient triples satisfy the full associativity equation. -/
theorem composition_assoc (a b c d : C ⊕ D) :
    (α_ (homObject a b) (homObject b c) (homObject c d)).inv ≫
        composition a b c ▷ homObject c d ≫ composition a c d =
      homObject a b ◁ composition b c d ≫ composition a b d := by
  cases a <;> cases b <;> cases c <;> cases d
  case inl.inl.inl.inl a b c d => exact e_assoc SSet.{u} a b c d
  case inr.inr.inr.inr a b c d => exact e_assoc SSet.{u} a b c d
  all_goals
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    first
      | exact PEmpty.elim p.1
      | exact PEmpty.elim p.2.1
      | exact PEmpty.elim p.2.2

/-- The actual whole original disjoint-sum enrichment, retaining both original coefficient families. -/
@[instance_reducible]
def enrichment : EnrichedCategory SSet.{u} (C ⊕ D) where
  Hom := homObject
  id := identity
  comp := composition
  id_comp := identity_comp
  comp_id := comp_identity
  assoc := composition_assoc

end SSet.DisjointSum
