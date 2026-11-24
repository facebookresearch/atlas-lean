/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalence

/-!
# Strict source-prescribed lifting of equivalence edges

`HasStrictEquivalenceLifting p` expresses a lifting condition for arbitrary
simplicial maps. A chosen source vertex and a base equivalence edge have an
equivalence lift with the specified source, an explicit target equality,
and equality of the actual image `1`-simplex.

Equivalence means `Edge.IsEquivalence`, defined through the ordinary
homotopy category even for an arbitrary simplicial set. This extracts the
lifting clause in Joyal's Definition 4.2 from its inner-fibration and
quasicategory context. Cisinski's §1.5.1 and Definition 3.3.15 use
inverse-triangle invertibility and additionally impose innerness; the
comparison with the present equivalence predicate assumes that both the
domain and codomain are quasicategories. The standalone condition is the project
extension of that clause.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet

/-- Every equivalence edge out of the image of a chosen vertex has a
strict equivalence lift. Both the target equality and the equality of
underlying `1`-simplices are retained. -/
class HasStrictEquivalenceLifting {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  /-- Source-prescribed equivalence-edge lifting, with its strict equations. -/
  exists_lift {x₀ : X _⦋0⦌} {y₁ : Y _⦋0⦌}
      (g : Edge (p.app (op ⦋0⦌) x₀) y₁) (hg : g.IsEquivalence) :
      ∃ (x₁ : X _⦋0⦌) (_ : p.app (op ⦋0⦌) x₁ = y₁) (f : Edge x₀ x₁),
        f.IsEquivalence ∧ (f.map p).edge = g.edge

/-- The characteristic condition for strict source-prescribed
equivalence-edge lifting. -/
theorem hasStrictEquivalenceLifting_iff {X Y : SSet.{u}} (p : X ⟶ Y) :
    HasStrictEquivalenceLifting p ↔
      ∀ {x₀ : X _⦋0⦌} {y₁ : Y _⦋0⦌} (g : Edge (p.app (op ⦋0⦌) x₀) y₁),
        g.IsEquivalence →
          ∃ (x₁ : X _⦋0⦌) (_ : p.app (op ⦋0⦌) x₁ = y₁) (f : Edge x₀ x₁),
            f.IsEquivalence ∧ (f.map p).edge = g.edge :=
  ⟨fun h ↦ @HasStrictEquivalenceLifting.exists_lift X Y p h, fun h ↦ ⟨h⟩⟩

end SSet
