/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PointedMotivicQuotients

/-!
# Native maps of pointed motivic cofibers

Every map is the actual pushout map of the given commutative square,
including its terminal collapsed-point leg.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PointedMotivicQuotientMaps

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open FiniteTransferCycleModels PointedMotivicModels PointedMotivicQuotients

variable {k : Type} [Field k]

/-- Pointed representables keep actual scheme-map composition. -/
theorem representedMap_comp {U V W : SmoothScheme k} (f : U ⟶ V) (g : V ⟶ W) :
    representedMap (f ≫ g) = representedMap f ≫ representedMap g := by
  apply (Under.forget (𝟙_ (Spaces (k := k)))).map_injective
  ext Z n x
  change Option (ULift.{1} (Z.unop ⟶ U)) at x
  change x.map (fun a => ULift.up (a.down ≫ (f ≫ g))) =
    (x.map (fun a => ULift.up (a.down ≫ f))).map (fun a => ULift.up (a.down ≫ g))
  cases x <;> simp [Category.assoc]

/-- A square gives its actual native pushout map on pointed cofibers. -/
def cofiberMap {X Y X' Y' : PointedSpaces (k := k)} (a : X ⟶ Y) (b : X' ⟶ Y')
    (u : X ⟶ X') (v : Y ⟶ Y') (h : a ≫ v = u ≫ b) : cofiber a ⟶ cofiber b :=
  Under.homMk
    (pushout.map a.right (isTerminalTensorUnit.from X.right)
      b.right (isTerminalTensorUnit.from X'.right) v.right (𝟙 _) u.right
      (congrArg Under.Hom.right h) (isTerminalTensorUnit.hom_ext _ _))
    (by simp [cofiber, pushout.map])

end MathlibExt.AlgebraicGeometry.PointedMotivicQuotientMaps
