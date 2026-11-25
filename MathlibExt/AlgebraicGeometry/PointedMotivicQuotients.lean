/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PointedMotivicModels
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# Literal pointed motivic quotients and smash products

The cofiber is the presheaf pushout against the terminal pointed object.
The smash product is the presheaf quotient of the actual product by its
two basepoint axes. All quotient, diagonal and represented maps retain
their native pushout or product maps.

Source: Voevodsky arXiv:math/0107109v1, Section 2 and Section 4,
pp. 3--6 and 12--14; Morel--Voevodsky, A1-homotopy theory, Section 2.
Local replacement and homotopy/cofiber equivalence are separate requests.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PointedMotivicQuotients

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open FiniteTransferCycleModels NisnevichTransferModels PointedMotivicModels
open scoped Simplicial

variable {k : Type} [Field k]

/-- The native represented pointed map sends each actual scheme map to
its postcomposition, and the added basepoint to the added basepoint. -/
def representedSetsMap {U V : SmoothScheme k} (f : U ⟶ V) :
    representedSets U ⟶ representedSets V where
  app W := ↾fun x => x.map (fun g => ULift.up (g.down ≫ f))
  naturality W Z a := by
    ext x
    cases x <;> simp [representedSets, Category.assoc]

/-- The actual pointed represented map, after the constant-simplex functor. -/
def representedMap {U V : SmoothScheme k} (f : U ⟶ V) :
    representedPointed U ⟶ representedPointed V :=
  Under.homMk (Functor.whiskerRight (representedSetsMap f)
    (Functor.const SimplexCategoryᵒᵖ)) (by rfl)

/-- The actual constant basepoint morphism of pointed presheaves. -/
def zeroMap (X Y : PointedSpaces (k := k)) : X ⟶ Y :=
  Under.homMk (isTerminalTensorUnit.from X.right ≫ Y.hom) (by
    rw [← Category.assoc]
    have h : X.hom ≫ isTerminalTensorUnit.from X.right = 𝟙 _ :=
      isTerminalTensorUnit.hom_ext _ _
    rw [h, Category.id_comp])

/-- The actual pointed presheaf cofiber, with its collapsed-point map. -/
def cofiber {X Y : PointedSpaces (k := k)} (a : X ⟶ Y) :
    PointedSpaces (k := k) :=
  Under.mk (pushout.inr a.right (isTerminalTensorUnit.from X.right))

/-- The native cofiber quotient map. -/
def cofiberQuotient {X Y : PointedSpaces (k := k)} (a : X ⟶ Y) :
    Y ⟶ cofiber a :=
  Under.homMk (pushout.inl a.right (isTerminalTensorUnit.from X.right)) (by
    rw [← Under.w a, Category.assoc, pushout.condition, ← Category.assoc]
    have h : X.hom ≫ isTerminalTensorUnit.from X.right = 𝟙 _ :=
      isTerminalTensorUnit.hom_ext _ _
    rw [h, Category.id_comp]
    rfl)

/-- The literal cofiber quotient kills the original pointed morphism. -/
theorem cofiberQuotient_comp_zero {X Y : PointedSpaces (k := k)} (a : X ⟶ Y) :
    a ≫ cofiberQuotient a = zeroMap X (cofiber a) := by
  apply (Under.forget (𝟙_ (Spaces (k := k)))).map_injective
  change a.right ≫ pushout.inl a.right (isTerminalTensorUnit.from X.right) =
    isTerminalTensorUnit.from X.right ≫ pushout.inr a.right (isTerminalTensorUnit.from X.right)
  exact pushout.condition

/-- Cofiber descent is the actual native pushout lift of a null composite. -/
def cofiberDesc {X Y Z : PointedSpaces (k := k)} (a : X ⟶ Y) (b : Y ⟶ Z)
    (h : a ≫ b = zeroMap X Z) : cofiber a ⟶ Z :=
  Under.homMk
    (pushout.desc b.right Z.hom (by
      exact congrArg Under.Hom.right h))
    (by simp [cofiber])

/-- Both basepoint axes are the native pushout wedge. -/
def wedge (X Y : PointedSpaces (k := k)) : Spaces (k := k) :=
  pushout X.hom Y.hom

/-- The two literal basepoint axes in the product. -/
def wedgeToProduct (X Y : PointedSpaces (k := k)) :
    wedge X Y ⟶ prod X.right Y.right :=
  pushout.desc
    (prod.lift (𝟙 X.right) (isTerminalTensorUnit.from X.right ≫ Y.hom))
    (prod.lift (isTerminalTensorUnit.from Y.right ≫ X.hom) (𝟙 Y.right)) (by
      apply prod.hom_ext
      · simp only [Category.assoc, prod.lift_fst, Category.comp_id]
        have h : Y.hom ≫ isTerminalTensorUnit.from Y.right = 𝟙 _ :=
          isTerminalTensorUnit.hom_ext _ _
        rw [← Category.assoc, h, Category.id_comp]
      · simp only [Category.assoc, prod.lift_snd, Category.comp_id]
        have h : X.hom ≫ isTerminalTensorUnit.from X.right = 𝟙 _ :=
          isTerminalTensorUnit.hom_ext _ _
        rw [← Category.assoc, h, Category.id_comp])

/-- The actual wedge map is the native pushout map of both pointed maps. -/
def wedgeMap {X Y X' Y' : PointedSpaces (k := k)} (a : X ⟶ X') (b : Y ⟶ Y') :
    wedge X Y ⟶ wedge X' Y' :=
  pushout.map X.hom Y.hom X'.hom Y'.hom a.right b.right (𝟙 _)
    (by simp) (by simp)

/-- The wedge map commutes with its two actual product axes. -/
theorem wedgeMap_toProduct {X Y X' Y' : PointedSpaces (k := k)}
    (a : X ⟶ X') (b : Y ⟶ Y') :
    wedgeToProduct X Y ≫ prod.map a.right b.right =
      wedgeMap a b ≫ wedgeToProduct X' Y' := by
  apply pushout.hom_ext <;> apply prod.hom_ext <;>
    simp [wedgeToProduct, wedgeMap, pushout.map, Category.assoc, Under.w]
  all_goals
    rw [← Category.assoc]
    congr 1

/-- The actual smash product, as product modulo the two pointed axes. -/
def smash (X Y : PointedSpaces (k := k)) : PointedSpaces (k := k) :=
  Under.mk (pushout.inr (wedgeToProduct X Y)
    (isTerminalTensorUnit.from (wedge X Y)))

/-- The native product-to-smash quotient. -/
def smashQuotient (X Y : PointedSpaces (k := k)) :
    prod X.right Y.right ⟶ (smash X Y).right :=
  pushout.inl (wedgeToProduct X Y) (isTerminalTensorUnit.from (wedge X Y))

/-- Smash maps are the actual pushout maps of the native product and wedge maps. -/
def smashMap {X Y X' Y' : PointedSpaces (k := k)} (a : X ⟶ X') (b : Y ⟶ Y') :
    smash X Y ⟶ smash X' Y' :=
  Under.homMk
    (pushout.map (wedgeToProduct X Y) (isTerminalTensorUnit.from (wedge X Y))
      (wedgeToProduct X' Y') (isTerminalTensorUnit.from (wedge X' Y'))
      (prod.map a.right b.right) (𝟙 _) (wedgeMap a b)
      (wedgeMap_toProduct a b) (isTerminalTensorUnit.hom_ext _ _))
    (by simp [smash, pushout.map])

/-- The source diagonal followed by the actual smash quotient. -/
def smashDiagonal (X : PointedSpaces (k := k)) : X ⟶ smash X X :=
  Under.homMk (prod.lift (𝟙 X.right) (𝟙 X.right) ≫ smashQuotient X X) (by
    have h : X.hom ≫ prod.lift (𝟙 X.right) (𝟙 X.right) =
        X.hom ≫ pushout.inl X.hom X.hom ≫ wedgeToProduct X X := by
      apply prod.hom_ext
      · simp [wedgeToProduct]
      · simp only [Category.assoc, prod.lift_snd, Category.comp_id,
          wedgeToProduct, pushout.inl_desc_assoc]
        have h0 : X.hom ≫ isTerminalTensorUnit.from X.right = 𝟙 _ :=
          isTerminalTensorUnit.hom_ext _ _
        rw [← Category.assoc, h0, Category.id_comp]
    rw [← Category.assoc, h]
    change (X.hom ≫ pushout.inl X.hom X.hom ≫ wedgeToProduct X X) ≫
      pushout.inl _ _ = pushout.inr _ _
    rw [Category.assoc, Category.assoc, pushout.condition,
      ← Category.assoc, ← Category.assoc]
    have h0 : (X.hom ≫ pushout.inl X.hom X.hom) ≫
        isTerminalTensorUnit.from (wedge X X) = 𝟙 _ :=
      isTerminalTensorUnit.hom_ext _ _
    dsimp only [wedge] at h0 ⊢
    rw [h0, Category.id_comp])

end MathlibExt.AlgebraicGeometry.PointedMotivicQuotients
