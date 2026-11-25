/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatCone

/-!
# Functoriality of the whole original fat cone

The actual pushout map transports the whole original cylinder and
the identical fixed apex. Its identity and composition equations
give the fat-cone functor to the category under the original point.
The entire path dictionary commutes with source precomposition and
ambient postcomposition, and the original join comparison is natural.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

/-- The actual whole fat-cone map induced by an original simplicial map. -/
def map {X Y : SSet.{u}} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  pushout.map (one X) (SSet.stdSimplex.isTerminalObj₀.from X)
    (one Y) (SSet.stdSimplex.isTerminalObj₀.from Y) (f ▷ (Δ[1] : SSet.{u})) (𝟙 Δ[0]) f
    (SSet.ι₁_comp f) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

/-- The induced map transports the entire original cylinder by the identical tensor map. -/
theorem cylinder_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    cylinder X ≫ map f = (f ▷ (Δ[1] : SSet.{u})) ≫ cylinder Y := pushout.inl_desc _ _ _

/-- The induced map fixes the entire original apex. -/
theorem apex_map {X Y : SSet.{u}} (f : X ⟶ Y) : apex X ≫ map f = apex Y := by
  have h : apex X ≫ map f = 𝟙 Δ[0] ≫ apex Y := pushout.inr_desc _ _ _
  exact h.trans (Category.id_comp _)

/-- The induced map transports the entire original base by the original map. -/
theorem base_map {X Y : SSet.{u}} (f : X ⟶ Y) : base X ≫ map f = f ≫ base Y := by
  rw [base, Category.assoc, cylinder_map, ← Category.assoc, SSet.ι₀_comp, Category.assoc, base]

/-- The fat cone of the identical original map is identical on every whole original field. -/
theorem map_id (X : SSet.{u}) : map (𝟙 X) = 𝟙 (obj X) := by
  apply hom_ext
  · rw [cylinder_map, id_whiskerRight, Category.id_comp, Category.comp_id]
  · rw [apex_map, Category.comp_id]

/-- Fat-cone transport composes as the identical whole original simplicial maps. -/
theorem map_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map f ≫ map g := by
  apply hom_ext
  · rw [cylinder_map, comp_whiskerRight, Category.assoc, ← Category.assoc (cylinder X),
      cylinder_map, Category.assoc, cylinder_map]
  · rw [apex_map, ← Category.assoc, apex_map, apex_map]

/-- The actual fat-cone functor, retaining its specified original point as structure map. -/
def underFunctor : SSet.{u} ⥤ Under (Δ[0] : SSet.{u}) where
  obj X := Under.mk (apex X)
  map f := Under.homMk (map f) (apex_map f)
  map_id X := by
    apply StructuredArrow.hom_ext
    exact map_id X
  map_comp f g := by
    apply StructuredArrow.hom_ext
    exact map_comp f g

/-- Reading the underlying map of fat-cone functor transport returns the identical original pushout map. -/
theorem underFunctor_map_right {X Y : SSet.{u}} (f : X ⟶ Y) : (underFunctor.map f).right = map f := rfl

/-- The original fat-cone to join-cone comparison commutes with the entire original source map. -/
theorem toJoin_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    map f ≫ toJoin Y = toJoin X ≫ (join.map f).app Δ[0] := by
  apply hom_ext
  · rw [← Category.assoc, cylinder_map, Category.assoc, cylinder_toJoin,
      ← Category.assoc, cylinder_toJoin, ConeCylinder.coneCylinder_naturality]
  · rw [← Category.assoc, apex_map, apex_toJoin, ← Category.assoc, apex_toJoin,
      joinInr_comp_map]

/-- The entire actual internal path commutes with original source precomposition. -/
theorem toPath_precomp {X Y H : SSet.{u}} (f : X ⟶ Y) (q : obj Y ⟶ H) :
    toPath (map f ≫ q) = f ≫ toPath q := by
  apply MonoidalClosed.uncurry_injective
  rw [toPath, toPath, MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry, ← Category.assoc (cylinder X), cylinder_map,
    Category.assoc, BraidedCategory.braiding_naturality_right_assoc]

/-- The entire actual internal path commutes with the original ambient map. -/
theorem toPath_postcomp {X H K : SSet.{u}} (q : obj X ⟶ H) (p : H ⟶ K) :
    toPath (q ≫ p) = toPath q ≫ (ihom (Δ[1] : SSet.{u})).map p := by
  simpa only [toPath, Category.assoc] using
    MonoidalClosed.curry_natural_right ((β_ (Δ[1] : SSet.{u}) X).hom ≫ cylinder X ≫ q) p

/-- The original comparison as an actual natural transformation between the two structured cone functors. -/
def joinComparison : underFunctor.{u} ⟶ joinOver (Δ[0] : SSet.{u}) where
  app X := Under.homMk (toJoin X) (apex_toJoin X)
  naturality _X _Y f := by
    apply StructuredArrow.hom_ext
    exact toJoin_naturality f

end SSet.WalkingAdjunction.FatCone
