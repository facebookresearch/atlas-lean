/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.JoinPathSliceComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The actual fat cone and its original join comparison

The fat cone is the native pushout of the one endpoint of the
ordinary simplicial cylinder along the terminal map. Maps out of it
are exactly whole cylinder maps whose final endpoint is the fixed
apex. Currying identifies these maps with the existing path-slice
dictionary. The canonical cylinder-to-join map induces the actual
fat-cone to join-cone comparison, preserving the entire base and apex.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace SSet.WalkingAdjunction

namespace FatCone

/-- The original one endpoint of the ordinary cylinder, with its full domain fixed. -/
abbrev one (X : SSet.{u}) : X ⟶ X ⊗ (Δ[1] : SSet.{u}) := SSet.ι₁

/-- The actual pushout which collapses precisely the entire final cylinder row to its apex. -/
def obj (X : SSet.{u}) : SSet.{u} := pushout (one X) (SSet.stdSimplex.isTerminalObj₀.from X)

/-- The entire original ordinary cylinder map into the fat cone. -/
def cylinder (X : SSet.{u}) : X ⊗ (Δ[1] : SSet.{u}) ⟶ obj X :=
  pushout.inl (one X) (SSet.stdSimplex.isTerminalObj₀.from X)

/-- The original fixed apex of the fat cone. -/
def apex (X : SSet.{u}) : (Δ[0] : SSet.{u}) ⟶ obj X :=
  pushout.inr (one X) (SSet.stdSimplex.isTerminalObj₀.from X)

/-- The entire original base is the zero endpoint followed by the cylinder inclusion. -/
def base (X : SSet.{u}) : X ⟶ obj X := SSet.ι₀ ≫ cylinder X

/-- The full final row is the original constant apex map. -/
theorem one_cylinder (X : SSet.{u}) : one X ≫ cylinder X =
    SSet.stdSimplex.isTerminalObj₀.from X ≫ apex X := pushout.condition

/-- Descend a whole cylinder map with its supplied actual constant final endpoint. -/
def desc {X H : SSet.{u}} (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ H)
    (z : (Δ[0] : SSet.{u}) ⟶ H)
    (hz : one X ≫ h = SSet.stdSimplex.isTerminalObj₀.from X ≫ z) : obj X ⟶ H :=
  pushout.desc h z hz

/-- Reading the original cylinder of the descended map returns the identical whole supplied map. -/
theorem cylinder_desc {X H : SSet.{u}} (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ H)
    (z : (Δ[0] : SSet.{u}) ⟶ H)
    (hz : one X ≫ h = SSet.stdSimplex.isTerminalObj₀.from X ≫ z) :
    cylinder X ≫ desc h z hz = h := pushout.inl_desc _ _ _

/-- Reading the original apex of the descended map returns the identical supplied apex. -/
theorem apex_desc {X H : SSet.{u}} (h : X ⊗ (Δ[1] : SSet.{u}) ⟶ H)
    (z : (Δ[0] : SSet.{u}) ⟶ H)
    (hz : one X ≫ h = SSet.stdSimplex.isTerminalObj₀.from X ≫ z) :
    apex X ≫ desc h z hz = z := pushout.inr_desc _ _ _

/-- Whole original cylinder and apex maps determine every map out of the fat cone. -/
theorem hom_ext {X H : SSet.{u}} {p q : obj X ⟶ H}
    (hc : cylinder X ≫ p = cylinder X ≫ q) (ha : apex X ≫ p = apex X ≫ q) : p = q :=
  pushout.hom_ext hc ha

/-- The actual fat-cone comparison to the original join cone. -/
def toJoin (X : SSet.{u}) : obj X ⟶ X ⋆ (Δ[0] : SSet.{u}) :=
  desc (ConeCylinder.coneCylinder X) (joinInr X Δ[0]) (ConeCylinder.coneCylinder_one X)

/-- The comparison retains the entire original cylinder-to-cone map. -/
theorem cylinder_toJoin (X : SSet.{u}) : cylinder X ≫ toJoin X = ConeCylinder.coneCylinder X :=
  cylinder_desc _ _ _

/-- The comparison fixes the identical whole original join apex. -/
theorem apex_toJoin (X : SSet.{u}) : apex X ≫ toJoin X = joinInr X Δ[0] := apex_desc _ _ _

/-- The comparison fixes the entire original join base. -/
theorem base_toJoin (X : SSet.{u}) : base X ≫ toJoin X = joinInl X Δ[0] := by
  rw [base, Category.assoc, cylinder_toJoin, ConeCylinder.coneCylinder_zero]

/-- The actual fat-cone map classified by a whole original internal path with fixed endpoint. -/
def ofPath {X H : SSet.{u}} (z : (Δ[0] : SSet.{u}) ⟶ H) (p : X ⟶ pathSpace H)
    (hp : p ≫ eval₁ = SSet.stdSimplex.isTerminalObj₀.from X ≫ z) : obj X ⟶ H :=
  desc ((β_ X (Δ[1] : SSet.{u})).hom ≫ MonoidalClosed.uncurry p) z
    ((comp_eval₁_eq_ι₁_braiding_uncurry p).symm.trans hp)

/-- The internal path of a complete fat-cone map. -/
def toPath {X H : SSet.{u}} (p : obj X ⟶ H) : X ⟶ pathSpace H :=
  MonoidalClosed.curry ((β_ (Δ[1] : SSet.{u}) X).hom ≫ cylinder X ≫ p)

/-- The path of a fat-cone map keeps the entire original final endpoint. -/
theorem toPath_one {X H : SSet.{u}} (p : obj X ⟶ H) :
    toPath p ≫ eval₁ = SSet.stdSimplex.isTerminalObj₀.from X ≫ apex X ≫ p := by
  rw [comp_eval₁_eq_ι₁_braiding_uncurry, toPath, MonoidalClosed.uncurry_curry,
    SymmetricCategory.symmetry_assoc, ← Category.assoc, one_cylinder, Category.assoc]

/-- Currying the descended whole path recovers that identical original path. -/
theorem toPath_ofPath {X H : SSet.{u}} (z : (Δ[0] : SSet.{u}) ⟶ H) (p : X ⟶ pathSpace H)
    (hp : p ≫ eval₁ = SSet.stdSimplex.isTerminalObj₀.from X ≫ z) : toPath (ofPath z p hp) = p := by
  apply MonoidalClosed.uncurry_injective
  rw [toPath, MonoidalClosed.uncurry_curry, ofPath, cylinder_desc,
    SymmetricCategory.symmetry_assoc]

/-- The path and original apex recover the complete supplied fat-cone map. -/
theorem ofPath_toPath {X H : SSet.{u}} (p : obj X ⟶ H) :
    ofPath (apex X ≫ p) (toPath p) (toPath_one p) = p := by
  apply hom_ext
  · rw [ofPath, cylinder_desc, toPath, MonoidalClosed.uncurry_curry,
      SymmetricCategory.symmetry_assoc]
  · exact apex_desc _ _ _

/-- The native full-map equivalence between fixed-apex fat cones and original internal paths. -/
def pathEquiv (X H : SSet.{u}) (z : (Δ[0] : SSet.{u}) ⟶ H) :
    {q : obj X ⟶ H // apex X ≫ q = z} ≃
      {p : X ⟶ pathSpace H // p ≫ eval₁ = SSet.stdSimplex.isTerminalObj₀.from X ≫ z} where
  toFun q := ⟨toPath q.1, by rw [toPath_one, q.2]⟩
  invFun p := ⟨ofPath z p.1 p.2, apex_desc _ _ _⟩
  left_inv q := by
    apply Subtype.ext
    have h := ofPath_toPath q.1
    simpa only [q.2] using h
  right_inv p := Subtype.ext (toPath_ofPath z p.1 p.2)

/-- Passing through the original comparison gives the identical internal path of the original join cone. -/
theorem toPath_toJoin {X H : SSet.{u}} (q : X ⋆ (Δ[0] : SSet.{u}) ⟶ H) :
    toPath (toJoin X ≫ q) = ConeCylinder.pathOfJoinCone q := by
  unfold toPath ConeCylinder.pathOfJoinCone
  rw [← Category.assoc (cylinder X), cylinder_toJoin]

end FatCone

end SSet.WalkingAdjunction
