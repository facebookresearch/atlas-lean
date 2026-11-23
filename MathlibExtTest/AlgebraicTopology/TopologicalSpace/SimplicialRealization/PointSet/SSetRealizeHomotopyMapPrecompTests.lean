/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module


import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMapPrecomp

/-!
# Realized homotopy source-precomposition tests

These clients pin the precomposed endpoints and cylinder, the covariant
realization square with an unchanged interval factor, the first-projection
factorization, and universe-zero and universe-one elaboration.  They also
guard the private tensor/product helpers and the absence of the later
relative and Waldhausen surfaces.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits Simplicial MonoidalCategory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory
namespace SSetRealizeHomotopyMapPrecompTests

section Generic

variable {W X Y : SSet.{u}} {f g : X ⟶ Y}
  (H : SSet.Homotopy f g) (k : W ⟶ X)

/-- Precomposition has the exact expected endpoint type. -/
example : SSet.Homotopy (k ≫ f) (k ≫ g) :=
  H.precomp k

/-- The time-zero endpoint remains source precomposition followed by the
original time-zero map. -/
example : SSet.ι₀ ≫ (H.precomp k).h = k ≫ f :=
  (H.precomp k).h₀

/-- The time-one endpoint remains source precomposition followed by the
original time-one map. -/
example : SSet.ι₁ ≫ (H.precomp k).h = k ≫ g :=
  (H.precomp k).h₁

/-- The precomposed cylinder is exactly the interval whiskering of the
source map followed by the original cylinder. -/
example :
    (H.precomp k).h = (k ▷ (Δ[1] : SSet.{u})) ≫ H.h :=
  SSet.Homotopy.precomp_h H k

/-- Realization is covariant in the source map and leaves the interval
factor unchanged. -/
example :
    Limits.prod.map (𝟙 TopCat.I.{u}) (SSet.toTop.map k) ≫
        SSet.realizeHomotopyMap X Y f g H =
      SSet.realizeHomotopyMap W Y (k ≫ f) (k ≫ g)
        (H.precomp k) :=
  SSet.realizeHomotopyMap_precomp H k

/-- The projection-factor theorem accepts arbitrary endpoint parameters and
uses the cylinder equality as its hypothesis. -/
example {q₀ q₁ : W ⟶ Y} (R : SSet.Homotopy q₀ q₁)
    (_hR : R.h = CartesianMonoidalCategory.fst W
      (Δ[1] : SSet.{u}) ≫ q₀) :
    SSet.realizeHomotopyMap W Y q₀ q₁ R =
      Limits.prod.snd ≫ SSet.toTop.map q₀ :=
  SSet.realizeHomotopyMap_of_h_eq_fst R _hR

end Generic

section UniverseZero

/-- Explicit universe-zero client for source precomposition and realization. -/
example {W X Y : SSet.{0}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (k : W ⟶ X) :
    Limits.prod.map (𝟙 TopCat.I.{0}) (SSet.toTop.map k) ≫
        SSet.realizeHomotopyMap X Y f g H =
      SSet.realizeHomotopyMap W Y (k ≫ f) (k ≫ g)
        (H.precomp k) :=
  SSet.realizeHomotopyMap_precomp H k

/-- Explicit universe-zero client for the projection factorization. -/
example {W Y : SSet.{0}} {q₀ q₁ : W ⟶ Y}
    (H : SSet.Homotopy q₀ q₁)
    (hH : H.h = CartesianMonoidalCategory.fst W
      (Δ[1] : SSet.{0}) ≫ q₀) :
    SSet.realizeHomotopyMap W Y q₀ q₁ H =
      Limits.prod.snd ≫ SSet.toTop.map q₀ :=
  SSet.realizeHomotopyMap_of_h_eq_fst H hH

end UniverseZero

section UniverseOne

/-- Explicit universe-one client for source precomposition and realization. -/
example {W X Y : SSet.{1}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (k : W ⟶ X) :
    Limits.prod.map (𝟙 TopCat.I.{1}) (SSet.toTop.map k) ≫
        SSet.realizeHomotopyMap X Y f g H =
      SSet.realizeHomotopyMap W Y (k ≫ f) (k ≫ g)
        (H.precomp k) :=
  SSet.realizeHomotopyMap_precomp H k

/-- Explicit universe-one client for the projection factorization. -/
example {W Y : SSet.{1}} {q₀ q₁ : W ⟶ Y}
    (H : SSet.Homotopy q₀ q₁)
    (hH : H.h = CartesianMonoidalCategory.fst W
      (Δ[1] : SSet.{1}) ≫ q₀) :
    SSet.realizeHomotopyMap W Y q₀ q₁ H =
      Limits.prod.snd ≫ SSet.toTop.map q₀ :=
  SSet.realizeHomotopyMap_of_h_eq_fst H hH

end UniverseOne

section PrivacyAndNonclaims

#guard_msgs (error, substring := true) in
#check SSet.tensorLeftIsoProd_hom_natural_left

#guard_msgs (error, substring := true) in
#check SSet.tensorLeftIsoProd_inv_natural_left

#guard_msgs (error, substring := true) in
#check SSet.HomotopyRel

#guard_msgs (error, substring := true) in
#check SSet.realizeHomotopyRelAtVertex

#guard_msgs (error, substring := true) in
#check SSet.realizeHomotopyMap_stationary_at_vertex

end PrivacyAndNonclaims

#print axioms SSet.Homotopy.precomp
#print axioms SSet.Homotopy.precomp_h
#print axioms SSet.realizeHomotopyMap_precomp
#print axioms SSet.realizeHomotopyMap_of_h_eq_fst

end SSetRealizeHomotopyMapPrecompTests
end MathlibExtTest.AlgebraicTopology.ModelCategory
