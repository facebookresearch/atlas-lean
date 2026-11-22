/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalInterval

/-!
# Finite Joyal Interval
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet.FiniteJoyalIntervalTest

variable {X : SSet.{u}}

/-- Public clients can prescribe all five generators with distinct inverse inputs. -/
theorem realizesFullData (f g h : Δ[1] ⟶ X) (L R : Δ[2] ⟶ X)
    (hL₀ : SSet.stdSimplex.δ (0 : Fin 3) ≫ L = g)
    (hL₁ : SSet.stdSimplex.δ (1 : Fin 3) ≫ L = joyalInterval.constSource.{u} ≫ f)
    (hL₂ : SSet.stdSimplex.δ (2 : Fin 3) ≫ L = f)
    (hR₀ : SSet.stdSimplex.δ (0 : Fin 3) ≫ R = f)
    (hR₁ : SSet.stdSimplex.δ (1 : Fin 3) ≫ R = joyalInterval.constTarget.{u} ≫ f)
    (hR₂ : SSet.stdSimplex.δ (2 : Fin 3) ≫ R = h) :
    ∃! a : joyalInterval.{u} ⟶ X,
      joyalInterval.forward.{u} ≫ a = f ∧
      joyalInterval.leftInverse.{u} ≫ a = g ∧
      joyalInterval.rightInverse.{u} ≫ a = h ∧
      joyalInterval.leftTriangle.{u} ≫ a = L ∧
      joyalInterval.rightTriangle.{u} ≫ a = R :=
  joyalInterval.existsUnique_realization f g h L R hL₀ hL₁ hL₂ hR₀ hR₁ hR₂

/-- A map is recovered from its public generators, using the public face equations. -/
theorem recoveredFromTriangles (a : joyalInterval.{u} ⟶ X) :
    joyalInterval.desc
      (joyalInterval.forward.{u} ≫ a)
      (joyalInterval.leftTriangle.{u} ≫ a)
      (joyalInterval.rightTriangle.{u} ≫ a)
      (joyalInterval.δ_two_leftTriangle_assoc a)
      (joyalInterval.δ_one_leftTriangle_assoc a)
      (joyalInterval.δ_zero_rightTriangle_assoc a)
      (joyalInterval.δ_one_rightTriangle_assoc a) = a :=
  joyalInterval.hom_ext
    (joyalInterval.forward_desc ..)
    (joyalInterval.leftTriangle_desc ..)
    (joyalInterval.rightTriangle_desc ..)

end SSet.FiniteJoyalIntervalTest
