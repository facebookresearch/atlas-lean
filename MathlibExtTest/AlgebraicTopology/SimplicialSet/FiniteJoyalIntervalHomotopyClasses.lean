/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalHomotopyClasses

/-!
# Finite Joyal Interval Homotopy Classes
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory MonoidalClosed
open scoped Simplicial

universe u

namespace SSet.joyalInterval.HomotopyClassesTest

variable {A B C : SSet.{u}} [Quasicategory C]

/-- An actual ordinary isomorphism identifies the original generated classes. -/
theorem sameClass_of_isomorphism (f g : A ⟶ C)
    (e : (HomotopyCategory.mk (ihomVertexEquiv A C f) :
      hoFunctor.obj ((ihom A).obj C)) ≅
      HomotopyCategory.mk (ihomVertexEquiv A C g)) :
    productPrecylinder.homotopyQuotientFunctor.map f =
      productPrecylinder.homotopyQuotientFunctor.map g :=
  (homotopyClass_eq_iff_isIsomorphic f g).mpr ⟨e⟩

/-- Quotient equality yields an isomorphism, not just connected objects. -/
theorem isomorphism_of_sameClass (f g : A ⟶ C)
    (h : productPrecylinder.homotopyQuotientFunctor.map f =
      productPrecylinder.homotopyQuotientFunctor.map g) :
    Nonempty ((HomotopyCategory.mk (ihomVertexEquiv A C f) :
      hoFunctor.obj ((ihom A).obj C)) ≅
      HomotopyCategory.mk (ihomVertexEquiv A C g)) :=
  (homotopyClass_eq_iff_isIsomorphic f g).mp h

/-- The public naturality theorem gives the full commuting function square. -/
theorem precomposition_square (a : B ⟶ A) :
    (fun α : productPrecylinder.HomotopyClass A C ↦
      homotopyClassEquivIsomorphismClasses B C
        (productPrecylinder.homotopyClassPrecomp a C α)) =
      fun α ↦ isomorphismClasses.map (hoFunctor.map ((pre a).app C))
        (homotopyClassEquivIsomorphismClasses A C α) := by
  funext α
  exact homotopyClassEquivIsomorphismClasses_naturality a α

/-- Naturality also transports an arbitrary isomorphism class through the
inverse bijection. There is no monicity or source-quasicategory premise. -/
theorem inverse_precomposition (a : B ⟶ A)
    (β : isomorphismClasses.obj (hoFunctor.obj ((ihom A).obj C))) :
    productPrecylinder.homotopyClassPrecomp a C
        ((homotopyClassEquivIsomorphismClasses A C).symm β) =
      (homotopyClassEquivIsomorphismClasses B C).symm
        (isomorphismClasses.map (hoFunctor.map ((pre a).app C)) β) := by
  apply (homotopyClassEquivIsomorphismClasses B C).injective
  rw [homotopyClassEquivIsomorphismClasses_naturality]
  simp only [Equiv.apply_symm_apply]

/-- The zero-simplex source and a concrete quasicategory use the canonical
imports, vertex dictionary and representative formula. -/
theorem deltaZero_representative (f : (Δ[0] : SSet.{u}) ⟶ Δ[1]) :
    homotopyClassEquivIsomorphismClasses (Δ[0]) (Δ[1])
        (productPrecylinder.homotopyQuotientFunctor.map f) =
      _root_.Quotient.mk (isIsomorphicSetoid (hoFunctor.obj ((ihom (Δ[0])).obj (Δ[1]))))
        (HomotopyCategory.mk (ihomVertexEquiv (Δ[0]) (Δ[1]) f)) :=
  homotopyClassEquivIsomorphismClasses_map f

end SSet.joyalInterval.HomotopyClassesTest
