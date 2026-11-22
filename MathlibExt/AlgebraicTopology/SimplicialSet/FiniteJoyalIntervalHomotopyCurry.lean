/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalCylinder
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyTesting

/-!
# Currying the actual finite-interval homotopy classes

The native cartesian adjunction descends to the original generated homotopy
quotients. The associator and braiding transpose both endpoints of a chosen
interval homotopy, without a fibrancy hypothesis on any object. The resulting
equivalence retains its representative formulas and naturality on all classes.

This is a project prerequisite for product stability, using the homotopy
classes of Cisinski, Definition 2.4.14 (July 30, 2026, printed p.55 / PDF p.71).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed

universe u

namespace SSet.joyalInterval

private def cylinderPermutation (S A : SSet.{u}) :
    S ⊗ (joyalInterval ⊗ A) ≅ joyalInterval ⊗ (S ⊗ A) :=
  (α_ S joyalInterval A).symm ≪≫
    (tensorRight A).mapIso (β_ S joyalInterval) ≪≫ (α_ joyalInterval S A)

private lemma cylinderPermutation_endpoint (S A : SSet.{u}) (ε : Fin 2) :
    S ◁ (productPrecylinder.app A).endpoint ε ≫ (cylinderPermutation S A).hom =
      (productPrecylinder.app (S ⊗ A)).endpoint ε := by
  simp only [productPrecylinder_endpoint]
  apply CartesianMonoidalCategory.hom_ext
  · simp [cylinderPermutation]
  · apply CartesianMonoidalCategory.hom_ext <;> simp [cylinderPermutation]

private lemma endpoint_cylinderPermutation_inv (S A : SSet.{u}) (ε : Fin 2) :
    (productPrecylinder.app (S ⊗ A)).endpoint ε ≫ (cylinderPermutation S A).inv =
      S ◁ (productPrecylinder.app A).endpoint ε := by
  rw [← cylinderPermutation_endpoint S A ε]
  simp

private def curryLeftHomotopy {S A Q : SSet.{u}} {f g : S ⊗ A ⟶ Q}
    (H : (productPrecylinder.app (S ⊗ A)).LeftHomotopy f g) :
    (productPrecylinder.app A).LeftHomotopy (curry f) (curry g) where
  h := curry ((cylinderPermutation S A).hom ≫ H.h)
  h₀ := by
    change (productPrecylinder.app A).endpoint 0 ≫
      curry ((cylinderPermutation S A).hom ≫ H.h) = curry f
    rw [← curry_natural_left, ← Category.assoc, cylinderPermutation_endpoint]
    exact congrArg curry H.h₀
  h₁ := by
    change (productPrecylinder.app A).endpoint 1 ≫
      curry ((cylinderPermutation S A).hom ≫ H.h) = curry g
    rw [← curry_natural_left, ← Category.assoc, cylinderPermutation_endpoint]
    exact congrArg curry H.h₁

private def uncurryLeftHomotopy {S A Q : SSet.{u}} {f g : A ⟶ (ihom S).obj Q}
    (H : (productPrecylinder.app A).LeftHomotopy f g) :
    (productPrecylinder.app (S ⊗ A)).LeftHomotopy (uncurry f) (uncurry g) where
  h := (cylinderPermutation S A).inv ≫ uncurry H.h
  h₀ := by
    change (productPrecylinder.app (S ⊗ A)).endpoint 0 ≫
      (cylinderPermutation S A).inv ≫ uncurry H.h = uncurry f
    rw [← Category.assoc, endpoint_cylinderPermutation_inv, ← uncurry_natural_left]
    exact congrArg uncurry H.h₀
  h₁ := by
    change (productPrecylinder.app (S ⊗ A)).endpoint 1 ≫
      (cylinderPermutation S A).inv ≫ uncurry H.h = uncurry g
    rw [← Category.assoc, endpoint_cylinderPermutation_inv, ← uncurry_natural_left]
    exact congrArg uncurry H.h₁

private lemma elementaryHomotopyRel_curry_iff {S A Q : SSet.{u}}
    (f g : S ⊗ A ⟶ Q) :
    productPrecylinder.elementaryHomotopyRel f g ↔
      productPrecylinder.elementaryHomotopyRel (curry f) (curry g) := by
  constructor
  · rintro ⟨H⟩
    exact ⟨curryLeftHomotopy H⟩
  · rintro ⟨H⟩
    exact ⟨by simpa only [uncurry_curry] using uncurryLeftHomotopy H⟩

/-- The actual generated finite-interval homotopy quotient admits currying
for arbitrary simplicial sets, with its original morphism universe. -/
def homotopyClassCurryEquiv (S A Q : SSet.{u}) :
    productPrecylinder.HomotopyClass (S ⊗ A) Q ≃
      productPrecylinder.HomotopyClass A ((ihom S).obj Q) := by
  change Quot (@HomRel.CompClosure SSet _ productPrecylinder.elementaryHomotopyRel
      (S ⊗ A) Q) ≃
    Quot (@HomRel.CompClosure SSet _ productPrecylinder.elementaryHomotopyRel
      A ((ihom S).obj Q))
  exact Quot.congr ((ihom.adjunction S).homEquiv A Q) (by
    intro f g
    simp only [HomRel.compClosure_iff_self]
    exact elementaryHomotopyRel_curry_iff f g)

/-- On every representative, the class equivalence is native currying. -/
lemma homotopyClassCurryEquiv_apply_map {S A Q : SSet.{u}} (f : S ⊗ A ⟶ Q) :
    homotopyClassCurryEquiv S A Q (productPrecylinder.homotopyQuotientFunctor.map f) =
      productPrecylinder.homotopyQuotientFunctor.map (curry f) := rfl

/-- On every representative, its inverse is native uncurrying. -/
lemma homotopyClassCurryEquiv_symm_apply_map {S A Q : SSet.{u}}
    (f : A ⟶ (ihom S).obj Q) :
    (homotopyClassCurryEquiv S A Q).symm
        (productPrecylinder.homotopyQuotientFunctor.map f) =
      productPrecylinder.homotopyQuotientFunctor.map (uncurry f) := rfl

/-- Currying commutes with precomposition on every generated homotopy class. -/
lemma homotopyClassCurryEquiv_precomp (S : SSet.{u}) {A A' Q : SSet.{u}}
    (a : A' ⟶ A) (h : productPrecylinder.HomotopyClass (S ⊗ A) Q) :
    homotopyClassCurryEquiv S A' Q
        (productPrecylinder.homotopyClassPrecomp (S ◁ a) Q h) =
      productPrecylinder.homotopyClassPrecomp a ((ihom S).obj Q)
        (homotopyClassCurryEquiv S A Q h) := by
  obtain ⟨f, rfl⟩ := productPrecylinder.homotopyQuotientFunctor.map_surjective h
  simp only [HomotopicalAlgebra.Precylinder.homotopyClassPrecomp_map,
    homotopyClassCurryEquiv_apply_map, curry_natural_left]

end SSet.joyalInterval
