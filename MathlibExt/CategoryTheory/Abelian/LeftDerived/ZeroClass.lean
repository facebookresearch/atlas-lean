/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# Degree-zero classes and derived augmentations

The degree-zero derived map agrees with the resolution augmentation on
homology classes. The formula transports through a chain isomorphism
using the same quotient-class map.
-/

@[expose] public section

noncomputable section

universe u v a b

open CategoryTheory

namespace CategoryTheory.ProjectiveResolution


variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type a} [Category.{b} D] [Abelian D] {X : C}
  (P : ProjectiveResolution X) (F : C ⥤ D) [F.Additive]

/-- The zero-class projection followed by resolution
computation and the derived-zero map is the mapped augmentation. -/
theorem zeroClass_fromLeftDerivedZero :
    let K := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
    K.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ K).inv ≫ (P.isoLeftDerivedObj F 0).inv ≫
      F.fromLeftDerivedZero.app X = F.map (P.π.f 0) := by
  dsimp only
  rw [ProjectiveResolution.fromLeftDerivedZero_eq P F]
  rw [← Category.assoc (P.isoLeftDerivedObj F 0).inv (P.isoLeftDerivedObj F 0).hom,
    Iso.inv_hom_id, Category.id_comp]
  rw [← Category.assoc
    (ChainComplex.isoHomologyι₀ ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).inv
    (ChainComplex.isoHomologyι₀
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)).hom,
    Iso.inv_hom_id, Category.id_comp]
  exact ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero' P F

/-- An chain-coordinate isomorphism preserves that same native
derived-zero augmentation computation. -/
theorem zeroClass_fromLeftDerivedZero_of_iso (K : ChainComplex D ℕ)
    (e : K ≅ (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) :
    K.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ K).inv ≫ HomologicalComplex.homologyMap e.hom 0 ≫
      (P.isoLeftDerivedObj F 0).inv ≫ F.fromLeftDerivedZero.app X =
        e.hom.f 0 ≫ F.map (P.π.f 0) := by
  rw [ChainComplex.isoHomologyι₀_inv_naturality_assoc,
    HomologicalComplex.p_opcyclesMap_assoc]
  rw [zeroClass_fromLeftDerivedZero P F]
  rfl

end CategoryTheory.ProjectiveResolution
