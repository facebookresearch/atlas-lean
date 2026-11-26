/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.UniverseScalarRestriction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Closed tensor functors after scalar-ring lifting

Let `R : Type u` be a commutative ring. Restriction along `R ≃+* ULift.{v} R` is an
equivalence between the module categories with coefficient universe `max u v`.

For a ground-scalar module `M`, the functor `M ⊗[R] -` is naturally isomorphic to inverse
scalar restriction, followed by tensoring with the lifted module over `ULift.{v} R`, followed
by scalar restriction back to `R`. Transporting the tensor–Hom adjunction along this
comparison makes the ground-scalar tensor category monoidal closed. In particular each left
tensor functor is a left adjoint and preserves colimits.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat.UniverseScalarRestriction

variable (R : Type u) [CommRing R]


/-- The module equivalence for lifted scalar rings.

The ring equivalence `R ≃+* ULift.{v} R` induces an equivalence from lifted-ring modules to
`R`-modules, both in coefficient universe `max u v`. -/
def moduleEquivalence : (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ≌ (Modules.{u,v} R) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (scalarEquiv.{u,v} R)

/-- The inverse restriction to lifted scalars.

The inverse of the module equivalence equips a ground-scalar module with the action of
`ULift.{v} R` through the down map. -/
def toLifted : (Modules.{u,v} R) ⥤ (ModuleCat.{max u v} (LiftedRing.{u,v} R)) := (moduleEquivalence.{u,v} R).inverse


/-- The counit comparison after lifting coefficient scalars.

For a ground-scalar module `M`, lifting its scalar action and restricting back gives an
`R`-module naturally isomorphic to `M`. -/
def originalModuleIso (M : (Modules.{u,v} R)) : (toOriginal.{u,v} R).obj ((toLifted.{u,v} R).obj M) ≅ M :=
  (moduleEquivalence.{u,v} R).counitIso.app M

/-- Naturality of the inverse scalar-lifting counit.

For `f : M → N`, applying `f` and then the inverse counit of `N` equals the inverse counit of
`M` followed by the lifted-and-restricted map. -/
@[reassoc]
theorem originalModuleIso_inv_naturality {M N : (Modules.{u,v} R)} (f : M ⟶ N) :
    f ≫ (originalModuleIso.{u,v} R N).inv =
      (originalModuleIso.{u,v} R M).inv ≫ (toOriginal.{u,v} R).map ((toLifted.{u,v} R).map f) :=
  (moduleEquivalence.{u,v} R).counitIso.inv.naturality f

/-- The scalar-lifting comparison for left tensor functors.

For a ground-scalar module `M`, `M ⊗[R] -` is naturally isomorphic to lifting scalars,
tensoring with the lifted `M` over `ULift.{v} R`, and restricting scalars back. -/
def tensorLeftComparison (M : (Modules.{u,v} R)) :
    tensorLeft M ≅ (toLifted.{u,v} R) ⋙ tensorLeft ((toLifted.{u,v} R).obj M) ⋙ (toOriginal.{u,v} R) :=
  NatIso.ofComponents (fun N =>
    ((originalModuleIso.{u,v} R M).symm ⊗ᵢ (originalModuleIso.{u,v} R N).symm) ≪≫
      tensorIso.{u,v} R ((toLifted.{u,v} R).obj M) ((toLifted.{u,v} R).obj N)) (by
        intro N N' f
        have ht : (𝟙 M ⊗ₘ f) ≫
            ((originalModuleIso.{u,v} R M).inv ⊗ₘ (originalModuleIso.{u,v} R N').inv) =
            ((originalModuleIso.{u,v} R M).inv ⊗ₘ (originalModuleIso.{u,v} R N).inv) ≫
              (𝟙 ((toOriginal.{u,v} R).obj ((toLifted.{u,v} R).obj M)) ⊗ₘ (toOriginal.{u,v} R).map
                ((toLifted.{u,v} R).map f)) := by
          rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
          simp only [Category.id_comp, Category.comp_id, originalModuleIso_inv_naturality]
        change ((𝟙 M ⊗ₘ f) ≫
            ((originalModuleIso.{u,v} R M).inv ⊗ₘ (originalModuleIso.{u,v} R N').inv)) ≫
            (tensorIso.{u,v} R ((toLifted.{u,v} R).obj M) ((toLifted.{u,v} R).obj N')).hom =
          ((originalModuleIso.{u,v} R M).inv ⊗ₘ (originalModuleIso.{u,v} R N).inv) ≫
            (tensorIso.{u,v} R ((toLifted.{u,v} R).obj M) ((toLifted.{u,v} R).obj N)).hom ≫
              (toOriginal.{u,v} R).map (𝟙 ((toLifted.{u,v} R).obj M) ⊗ₘ (toLifted.{u,v} R).map f)
        have hn := tensorIso_naturality.{u,v} R
          (𝟙 ((toLifted.{u,v} R).obj M)) ((toLifted.{u,v} R).map f)
        have hi := congrArg (fun z => z ⊗ₘ (toOriginal.{u,v} R).map ((toLifted.{u,v} R).map f))
          ((toOriginal.{u,v} R).map_id ((toLifted.{u,v} R).obj M))
        have hn' := (congrArg (fun z => z ≫
          (tensorIso.{u,v} R ((toLifted.{u,v} R).obj M) ((toLifted.{u,v} R).obj N')).hom)
            hi).symm.trans hn
        exact (congrArg (fun z => z ≫
          (tensorIso.{u,v} R ((toLifted.{u,v} R).obj M) ((toLifted.{u,v} R).obj N')).hom)
            ht).trans ((Category.assoc _ _ _).trans
              (congrArg (fun z =>
                ((originalModuleIso.{u,v} R M).inv ⊗ₘ (originalModuleIso.{u,v} R N).inv) ≫ z)
                  hn')))


/-- The right adjoint to tensoring with a universe scalar module.

For `M`, the lifted-ring tensor–Hom adjunction and the scalar-lifting comparison give a right
adjoint to `M ⊗[R] -` in the ground-scalar module category. -/
def closed (M : (Modules.{u,v} R)) : Closed M := by
  let J := (toLifted.{u,v} R) ⋙ tensorLeft ((toLifted.{u,v} R).obj M) ⋙ (toOriginal.{u,v} R)
  letI : (toLifted.{u,v} R).IsEquivalence := (moduleEquivalence.{u,v} R).symm.isEquivalence_functor
  letI : J.IsLeftAdjoint := inferInstance
  exact
    { rightAdj := J.rightAdjoint
      adj := (Adjunction.ofIsLeftAdjoint J).ofNatIsoLeft (tensorLeftComparison.{u,v} R M).symm }

/-- The monoidal closed structure on universe scalar modules.

Every left tensor functor in the module category with lifted regular unit has a right adjoint,
as obtained through the lifted-scalar equivalence. -/
instance monoidalClosed : MonoidalClosed (Modules.{u,v} R) where
  closed M := closed.{u,v} R M

end ModuleCat.UniverseScalarRestriction
