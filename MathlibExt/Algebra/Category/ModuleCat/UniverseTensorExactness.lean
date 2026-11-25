/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.UniverseScalarRestriction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Closed module tensors in larger universes

Scalar restriction along the lift equivalence gives an exact equivalence
of module categories. Comparing tensor-left through this equivalence
provides its right adjoint and hence colimit preservation. The comparison
uses the scoped tensor structure in the same larger module universe.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace ModuleCat.UniverseScalarRestriction

variable (R : Type u) [CommRing R]


/-- The native ring-equivalence module equivalence in the actual common world. -/
def moduleEquivalence : (ModuleCat.{max u v} (LiftedRing.{u,v} R)) ≌ (Modules.{u,v} R) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv (scalarEquiv.{u,v} R)

/-- The actual inverse restriction of scalars, with coefficient action through down. -/
def toLifted : (Modules.{u,v} R) ⥤ (ModuleCat.{max u v} (LiftedRing.{u,v} R)) := (moduleEquivalence.{u,v} R).inverse


/-- The actual counit isomorphism of the original module representation. -/
def originalModuleIso (M : (Modules.{u,v} R)) : (toOriginal.{u,v} R).obj ((toLifted.{u,v} R).obj M) ≅ M :=
  (moduleEquivalence.{u,v} R).counitIso.app M

@[reassoc]
theorem originalModuleIso_inv_naturality {M N : (Modules.{u,v} R)} (f : M ⟶ N) :
    f ≫ (originalModuleIso.{u,v} R N).inv =
      (originalModuleIso.{u,v} R M).inv ≫ (toOriginal.{u,v} R).map ((toLifted.{u,v} R).map f) :=
  (moduleEquivalence.{u,v} R).counitIso.inv.naturality f

/-- The actual tensor-left functor is a conjugate of native tensor over
the actual lifted ring. Its comparison uses earned scalar/tensor isomorphisms. -/
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


/-- The actual original-ring tensor-left adjunction is transported from
the native lifted-ring tensor-left adjunction through an actual functor isomorphism. -/
def closed (M : (Modules.{u,v} R)) : Closed M := by
  let J := (toLifted.{u,v} R) ⋙ tensorLeft ((toLifted.{u,v} R).obj M) ⋙ (toOriginal.{u,v} R)
  letI : (toLifted.{u,v} R).IsEquivalence := (moduleEquivalence.{u,v} R).symm.isEquivalence_functor
  letI : J.IsLeftAdjoint := inferInstance
  exact
    { rightAdj := J.rightAdjoint
      adj := (Adjunction.ofIsLeftAdjoint J).ofNatIsoLeft (tensorLeftComparison.{u,v} R M).symm }

instance monoidalClosed : MonoidalClosed (Modules.{u,v} R) where
  closed M := closed.{u,v} R M

end ModuleCat.UniverseScalarRestriction
