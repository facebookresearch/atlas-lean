/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Adapted from AxiomMath/Stacks at
c496df0d9beea9deaeabcea8492605f9a0a2313b:
* StacksFrontier/Homology/DerivedIndexing/Basic.lean;
* StacksFrontier/Homology/DerivedIndexing/Extend.lean.
Those sources are licensed under Apache 2.0 and carry no individual
author/copyright notice. Modification notice: retain the actual
injective-resolution comparison as a standalone object-level helper,
using the homotopy presentation of Mathlib's current bounded-below
derived unit.
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Classical right-derived cohomology and bounded-below derived functors

The two sides are computed on the same actual injective resolution.
The comparison uses its augmentation, the right-derived unit on its
injective terms, extension by zero and Mathlib's homology factorization.
No comparison is supplied as data.
-/

namespace MathlibExt.HomologicalAlgebra.RightDerivedCohomology

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open HomologicalComplex

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- The degreewise comparison, including the actual zero-object map
outside the original nonnegative indexing. -/
def mapExtendXIso (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ) :
    ∀ i : Option ℕ, extend.X ((F.mapHomologicalComplex (.up ℕ)).obj K) i ≅
      F.obj (extend.X K i)
  | some _ => Iso.refl _
  | none => F.mapZeroObject.symm

lemma mapExtendXIso_d (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ)
    (i j : Option ℕ) :
    (mapExtendXIso F K i).hom ≫ F.map (extend.d K i j) =
      extend.d ((F.mapHomologicalComplex (.up ℕ)).obj K) i j ≫
        (mapExtendXIso F K j).hom := by
  cases i with
  | none => exact (extend.isZero_X _ rfl).eq_of_src _ _
  | some a =>
    cases j with
    | none => exact (F.map_isZero (extend.isZero_X K rfl)).eq_of_tgt _ _
    | some b => exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Apply the additive functor before or after extension by zero. -/
def mapExtendedComplexIso (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  (Hom.isoOfComponents
    (fun i ↦ mapExtendXIso F K (ComplexShape.embeddingUpNat.r i))
    (fun _ _ _ ↦ mapExtendXIso_d F K _ _)).symm

/-- The actual extended resolution in the bounded-below homotopy category. -/
def resolutionHomotopyPlus {X : C} (I : InjectiveResolution X) : HomotopyCategory.Plus C :=
  ⟨(HomotopyCategory.quotient C (.up ℤ)).obj I.cochainComplex, by
    rw [HomotopyCategory.plus_quotient_obj_iff]
    exact ⟨0, inferInstance⟩⟩

variable [EnoughInjectives C] [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]

/-- The augmentation identifies X[0] with its resolution in D⁺. -/
def resolutionDerivedIso {X : C} (I : InjectiveResolution X) :
    (DerivedCategory.Plus.singleFunctor C 0).obj X ≅
      DerivedCategory.Plus.Qh.obj (resolutionHomotopyPlus I) := by
  have hi : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient C (.up ℤ)).map I.ι')) := by
    rw [DerivedCategory.isIso_Qh_map_iff,
      HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  exact DerivedCategory.Plus.ι.preimageIso
    ((DerivedCategory.Plus.singleFunctorιIso C 0).app X ≪≫
      (DerivedCategory.singleFunctorIsoCompQh C 0).app X ≪≫
        asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map I.ι')))

/-- Injective terms make the homotopy presentation of the actual
bounded-below derived unit invertible. -/
lemma resolutionUnitIsIso (F : C ⥤ D) [F.Additive] {X : C} (I : InjectiveResolution X) :
    IsIso (F.rightDerivedFunctorPlusUnith.app (resolutionHomotopyPlus I)) := by
  have (n : ℤ) : Injective ((resolutionHomotopyPlus I).obj.as.X n) :=
    inferInstanceAs (Injective (I.cochainComplex.X n))
  infer_instance

/-- The canonical comparison Hⁿ(RF(X[0])) ≅ RⁿF(X), with the actual
classical and bounded-below definitions. -/
def derivedCohomologyIso (F : C ⥤ D) [F.Additive] (X : C) (n : ℕ) :
    (DerivedCategory.homologyFunctor D (n : ℤ)).obj
      ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor C 0).obj X)) ≅
      (F.rightDerived n).obj X := by
  let I := injectiveResolution X
  let K := resolutionHomotopyPlus I
  let L := (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let H := DerivedCategory.homologyFunctor D (n : ℤ)
  let Hh := HomotopyCategory.homologyFunctor D (.up ℤ) (n : ℤ)
  have hi : IsIso (F.rightDerivedFunctorPlusUnith.app K) := resolutionUnitIsIso F I
  exact
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).mapIso
      (F.rightDerivedFunctorPlus.mapIso (resolutionDerivedIso I)) ≪≫
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).mapIso
      (asIso (F.rightDerivedFunctorPlusUnith.app K)).symm ≪≫
    H.mapIso ((DerivedCategory.Plus.QhCompιIsoιCompQh D).app
      (F.mapHomotopyCategoryPlus.obj K)) ≪≫
    (DerivedCategory.homologyFunctorFactorsh D (n : ℤ)).app
      (F.mapHomotopyCategoryPlus.obj K).obj ≪≫
    Hh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app I.cochainComplex) ≪≫
    (HomotopyCategory.homologyFunctorFactors D (.up ℤ) (n : ℤ)).app L ≪≫
    (HomologicalComplex.homologyFunctor D (.up ℤ) (n : ℤ)).mapIso
      (mapExtendedComplexIso F I.cocomplex) ≪≫
    ((F.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl ≪≫
    (I.isoRightDerivedObj F n).symm

end MathlibExt.HomologicalAlgebra.RightDerivedCohomology

