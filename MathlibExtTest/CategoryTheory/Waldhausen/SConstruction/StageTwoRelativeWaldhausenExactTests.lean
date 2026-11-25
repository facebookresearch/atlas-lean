/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwoRelativeWaldhausenExact

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Waldhausen.SConstruction.StageTwoRelativeWaldhausenExactTests

open StageTwoRelativeWaldhausenExact

local instance stageZero {E : Type w} [Category.{z} E]
    [HasZeroObject E] [WaldhausenCategoryWithoutGluing E] (n : ℕ) : HasZeroObject (Stage E n) :=
  generalStageHasZeroObject E n

local instance stageValue {E : Type w} [Category.{z} E]
    [HasZeroObject E] [WaldhausenCategoryWithoutGluing E] (n : ℕ) : WaldhausenCategoryWithoutGluing (Stage E n) :=
  generalStageWaldhausenCategory E n

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

local instance cofiberValue : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
  CofiberSequenceCategory.relativeWaldhausenCategory C

example : (stageTwoFunctor C).IsWaldhausenExact := stageTwoFunctor_exact C
example : (stageTwoExtraction C).IsWaldhausenExact := stageTwoExtraction_exact C

example {S T : CofiberSequenceCategory C} (f : S ⟶ T)
    (hf : CofiberSequenceCategory.relativeCofibrations C f) :
    stageCofibrations C 2 ((stageTwoFunctor C).map f) := stageTwoFunctor_cofibrations C f hf

example {A B : Stage C 2} (f : A ⟶ B) (hf : stageCofibrations C 2 f) :
    CofiberSequenceCategory.relativeCofibrations C ((stageTwoExtraction C).map f) :=
  stageTwoExtraction_cofibrations C f hf

example {S T : CofiberSequenceCategory C} (f : S ⟶ T)
    (hf : CofiberSequenceCategory.levelwiseWeakEquivalences C f) :
    stageWeak C 2 ((stageTwoFunctor C).map f) := stageTwoFunctor_weak C f hf

example {A B : Stage C 2} (f : A ⟶ B) (hf : stageWeak C 2 f) :
    CofiberSequenceCategory.levelwiseWeakEquivalences C ((stageTwoExtraction C).map f) :=
  stageTwoExtraction_weak C f hf

example {S : CofiberSequenceCategory C} (hS : IsZero S) : IsZero ((stageTwoFunctor C).obj S) :=
  (stageTwoFunctor_exact C).map_isZero hS

example {A : Stage C 2} (hA : IsZero A) : IsZero ((stageTwoExtraction C).obj A) :=
  (stageTwoExtraction_exact C).map_isZero hA

example {S T S' P : CofiberSequenceCategory C} (i : S ⟶ T) (f : S ⟶ S') (l : S' ⟶ P) (r : T ⟶ P)
    (hi : IsCofibration i) (hp : IsPushout f i l r) :
    IsPushout ((stageTwoFunctor C).map f) ((stageTwoFunctor C).map i)
      ((stageTwoFunctor C).map l) ((stageTwoFunctor C).map r) :=
  (stageTwoFunctor_exact C).map_pushout i f l r hi hp

example {A B A' P : Stage C 2} (i : A ⟶ B) (f : A ⟶ A') (l : A' ⟶ P) (r : B ⟶ P)
    (hi : IsCofibration i) (hp : IsPushout f i l r) :
    IsPushout ((stageTwoExtraction C).map f) ((stageTwoExtraction C).map i)
      ((stageTwoExtraction C).map l) ((stageTwoExtraction C).map r) :=
  (stageTwoExtraction_exact C).map_pushout i f l r hi hp

example : (stageTwoEquivalence C).functor = stageTwoFunctor C := rfl
example : (stageTwoEquivalence C).inverse = stageTwoExtraction C := rfl

example : (stageTwoEquivalence C).functor.IsWaldhausenExact ∧
    (stageTwoEquivalence C).inverse.IsWaldhausenExact := stageTwoEquivalence_exact C

example : stageTwoFunctor C ⋙ eval C 2 (interval (0 : Fin 3) 1 (by decide)) =
    CofiberSequenceCategory.source C := stageTwoFunctor_source C

example : stageTwoFunctor C ⋙ eval C 2 (interval (0 : Fin 3) 2 (by decide)) =
    CofiberSequenceCategory.middle C := stageTwoFunctor_middle C

example : stageTwoFunctor C ⋙ eval C 2 (interval (1 : Fin 3) 2 (by decide)) =
    CofiberSequenceCategory.quotient C := stageTwoFunctor_quotient C

example : stageTwoExtraction C ⋙ CofiberSequenceCategory.source C =
    eval C 2 (interval (0 : Fin 3) 1 (by decide)) := stageTwoExtraction_source C

example : stageTwoExtraction C ⋙ CofiberSequenceCategory.middle C =
    eval C 2 (interval (0 : Fin 3) 2 (by decide)) := stageTwoExtraction_middle C

example : stageTwoExtraction C ⋙ CofiberSequenceCategory.quotient C =
    eval C 2 (interval (1 : Fin 3) 2 (by decide)) := stageTwoExtraction_quotient C

example (S : CofiberSequenceCategory C) (k : Fin 3) :
    ((stageTwoUnit C).hom.app S).hom.app k ≫ eqToHom (stageTwoUnit_column_object C S k) =
      𝟙 (S.obj.obj k) := stageTwoUnit_column_hom C S k

example (S : CofiberSequenceCategory C) (k : Fin 3) :
    eqToHom (stageTwoUnit_column_object C S k).symm ≫ ((stageTwoUnit C).inv.app S).hom.app k =
      𝟙 (S.obj.obj k) := stageTwoUnit_column_inv C S k

example (A : Stage C 2) (k : Fin 3) :
    eqToHom (stageTwoCounit_column_object C A k).symm ≫
        ((stageTwoCounit C).hom.app A).hom.app (triangleCell k) =
      𝟙 (A.obj.obj (triangleCell k)) := stageTwoCounit_column_hom C A k

example (A : Stage C 2) (k : Fin 3) :
    ((stageTwoCounit C).inv.app A).hom.app (triangleCell k) ≫
        eqToHom (stageTwoCounit_column_object C A k) =
      𝟙 (A.obj.obj (triangleCell k)) := stageTwoCounit_column_inv C A k

example (A : Stage C 2) (i : Fin 3) :
    eqToHom (stageTwoFunctor_obj_diag C ((stageTwoExtraction C).obj A) i).symm ≫
        ((stageTwoCounit C).hom.app A).hom.app (diag i) =
      (A.property.diag_isZero i).from_ (0 : C) := stageTwoCounit_diagonal_hom C A i

example (A : Stage C 2) (i : Fin 3) :
    ((stageTwoCounit C).inv.app A).hom.app (diag i) ≫
        eqToHom (stageTwoFunctor_obj_diag C ((stageTwoExtraction C).obj A) i) =
      (A.property.diag_isZero i).to_ (0 : C) := stageTwoCounit_diagonal_inv C A i

example {S T : CofiberSequenceCategory C} (f : S ⟶ T) (i : Fin 3) :
    eqToHom (stageTwoFunctor_obj_diag C S i).symm ≫
        ((stageTwoFunctor C).map f).hom.app (diag i) ≫
        eqToHom (stageTwoFunctor_obj_diag C T i) = 𝟙 (0 : C) := stageTwoFunctor_map_diag C f i

end CategoryTheory.Waldhausen.SConstruction.StageTwoRelativeWaldhausenExactTests

end
