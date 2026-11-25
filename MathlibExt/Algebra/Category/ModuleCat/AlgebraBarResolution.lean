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

public import MathlibExt.Algebra.Category.ModuleCat.AlgebraTensorAdjunction
public import MathlibExt.CategoryTheory.Monad.AdjunctionBarContraction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# The original canonical algebra Bar projective resolution

The simplicial object is the existing adjunction Bar of scalar tensor and
native restriction, evaluated at the original acting-algebra module. Its
augmentation is the original counit. Applying native restriction gives the
existing genuine forgotten extra degeneracy; exact conservative restriction
then reflects the augmentation quasi-isomorphism. Original ground freeness
of the acting algebra and coefficient earns degreewise projectivity of the
original Bar terms. No Bar differential or resolution certificate is supplied.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Monad AlgebraicTopology Opposite
open scoped TensorProduct ModuleCat.Algebra Simplicial

namespace ModuleCat.AlgebraBar

variable (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A]


/-- The original canonical adjunction Bar, evaluated at the original module. -/
def augmented (Y : (ModuleCat.{max u v w} A)) : SimplicialObject.Augmented (ModuleCat.{max u v w} A) :=
  (SimplicialObject.Augmented.whiskeringObj
    (ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} A) (ModuleCat.{max u v w} A)
    ((evaluation (ModuleCat.{max u v w} A) (ModuleCat.{max u v w} A)).obj Y)).obj
    (Monad.adjAugmented (AlgebraTensor.adjunction.{u, v, w} R A))

@[simp]
theorem augmented_point (Y : (ModuleCat.{max u v w} A)) : (augmented R A Y).right = Y := rfl

/-- The original native alternating-face complex of the canonical Bar. -/
def complex (Y : (ModuleCat.{max u v w} A)) : ChainComplex (ModuleCat.{max u v w} A) ℕ :=
  AlternatingFaceMapComplex.obj (augmented R A Y).left

/-- The original native Bar augmentation. -/
def augmentation (Y : ModuleCat.{max u v w} A) :
    complex R A Y ⟶ (ChainComplex.single₀ (ModuleCat.{max u v w} A)).obj Y :=
  AlternatingFaceMapComplex.ε.app (augmented R A Y)

@[simp]
theorem augmentation_f_zero (Y : (ModuleCat.{max u v w} A)) :
    (augmentation R A Y).f 0 = (AlgebraTensor.adjunction.{u, v, w} R A).counit.app Y := by
  rw [augmentation, AlternatingFaceMapComplex.ε_app_f_zero]
  unfold augmented
  rw [SimplicialObject.Augmented.whiskeringObj_obj_hom_app_mk,
    Monad.adjAugmented_hom_zero]
  rfl

/-- Original degree n is the original free module on the n-fold native
scalar tensor monad applied to the restricted original module. -/
theorem complex_X (Y : (ModuleCat.{max u v w} A)) (n : ℕ) :
    (complex R A Y).X n = (AlgebraTensor.functor.{u, v, w} R A).obj
      ((Monad.monadPow (AlgebraTensor.adjunction.{u, v, w} R A).toMonad n).obj
        ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y)) := rfl

/-- Native restriction of this original augmented Bar. -/
def forgotten (Y : (ModuleCat.{max u v w} A)) : SimplicialObject.Augmented (ModuleCat.{max u v w} R) :=
  (SimplicialObject.Augmented.whiskeringObj (ModuleCat.{max u v w} A) (ModuleCat.{max u v w} R)
    (ModuleCat.restrictScalars.{max u v w} (algebraMap R A))).obj (augmented R A Y)

/-- The existing adjunction Bar contraction is on this actual forgotten
canonical Bar, with no supplied extra-degeneracy data. -/
def forgottenExtra (Y : (ModuleCat.{max u v w} A)) : (forgotten R A Y).ExtraDegeneracy := by
  change (Monad.AdjunctionBarContraction.forgotten (AlgebraTensor.adjunction.{u, v, w} R A) Y).ExtraDegeneracy
  exact Monad.AdjunctionBarContraction.extra (AlgebraTensor.adjunction.{u, v, w} R A) Y

/-- Native alternating faces commute with exact scalar restriction. -/
def forgottenComplexIso (Y : (ModuleCat.{max u v w} A)) :
    ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (complex R A Y) ≅
      AlternatingFaceMapComplex.obj (forgotten R A Y).left :=
  (alternatingFaceMapComplexCompMapHomologicalComplexIso
    (ModuleCat.restrictScalars.{max u v w} (algebraMap R A))).app (augmented R A Y).left

/-- The comparison uses the original augmentation under native restriction. -/
theorem forgottenAugmentation_square (Y : (ModuleCat.{max u v w} A)) :
    ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (augmentation R A Y) ≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars.{max u v w} (algebraMap R A))
        (ComplexShape.down ℕ) 0).app Y).hom =
        (forgottenComplexIso R A Y).hom ≫
          AlternatingFaceMapComplex.ε.app (forgotten R A Y) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      let G : ModuleCat.{max u v w} A ⥤ ModuleCat.{max u v w} R :=
        ModuleCat.restrictScalars (algebraMap R A)
      change G.map ((augmented R A Y).hom.app (op ⦋0⦌)) ≫ 𝟙 _ =
        𝟙 _ ≫ G.map ((augmented R A Y).hom.app (op ⦋0⦌))
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
        ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y)
        (n + 1) (by omega)).eq_of_tgt _ _

local instance restriction_preservesHomology :
    (ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).PreservesHomology :=
  Functor.preservesHomologyOfExact (ModuleCat.restrictScalars.{max u v w} (algebraMap R A))

/-- The actual canonical Bar augmentation is a quasi-isomorphism. Its proof
uses the genuine forgotten extra degeneracy and conservative exact restriction. -/
theorem augmentation_quasiIso (Y : (ModuleCat.{max u v w} A)) : QuasiIso (augmentation R A Y) := by
  have hε : QuasiIso (AlternatingFaceMapComplex.ε.app (forgotten R A Y)) :=
    (forgottenExtra R A Y).homotopyEquiv.quasiIso_hom
  let e := (HomologicalComplex.singleMapHomologicalComplex
    (ModuleCat.restrictScalars.{max u v w} (algebraMap R A)) (ComplexShape.down ℕ) 0).app Y
  letI : QuasiIso (((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map
      (augmentation R A Y) ≫ e.hom) := by
    rw [forgottenAugmentation_square]
    exact quasiIso_comp
      (hφ := quasiIso_of_isIso ((forgottenComplexIso R A Y).hom)) (hφ' := hε) _ _
  have hmap : QuasiIso (((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map
      (augmentation R A Y)) :=
    quasiIso_of_comp_right (hφ := quasiIso_of_isIso e.hom) _ e.hom
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (augmentation R A Y) (ModuleCat.restrictScalars.{max u v w} (algebraMap R A))).mp hmap

/-- Actual native powers of scalar tensor preserve ground freeness when the
original algebra is ground-free. -/
theorem monadPow_moduleFree [Module.Free R A] (X : (ModuleCat.{max u v w} R)) [Module.Free R X] (n : ℕ) :
    Module.Free R ((Monad.monadPow (AlgebraTensor.adjunction.{u, v, w} R A).toMonad n).obj X) := by
  induction n with
  | zero =>
      change Module.Free R X
      infer_instance
  | succ n ih =>
      rw [Monad.monadPow_succ_obj_eq]
      letI : Module.Free R ((Monad.monadPow (AlgebraTensor.adjunction.{u, v, w} R A).toMonad n).obj X) := ih
      exact AlgebraTensor.groundObj_moduleFree R A
        ((Monad.monadPow (AlgebraTensor.adjunction.{u, v, w} R A).toMonad n).obj X)

/-- Ground freeness earns projectivity of every original native Bar term. -/
instance complex_projective [Module.Free R A] (Y : ModuleCat.{max u v w} A)
    [Module.Free R ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y)] (n : ℕ) :
    Projective ((complex R A Y).X n) := by
  rw [complex_X]
  letI : Module.Free R ((Monad.monadPow (AlgebraTensor.adjunction.{u, v, w} R A).toMonad n).obj
    ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y)) :=
    monadPow_moduleFree R A ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y) n
  exact AlgebraTensor.obj_projective R A _

/-- The actual original canonical Bar projective resolution, with exactness
and projectivity constructed from its original providers. -/
def projectiveResolution [Module.Free R A] (Y : ModuleCat.{max u v w} A)
    [Module.Free R ((ModuleCat.restrictScalars.{max u v w} (algebraMap R A)).obj Y)] :
    ProjectiveResolution Y where
  complex := complex R A Y
  projective := fun n => inferInstance
  π := augmentation R A Y
  quasiIso := augmentation_quasiIso R A Y

end ModuleCat.AlgebraBar
