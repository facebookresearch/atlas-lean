/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.FiniteFreeComplement
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.LinearAlgebra.Pi

/-!
# Natural isomorphisms from the regular finite projective generator

A natural transformation between additive functors out of finite
projectives is an isomorphism when its original regular component is.
Finite biproducts and actual projective retracts extend that one premise.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace FGProjectiveCat

variable {R : Type u} [Ring R]
variable {D : Type w} [Category.{v} D] [Preadditive D]
variable {F G : FGProjectiveCat.{u} R ⥤ D} [F.Additive] [G.Additive]

private theorem isIso_app_biprod (η : F ⟶ G) (P Q : FGProjectiveCat.{u} R)
    [IsIso (η.app P)] [IsIso (η.app Q)] : IsIso (η.app (P ⊞ Q)) := by
  let : PreservesBiproduct (pairFunction P Q) F := inferInstance
  let : PreservesBinaryBiproduct P Q F :=
    preservesBinaryBiproduct_of_preservesBiproduct F P Q
  let : PreservesBiproduct (pairFunction P Q) G := inferInstance
  let : PreservesBinaryBiproduct P Q G :=
    preservesBinaryBiproduct_of_preservesBiproduct G P Q
  have h : η.app (P ⊞ Q) ≫ (G.mapBiprod P Q).hom =
      (F.mapBiprod P Q).hom ≫ biprod.map (η.app P) (η.app Q) := by
    apply biprod.hom_ext
    · simpa only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, biprod.lift_fst_assoc,
        biprod.map_fst] using (η.naturality (biprod.fst : P ⊞ Q ⟶ P)).symm
    · simpa only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd, biprod.lift_snd_assoc,
        biprod.map_snd] using (η.naturality (biprod.snd : P ⊞ Q ⟶ Q)).symm
  have hIso : IsIso (η.app (P ⊞ Q) ≫ (G.mapBiprod P Q).hom) := by
    rw [h]
    change IsIso ((F.mapBiprod P Q).hom ≫
      (biprod.mapIso (asIso (η.app P)) (asIso (η.app Q))).hom)
    infer_instance
  exact ((MorphismProperty.isomorphisms D).cancel_right_of_respectsIso
    (η.app (P ⊞ Q)) (G.mapBiprod P Q).hom).mp hIso

private theorem standardFree_zero_isZero : IsZero (standardFree R 0) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply FGProjectiveCat.hom_ext
  ext x i
  exact Fin.elim0 i

private def standardFree_one_regularIso : standardFree R 1 ≅ regular R :=
  isoOfLinearEquiv (LinearEquiv.funUnique (Fin 1) R R)

private theorem isIso_app_standardFree (η : F ⟶ G)
    [IsIso (η.app (regular R))] (n : ℕ) : IsIso (η.app (standardFree R n)) := by
  induction n with
  | zero =>
      exact (Functor.map_isZero F standardFree_zero_isZero).isIso
        (Functor.map_isZero G standardFree_zero_isZero) (η.app (standardFree R 0))
  | succ n ih =>
      have : IsIso (η.app (standardFree R n)) := ih
      have : IsIso (η.app (standardFree R 1)) :=
        (η.isIso_app_iff_of_iso standardFree_one_regularIso).mpr inferInstance
      have : IsIso (η.app (standardFree R n ⊞ standardFree R 1)) :=
        isIso_app_biprod η _ _
      exact (η.isIso_app_iff_of_iso (standardFreeAddIso R n 1)).mpr inferInstance

/-- The actual regular component is the only generator isomorphism
premise needed for an additive natural transformation on finite projectives. -/
theorem isIso_natTrans_app_of_regular (η : F ⟶ G)
    [IsIso (η.app (regular R))] (P : FGProjectiveCat.{u} R) : IsIso (η.app P) := by
  obtain ⟨n, Q, ⟨e⟩⟩ := exists_biprod_iso_fin_free P
  have h : Retract P (standardFree R n) :=
    { i := biprod.inl ≫ e.hom
      r := e.inv ≫ biprod.fst
      retract := by simp }
  have : IsIso (η.app (standardFree R n)) := isIso_app_standardFree η n
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms D)
    (η.retractArrowApp h) inferInstance

/-- The original natural transformation becomes a natural isomorphism
from its original regular generator component. -/
def natIsoOfRegular (η : F ⟶ G) [IsIso (η.app (regular R))] : F ≅ G := by
  letI : ∀ P : FGProjectiveCat.{u} R, IsIso (η.app P) :=
    isIso_natTrans_app_of_regular η
  letI : IsIso η := NatIso.isIso_of_isIso_app η
  exact asIso η

/-- The earned natural isomorphism retains the literal original forward
natural transformation. -/
@[simp]
theorem natIsoOfRegular_hom (η : F ⟶ G) [IsIso (η.app (regular R))] :
    (natIsoOfRegular η).hom = η := rfl

end FGProjectiveCat

end
