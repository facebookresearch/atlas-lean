/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowScalarCalibration
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Actual scalar coordinates of the original regular row successor

The successor adds the original rank-one object on the left, braids it
past the rank-n object, and uses the original free biproduct comparison.
The tensor/row biproduct square determines its scalar coordinate equation.
No regular-arrow compatibility or expected naturality equation is an input.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uR uS uC vC uD vD

namespace AlgebraicKTheory.StableGL

private theorem mapped_braiding
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] (X Y : C) :
    letI : PreservesBinaryBiproduct X Y F :=
      preservesBinaryBiproduct_of_preservesBiproduct F X Y
    letI : PreservesBinaryBiproduct Y X F :=
      preservesBinaryBiproduct_of_preservesBiproduct F Y X
    (F.mapBiprod X Y).inv ≫ F.map (biprod.braiding X Y).hom =
      (biprod.braiding (F.obj X) (F.obj Y)).hom ≫ (F.mapBiprod Y X).inv := by
  let : PreservesBinaryBiproduct X Y F :=
    preservesBinaryBiproduct_of_preservesBiproduct F X Y
  let : PreservesBinaryBiproduct Y X F :=
    preservesBinaryBiproduct_of_preservesBiproduct F Y X
  have hb : (biprod.braiding X Y).hom =
      biprod.desc (biprod.inr : X ⟶ Y ⊞ X) (biprod.inl : Y ⟶ Y ⊞ X) := by
    cat_disch
  rw [hb, biprod.mapBiprod_inv_map_desc, Functor.mapBiprod_inv]
  apply biprod.hom_ext' <;> cat_disch

private theorem oppositeIsoSquare
    {C : Type uC} [Category.{vC} C] {A B A' B' : C}
    (p : A ≅ B) (q : A' ≅ B') (e : A ≅ A') (m : B ≅ B')
    (h : p ≪≫ m = e ≪≫ q) :
    p.symm ≪≫ e = m ≪≫ q.symm := by
  apply Iso.ext
  apply (cancel_mono q.hom).1
  have hh := congrArg (fun i : A ≅ B' => p.inv ≫ i.hom) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using hh.symm

/-- The exact coordinate equation needed to transport the actual regular successor.
The source and target ring carriers remain independent. -/
public theorem finiteFreeRowScalarIso_successor_coordinates
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (n : ℕ) :
    let XR := fun i : ℕ => (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj i
    let XS := fun i : ℕ => (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj i
    let FR := (FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
      FGProjectiveCat.scalarExtension.{uR, uS, uR} f
    let FS := (FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
      (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse
    letI : PreservesBinaryBiproduct (XR 1) (XR n) FR :=
      preservesBinaryBiproduct_of_preservesBiproduct FR _ _
    letI : PreservesBinaryBiproduct (XS 1) (XS n) FS :=
      preservesBinaryBiproduct_of_preservesBiproduct FS _ _
    (FR.mapBiprod (XR 1) (XR n)).symm ≪≫
        FR.mapIso (biprod.braiding (XR 1) (XR n) ≪≫
          (FGProjectiveCat.IdempotentModel.freeBiprodIso R n 1).symm) ≪≫
        finiteFreeRowScalarIso f (n + 1) =
      biprod.mapIso (finiteFreeRowScalarIso f 1) (finiteFreeRowScalarIso f n) ≪≫
        (FS.mapBiprod (XS 1) (XS n)).symm ≪≫
        FS.mapIso (biprod.braiding (XS 1) (XS n) ≪≫
          (FGProjectiveCat.IdempotentModel.freeBiprodIso S n 1).symm) := by
  dsimp only
  let XR := fun i : ℕ => (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj i
  let XS := fun i : ℕ => (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks S)).obj i
  let FR := (FGProjectiveCat.IdempotentModel.equivalence R).functor ⋙
    FGProjectiveCat.scalarExtension.{uR, uS, uR} f
  let FS := (FGProjectiveCat.IdempotentModel.equivalence S).functor ⋙
    (FGProjectiveCat.universeEquivalence.{uS, uR} S).inverse
  let : PreservesBinaryBiproduct (XR 1) (XR n) FR :=
    preservesBinaryBiproduct_of_preservesBiproduct FR _ _
  let : PreservesBinaryBiproduct (XR n) (XR 1) FR :=
    preservesBinaryBiproduct_of_preservesBiproduct FR _ _
  let : PreservesBinaryBiproduct (XS 1) (XS n) FS :=
    preservesBinaryBiproduct_of_preservesBiproduct FS _ _
  let : PreservesBinaryBiproduct (XS n) (XS 1) FS :=
    preservesBinaryBiproduct_of_preservesBiproduct FS _ _
  let BR := FGProjectiveCat.IdempotentModel.freeBiprodIso R n 1
  let BS := FGProjectiveCat.IdempotentModel.freeBiprodIso S n 1
  let JR := FR.mapIso BR ≪≫ FR.mapBiprod (XR n) (XR 1)
  let JS := FS.mapIso BS ≪≫ FS.mapBiprod (XS n) (XS 1)
  let η := finiteFreeRowScalarIso f (n + 1)
  let M := biprod.mapIso (finiteFreeRowScalarIso f n) (finiteFreeRowScalarIso f 1)
  have hBP : JR ≪≫ M = η ≪≫ JS := by
    simpa only [JR, JS, BR, BS, η, M, FR, FS, XR, XS, Iso.trans_assoc] using
      (finiteFreeRowScalarIso_biproduct f n 1)
  have hInv := oppositeIsoSquare JR JS η M hBP
  have hInvHom :
      (FR.mapBiprod (XR n) (XR 1)).inv ≫ FR.map BR.inv ≫ η.hom =
        biprod.map (finiteFreeRowScalarIso f n).hom (finiteFreeRowScalarIso f 1).hom ≫
          (FS.mapBiprod (XS n) (XS 1)).inv ≫ FS.map BS.inv := by
    simpa only [JR, JS, M, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
      Functor.mapIso_inv, biprod.mapIso_hom, Category.assoc] using congrArg Iso.hom hInv
  have hR := mapped_braiding FR (XR 1) (XR n)
  have hS := mapped_braiding FS (XS 1) (XS n)
  have hM :
      (biprod.braiding (FR.obj (XR 1)) (FR.obj (XR n))).hom ≫
          biprod.map (finiteFreeRowScalarIso f n).hom (finiteFreeRowScalarIso f 1).hom =
        biprod.map (finiteFreeRowScalarIso f 1).hom (finiteFreeRowScalarIso f n).hom ≫
          (biprod.braiding (FS.obj (XS 1)) (FS.obj (XS n))).hom :=
    (biprod.braid_natural (finiteFreeRowScalarIso f 1).hom (finiteFreeRowScalarIso f n).hom).symm
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  change (FR.mapBiprod (XR 1) (XR n)).inv ≫ FR.map (biprod.braiding (XR 1) (XR n)).hom ≫
      FR.map BR.inv ≫ η.hom =
    biprod.map (finiteFreeRowScalarIso f 1).hom (finiteFreeRowScalarIso f n).hom ≫
      (FS.mapBiprod (XS 1) (XS n)).inv ≫ FS.map (biprod.braiding (XS 1) (XS n)).hom ≫ FS.map BS.inv
  calc
    _ = (biprod.braiding (FR.obj (XR 1)) (FR.obj (XR n))).hom ≫
        ((FR.mapBiprod (XR n) (XR 1)).inv ≫ FR.map BR.inv ≫ η.hom) := by
      simpa only [Category.assoc] using congrArg (fun h => h ≫ FR.map BR.inv ≫ η.hom) hR
    _ = (biprod.braiding (FR.obj (XR 1)) (FR.obj (XR n))).hom ≫
        (biprod.map (finiteFreeRowScalarIso f n).hom (finiteFreeRowScalarIso f 1).hom ≫
          (FS.mapBiprod (XS n) (XS 1)).inv ≫ FS.map BS.inv) :=
      congrArg (fun h => (biprod.braiding (FR.obj (XR 1)) (FR.obj (XR n))).hom ≫ h) hInvHom
    _ = (biprod.map (finiteFreeRowScalarIso f 1).hom (finiteFreeRowScalarIso f n).hom ≫
        (biprod.braiding (FS.obj (XS 1)) (FS.obj (XS n))).hom) ≫
          (FS.mapBiprod (XS n) (XS 1)).inv ≫ FS.map BS.inv := by
      simpa only [Category.assoc] using
        congrArg (fun h => h ≫ (FS.mapBiprod (XS n) (XS 1)).inv ≫ FS.map BS.inv) hM
    _ = biprod.map (finiteFreeRowScalarIso f 1).hom (finiteFreeRowScalarIso f n).hom ≫
        (FS.mapBiprod (XS 1) (XS n)).inv ≫ FS.map (biprod.braiding (XS 1) (XS n)).hom ≫
          FS.map BS.inv := by
      simpa only [Category.assoc] using congrArg
        (fun h => biprod.map (finiteFreeRowScalarIso f 1).hom (finiteFreeRowScalarIso f n).hom ≫
          h ≫ FS.map BS.inv) hS.symm

end AlgebraicKTheory.StableGL
