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

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Good-truncation roof for cochain complexes concentrated in degree zero

Double good truncation identifies with the single complex on degree-zero
homology. The resulting roof is natural for every cochain complex, and its
degree-zero homology coordinate is the identity in the canonical charts.
Vanishing of off-zero homology makes both roof arrows quasi-isomorphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

private def zeroDegreeHomologyIso (J : CochainComplex A ℤ)
    [J.IsStrictlyGE 0] [J.IsStrictlyLE 0] : J.X 0 ≅ J.homology 0 :=
  (J.iCyclesIso 0 1 ((ComplexShape.up ℤ).next_eq' (by rfl))
      ((J.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _)).symm ≪≫
    J.isoHomologyπ (-1) 0
      ((ComplexShape.up ℤ).prev_eq' (by change (-1 : ℤ) + 1 = 0; omega))
      ((J.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _)

private theorem iCycles_zeroDegreeHomologyIso (J : CochainComplex A ℤ)
    [J.IsStrictlyGE 0] [J.IsStrictlyLE 0] :
    J.iCycles 0 ≫ (zeroDegreeHomologyIso J).hom = J.homologyπ 0 := by
  simp [zeroDegreeHomologyIso]

private theorem homologyπ_zeroDegreeHomologyIso_inv (J : CochainComplex A ℤ)
    [J.IsStrictlyGE 0] [J.IsStrictlyLE 0] :
    J.homologyπ 0 ≫ (zeroDegreeHomologyIso J).inv = J.iCycles 0 := by
  rw [← cancel_mono (zeroDegreeHomologyIso J).hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, iCycles_zeroDegreeHomologyIso]

private theorem zeroDegreeHomologyIso_naturality
    {J J' : CochainComplex A ℤ} [J.IsStrictlyGE 0] [J.IsStrictlyLE 0]
    [J'.IsStrictlyGE 0] [J'.IsStrictlyLE 0] (f : J ⟶ J') :
    (zeroDegreeHomologyIso J).hom ≫ homologyMap f 0 =
      f.f 0 ≫ (zeroDegreeHomologyIso J').hom := by
  have : IsIso (J.iCycles 0) :=
    J.isIso_iCycles 0 1 ((ComplexShape.up ℤ).next_eq' (by rfl))
      ((J.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _)
  apply (cancel_epi (J.iCycles 0)).mp
  calc
    J.iCycles 0 ≫ ((zeroDegreeHomologyIso J).hom ≫ homologyMap f 0) =
        J.homologyπ 0 ≫ homologyMap f 0 := by
      rw [← Category.assoc, iCycles_zeroDegreeHomologyIso]
    _ = cyclesMap f 0 ≫ J'.homologyπ 0 := homologyπ_naturality f 0
    _ = cyclesMap f 0 ≫
        (J'.iCycles 0 ≫ (zeroDegreeHomologyIso J').hom) := by
      rw [iCycles_zeroDegreeHomologyIso]
    _ = J.iCycles 0 ≫ (f.f 0 ≫ (zeroDegreeHomologyIso J').hom) := by
      rw [← Category.assoc, cyclesMap_i, Category.assoc]

private def doubleTruncationComponentIso (K : CochainComplex A ℤ) :
    ((K.truncLE 0).truncGE 0).X 0 ≅ K.homology 0 :=
  zeroDegreeHomologyIso ((K.truncLE 0).truncGE 0) ≪≫
    (isoOfQuasiIsoAt ((K.truncLE 0).πTruncGE 0) 0).symm ≪≫
    isoOfQuasiIsoAt (K.ιTruncLE 0) 0

private theorem doubleTruncationComponentIso_naturality
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (truncGEMap (truncLEMap f 0) 0).f 0 ≫
        (doubleTruncationComponentIso L).hom =
      (doubleTruncationComponentIso K).hom ≫ homologyMap f 0 := by
  let fT := truncLEMap f 0
  let fQ := truncGEMap fT 0
  let pK := isoOfQuasiIsoAt ((K.truncLE 0).πTruncGE 0) 0
  let pL := isoOfQuasiIsoAt ((L.truncLE 0).πTruncGE 0) 0
  let iK := isoOfQuasiIsoAt (K.ιTruncLE 0) 0
  let iL := isoOfQuasiIsoAt (L.ιTruncLE 0) 0
  have hp : homologyMap fT 0 ≫ pL.hom = pK.hom ≫ homologyMap fQ 0 := by
    change homologyMap fT 0 ≫ homologyMap ((L.truncLE 0).πTruncGE 0) 0 =
      homologyMap ((K.truncLE 0).πTruncGE 0) 0 ≫ homologyMap fQ 0
    rw [← homologyMap_comp, ← homologyMap_comp]
    exact congrArg (fun g => homologyMap g 0) (πTruncGE_naturality fT 0).symm
  have hpInv : homologyMap fQ 0 ≫ pL.inv = pK.inv ≫ homologyMap fT 0 := by
    calc
      homologyMap fQ 0 ≫ pL.inv =
          pK.inv ≫ (pK.hom ≫ homologyMap fQ 0) ≫ pL.inv := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = pK.inv ≫ (homologyMap fT 0 ≫ pL.hom) ≫ pL.inv := by
        rw [← hp]
      _ = pK.inv ≫ homologyMap fT 0 := by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hi : homologyMap fT 0 ≫ iL.hom = iK.hom ≫ homologyMap f 0 := by
    change homologyMap fT 0 ≫ homologyMap (L.ιTruncLE 0) 0 =
      homologyMap (K.ιTruncLE 0) 0 ≫ homologyMap f 0
    rw [← homologyMap_comp, ← homologyMap_comp]
    exact congrArg (fun g => homologyMap g 0) (ιTruncLE_naturality f 0)
  dsimp only [doubleTruncationComponentIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  change fQ.f 0 ≫
      ((zeroDegreeHomologyIso ((L.truncLE 0).truncGE 0)).hom ≫ pL.inv ≫ iL.hom) =
    (zeroDegreeHomologyIso ((K.truncLE 0).truncGE 0)).hom ≫
      pK.inv ≫ iK.hom ≫ homologyMap f 0
  calc
    _ = (zeroDegreeHomologyIso ((K.truncLE 0).truncGE 0)).hom ≫
        homologyMap fQ 0 ≫ pL.inv ≫ iL.hom := by
      simpa only [Category.assoc] using
        congrArg (fun g => g ≫ pL.inv ≫ iL.hom)
          (zeroDegreeHomologyIso_naturality fQ).symm
    _ = (zeroDegreeHomologyIso ((K.truncLE 0).truncGE 0)).hom ≫
        pK.inv ≫ homologyMap fT 0 ≫ iL.hom := by
      simpa only [Category.assoc] using
        congrArg (fun g => (zeroDegreeHomologyIso ((K.truncLE 0).truncGE 0)).hom ≫
          g ≫ iL.hom) hpInv
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun g => (zeroDegreeHomologyIso ((K.truncLE 0).truncGE 0)).hom ≫
          pK.inv ≫ g) hi

/-- Canonical identification of double good truncation with the single complex on degree-zero homology. -/
def homologyZeroDoubleTruncationIso (K : CochainComplex A ℤ) :
    (K.truncLE 0).truncGE 0 ≅
      (single A (ComplexShape.up ℤ) 0).obj (K.homology 0) := by
  let Q := (K.truncLE 0).truncGE 0
  let e : Q.X 0 ≅ K.homology 0 :=
    ((Q.iCyclesIso 0 1 ((ComplexShape.up ℤ).next_eq' (by rfl))
        ((Q.isZero_of_isStrictlyLE 0 1 (by omega)).eq_of_tgt _ _)).symm ≪≫
      Q.isoHomologyπ (-1) 0
        ((ComplexShape.up ℤ).prev_eq' (by change (-1 : ℤ) + 1 = 0; omega))
        ((Q.isZero_of_isStrictlyGE 0 (-1) (by omega)).eq_of_src _ _)) ≪≫
      (isoOfQuasiIsoAt ((K.truncLE 0).πTruncGE 0) 0).symm ≪≫
        isoOfQuasiIsoAt (K.ιTruncLE 0) 0
  exact
    { hom := mkHomToSingle e.hom (by
        intro i hi
        exact (Q.isZero_of_isStrictlyGE 0 i (by
          change i + 1 = 0 at hi
          omega)).eq_of_src _ _)
      inv := mkHomFromSingle e.inv (by
        intro i hi
        exact (Q.isZero_of_isStrictlyLE 0 i (by
          change 0 + 1 = i at hi
          omega)).eq_of_tgt _ _)
      hom_inv_id := by
        apply HomologicalComplex.Hom.ext
        funext i
        by_cases hi : i = 0
        · subst i
          simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
            mkHomToSingle_f, mkHomFromSingle_f, Category.assoc,
            Iso.inv_hom_id_assoc, Iso.hom_inv_id]
        · by_cases hneg : i < 0
          · exact (Q.isZero_of_isStrictlyGE 0 i hneg).eq_of_src _ _
          · exact (Q.isZero_of_isStrictlyLE 0 i (by omega)).eq_of_src _ _
      inv_hom_id := by
        apply HomologicalComplex.Hom.ext
        funext i
        by_cases hi : i = 0
        · subst i
          simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
            mkHomToSingle_f, mkHomFromSingle_f, Category.assoc,
            Iso.inv_hom_id_assoc, Iso.hom_inv_id]
        · exact (isZero_single_obj_X (ComplexShape.up ℤ) 0 (K.homology 0) i hi).eq_of_src _ _ }

private theorem homologyZeroDoubleTruncationIso_hom_f_zero
    (K : CochainComplex A ℤ) :
    (homologyZeroDoubleTruncationIso K).hom.f 0 =
      (doubleTruncationComponentIso K).hom ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 (K.homology 0)).inv := by
  apply mkHomToSingle_f
  intro i hi
  exact (((K.truncLE 0).truncGE 0).isZero_of_isStrictlyGE 0 i (by
    change i + 1 = 0 at hi
    omega)).eq_of_src _ _

/-- Naturality of the double-truncation-to-single identification. -/
theorem homologyZeroDoubleTruncationIso_naturality
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    truncGEMap (truncLEMap f 0) 0 ≫ (homologyZeroDoubleTruncationIso L).hom =
      (homologyZeroDoubleTruncationIso K).hom ≫
        (single A (ComplexShape.up ℤ) 0).map (homologyMap f 0) := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = 0
  · subst i
    apply (cancel_mono (singleObjXSelf (ComplexShape.up ℤ) 0 (L.homology 0)).hom).mp
    simp only [HomologicalComplex.comp_f,
      homologyZeroDoubleTruncationIso_hom_f_zero, single_map_f_self,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact doubleTruncationComponentIso_naturality f
  · exact (isZero_single_obj_X (ComplexShape.up ℤ) 0 (L.homology 0) i hi).eq_of_tgt _ _

private theorem singleHomologyCoordinate_of_strictSupport
    (J : CochainComplex A ℤ) [J.IsStrictlyGE 0] [J.IsStrictlyLE 0]
    {B : A} (f : J ⟶ (single A (ComplexShape.up ℤ) 0).obj B) :
    homologyMap f 0 ≫ (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 B).hom =
      (zeroDegreeHomologyIso J).inv ≫ f.f 0 ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 B).hom := by
  apply (cancel_epi (J.homologyπ 0)).mp
  calc
    J.homologyπ 0 ≫
        (homologyMap f 0 ≫ (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 B).hom) =
      cyclesMap f 0 ≫
        (((single A (ComplexShape.up ℤ) 0).obj B).homologyπ 0 ≫
          (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 B).hom) := by
      rw [← Category.assoc, homologyπ_naturality, Category.assoc]
    _ = cyclesMap f 0 ≫
        (singleObjCyclesSelfIso (ComplexShape.up ℤ) 0 B).hom := by
      rw [homologyπ_singleObjHomologySelfIso_hom]
    _ = (J.iCycles 0 ≫ f.f 0) ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 B).hom := by
      rw [singleObjCyclesSelfIso_hom, ← Category.assoc, cyclesMap_i]
    _ = J.homologyπ 0 ≫
        ((zeroDegreeHomologyIso J).inv ≫ f.f 0 ≫
          (singleObjXSelf (ComplexShape.up ℤ) 0 B).hom) := by
      simpa only [Category.assoc] using
        congrArg (fun g => g ≫ f.f 0 ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 B).hom)
          (homologyπ_zeroDegreeHomologyIso_inv J).symm

/-- The single-complex homology coordinate is the inverse of the canonical truncation map. -/
theorem homologyZeroDoubleTruncationIso_homology_zero (K : CochainComplex A ℤ) :
    homologyMap (homologyZeroDoubleTruncationIso K).hom 0 ≫
        (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (K.homology 0)).hom =
      (isoOfQuasiIsoAt ((K.truncLE 0).πTruncGE 0) 0).inv ≫
        homologyMap (K.ιTruncLE 0) 0 := by
  rw [singleHomologyCoordinate_of_strictSupport,
    homologyZeroDoubleTruncationIso_hom_f_zero]
  dsimp only [doubleTruncationComponentIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The right roof arrow is the second good-truncation projection followed by the single-complex identification. -/
def homologyZeroRoofHom (K : CochainComplex A ℤ) :
    K.truncLE 0 ⟶ (single A (ComplexShape.up ℤ) 0).obj (K.homology 0) :=
  (K.truncLE 0).πTruncGE 0 ≫ (homologyZeroDoubleTruncationIso K).hom

/-- The left and right roof arrows give the same degree-zero homology coordinate. -/
@[reassoc]
theorem homologyZeroRoofHom_homology_zero (K : CochainComplex A ℤ) :
    homologyMap (homologyZeroRoofHom K) 0 ≫
        (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (K.homology 0)).hom =
      homologyMap (K.ιTruncLE 0) 0 := by
  rw [homologyZeroRoofHom, homologyMap_comp, Category.assoc,
    homologyZeroDoubleTruncationIso_homology_zero]
  exact (isoOfQuasiIsoAt ((K.truncLE 0).πTruncGE 0) 0).hom_inv_id_assoc _

/-- The degree-zero homology map is the identity under the canonical identifications. -/
theorem homologyZeroRoofHom_homology_identity (K : CochainComplex A ℤ) :
    (isoOfQuasiIsoAt (K.ιTruncLE 0) 0).inv ≫
        homologyMap (homologyZeroRoofHom K) 0 ≫
          (singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (K.homology 0)).hom =
      𝟙 (K.homology 0) := by
  rw [homologyZeroRoofHom_homology_zero]
  exact (isoOfQuasiIsoAt (K.ιTruncLE 0) 0).inv_hom_id

/-- The roof is natural in every cochain map. -/
@[reassoc]
theorem homologyZeroRoofHom_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    truncLEMap f 0 ≫ homologyZeroRoofHom L =
      homologyZeroRoofHom K ≫ (single A (ComplexShape.up ℤ) 0).map (homologyMap f 0) := by
  rw [homologyZeroRoofHom, homologyZeroRoofHom, ← Category.assoc,
    ← πTruncGE_naturality, Category.assoc,
    homologyZeroDoubleTruncationIso_naturality, ← Category.assoc]

/-- If homology vanishes away from degree zero, both roof arrows are quasi-isomorphisms. -/
theorem homologyZeroRoof_quasiIso (K : CochainComplex A ℤ)
    (hK : ∀ q : ℤ, q ≠ 0 → IsZero (K.homology q)) :
    QuasiIso (K.ιTruncLE 0) ∧ QuasiIso (homologyZeroRoofHom K) := by
  have hLE : K.IsLE 0 := by
    rw [isLE_iff]
    intro q hq
    rw [exactAt_iff_isZero_homology]
    exact hK q (by omega)
  let : K.IsLE 0 := hLE
  have hGE : (K.truncLE 0).IsGE 0 := by
    rw [isGE_iff]
    intro q hq
    rw [exactAt_iff_isZero_homology]
    have : QuasiIsoAt (K.ιTruncLE 0) q :=
      quasiIsoAt_ιTruncLE K 0 q (by omega)
    exact IsZero.of_iso (hK q (by omega)) (isoOfQuasiIsoAt (K.ιTruncLE 0) q)
  let : (K.truncLE 0).IsGE 0 := hGE
  constructor
  · infer_instance
  · unfold homologyZeroRoofHom
    infer_instance

end CochainComplex
