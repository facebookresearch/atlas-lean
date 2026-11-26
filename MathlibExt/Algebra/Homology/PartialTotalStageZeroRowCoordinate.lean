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

public import MathlibExt.Algebra.Homology.PartialTotalHomologyCoordinates
public import MathlibExt.Algebra.Homology.PartialTotalSecondPageVerticalHomology
public import MathlibExt.Algebra.Homology.PartialTotalZero
public import MathlibExt.Algebra.Homology.PartialTotalSuccessor

/-!
# The stage-zero row coordinate

This file compares the canonical inclusion of row zero into the zeroth partial
total with the package-bound morphism from the literal bottom-to-zero spectral
homology object to the chosen first page. The structural coordinate factors
through the standard core via the invertible canonical spectral map, and the
resulting comparison identifies the row-zero composite with the chosen
first-page morphism. Its scope is the objectwise stage-zero row coordinate;
it asserts neither a filtration splitting nor a page-at-infinity object.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ComposableArrows
open CategoryTheory.Abelian.SpectralObject

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

/-- The canonical inclusion of row zero into the zeroth partial total. -/
noncomputable def partialTotalZeroRowToPartialTotal :
    B.X 0 ⟶ B.partialTotal 0 := by
  let T := B.firstStupidTrunc 0
  let eRow := B.partialTotalLastRowIso 0
  unfold partialTotal
  exact
    { f := fun q =>
        eRow.inv.f q ≫
          T.ιTotal (ComplexShape.down ℕ) 0 q q (Nat.zero_add q)
      comm' := by
        intro i j hij
        rw [HomologicalComplex₂.total_d, Preadditive.comp_add]
        simp only [Category.assoc]
        rw [T.ι_D₁, T.ι_D₂]
        rw [T.d₁_eq_zero (ComplexShape.down ℕ) 0 i j (by simp)]
        rw [T.d₂_eq (ComplexShape.down ℕ) 0 hij j (by simp)]
        have hε : ComplexShape.ε₂ (ComplexShape.down ℕ)
            (ComplexShape.down ℕ) (ComplexShape.down ℕ) (0, i) = 1 := by
          rfl
        rw [hε, one_smul]
        simp only [comp_zero, zero_add]
        exact HomologicalComplex.Hom.comm_assoc eRow.inv i j _ }


/-- The zero-row inclusion is the stage-zero partial-total cell coordinate. -/
@[simp]
theorem partialTotalZeroRowToPartialTotal_f (q : ℕ) :
    B.partialTotalZeroRowToPartialTotal.f q =
      B.partialTotalComponent 0 (0 : Fin 1) q q (Nat.zero_add q) := by
  set_option backward.isDefEq.respectTransparency false in
  unfold partialTotalZeroRowToPartialTotal partialTotalComponent
  dsimp only
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (B.partialTotalLastRowIso 0).inv.f q ≫
      (B.firstStupidTrunc 0).ιTotal
        (ComplexShape.down ℕ) 0 q q (Nat.zero_add q) = _
  rfl

/-- The zero-row inclusion into the partial total is natural in bicomplex
morphisms. -/
@[reassoc]
theorem partialTotalZeroRowToPartialTotal_naturality
    {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)}
    (φ : B ⟶ B') :
    φ.f 0 ≫ B'.partialTotalZeroRowToPartialTotal =
      B.partialTotalZeroRowToPartialTotal ≫ B.partialTotalHom φ 0 := by
  apply HomologicalComplex.hom_ext
  intro q
  simp only [HomologicalComplex.comp_f,
    partialTotalZeroRowToPartialTotal_f]
  exact (B.partialTotalComponent_naturality φ 0 (0 : Fin 1)
    q q (Nat.zero_add q)).symm

/-- Inclusion of the zeroth row into the full total complex. -/
noncomputable def partialTotalZeroRowToTotal :
    B.X 0 ⟶ B.total (ComplexShape.down ℕ) where
  f q := B.ιTotal (ComplexShape.down ℕ) 0 q q (Nat.zero_add q)
  comm' q q' h := by
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
      B.ι_D₁, B.ι_D₂]
    rw [B.d₁_eq_zero (ComplexShape.down ℕ) 0 q q' (by simp)]
    rw [B.d₂_eq (ComplexShape.down ℕ) 0 h q' (by simp)]
    simp

@[simp]
theorem partialTotalZeroRowToTotal_f (q : ℕ) :
    B.partialTotalZeroRowToTotal.f q =
      B.ιTotal (ComplexShape.down ℕ) 0 q q (Nat.zero_add q) :=
  rfl

/-- The zero-row partial-total inclusion factors the literal full-total
zero-row inclusion. -/
@[reassoc]
theorem partialTotalZeroRowToPartialTotal_comp_partialTotalι :
    B.partialTotalZeroRowToPartialTotal ≫ B.partialTotalι 0 =
      B.partialTotalZeroRowToTotal := by
  apply HomologicalComplex.hom_ext
  intro q
  simp only [HomologicalComplex.comp_f,
    partialTotalZeroRowToPartialTotal_f,
    partialTotalZeroRowToTotal_f]
  simpa using B.partialTotalComponent_comp_partialTotalι
    0 (0 : Fin 1) q q (Nat.zero_add q)

/-- The zero-row inclusion into the full total is natural in bicomplex
morphisms. -/
@[reassoc]
theorem partialTotalZeroRowToTotal_naturality
    {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)}
    (φ : B ⟶ B') :
    φ.f 0 ≫ B'.partialTotalZeroRowToTotal =
      B.partialTotalZeroRowToTotal ≫
        HomologicalComplex₂.total.map φ (ComplexShape.down ℕ) := by
  apply HomologicalComplex.hom_ext
  intro q
  simp only [HomologicalComplex.comp_f, partialTotalZeroRowToTotal_f]
  exact (HomologicalComplex₂.ιTotal_map
    (K := B) (L := B') (φ := φ) (c₁₂ := ComplexShape.down ℕ)
    0 q q (Nat.zero_add q)).symm

/-- The canonical StageZero source and stage coordinates, constructed
together with their homology compatibility. -/
noncomputable def partialTotalStageZeroSourceCoordinate (q : ℕ) :
    Σ eSource :
        ((B.partialTotalSpectralObject.H (-(q : ℤ))).obj
          (mk₁ (homOfLE
            (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ≅
        ((B.partialTotalSpectralObject.H ((core).deg (0, q))).obj
          (mk₁ (homOfLE
            (show (⊥ : EInt) ≤ (core).i₂ (0, q) by simp)))),
      { eStage :
          (B.partialTotalCochainFiltration.obj
              ((core).i₂ (0, q))).homology ((core).deg (0, q)) ≅
            ((B.partialTotal 0).extend
              ComplexShape.embeddingDownNat).homology ((core).deg (0, q)) //
        (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
            eSource.hom ≫
            (B.partialTotalSpectralObjectHObjIso
              ((core).deg (0, q))
              (show (⊥ : EInt) ≤ (core).i₂ (0, q) by simp)).hom =
          ((B.partialTotal 0).extendHomologyIso
            ComplexShape.embeddingDownNat (by
              rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
              change -(q : ℤ) = -(0 : ℤ) - (q : ℤ)
              omega)).inv ≫
          eStage.inv ≫
          (CochainComplex.mappingConeZeroSourceHomologyIso
            (B.partialTotalCochainFiltration.map
              (homOfLE
                (show (⊥ : EInt) ≤ (core).i₂ (0, q) by simp)))
            B.isZero_partialTotalCochainFiltration_obj_bot
            ((core).deg (0, q))).inv ∧
        HEq eStage
          (HomologicalComplex.homologyMapIso
            (B.partialTotalCochainFiltrationStageIso 0)
            ((core).deg (0, q))) ∧
        eSource.hom = eqToHom (by
          simp only [
            CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
          rw [show -(q : ℤ) = -(0 : ℤ) - (q : ℤ) by omega]
          simp only [Int.cast_ofNat_Int, Int.neg_zero]
          congr 1) } := by
  let coordinateOf (d : ℤ) (z : EInt)
      (hd : -(q : ℤ) = d)
      (hz : ((0 : ℤ) : EInt) = z) :
      Σ eSource :
          ((B.partialTotalSpectralObject.H (-(q : ℤ))).obj
            (mk₁ (homOfLE
              (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ≅
          ((B.partialTotalSpectralObject.H d).obj
            (mk₁ (homOfLE (show (⊥ : EInt) ≤ z by simp)))),
        { eStage :
            (B.partialTotalCochainFiltration.obj z).homology d ≅
              ((B.partialTotal 0).extend
                ComplexShape.embeddingDownNat).homology d //
          (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
              eSource.hom ≫
              (B.partialTotalSpectralObjectHObjIso d
                (show (⊥ : EInt) ≤ z by simp)).hom =
            ((B.partialTotal 0).extendHomologyIso
              ComplexShape.embeddingDownNat hd).inv ≫
            eStage.inv ≫
            (CochainComplex.mappingConeZeroSourceHomologyIso
              (B.partialTotalCochainFiltration.map
                (homOfLE (show (⊥ : EInt) ≤ z by simp)))
              B.isZero_partialTotalCochainFiltration_obj_bot d).inv ∧
          HEq eStage
            (HomologicalComplex.homologyMapIso
              (B.partialTotalCochainFiltrationStageIso 0) d) ∧
          eSource.hom = eqToHom (by
            subst d
            subst z
            rfl) } := by
    let eExtProvider :
        ((B.partialTotal 0).extend
          ComplexShape.embeddingDownNat).homology
            (ComplexShape.embeddingDownNat.f q) ≅
          (B.partialTotal 0).homology q :=
      (B.partialTotal 0).extendHomologyIso
        ComplexShape.embeddingDownNat rfl
    let eExtCoordinate :
        ((B.partialTotal 0).extend
          ComplexShape.embeddingDownNat).homology d ≅
          (B.partialTotal 0).homology q :=
      (B.partialTotal 0).extendHomologyIso
        ComplexShape.embeddingDownNat hd
    subst d
    subst z
    have hExt : eExtProvider = eExtCoordinate := by
      dsimp only [eExtProvider, eExtCoordinate]
      congr 1
    refine ⟨Iso.refl _, ?_⟩
    refine ⟨HomologicalComplex.homologyMapIso
      (B.partialTotalCochainFiltrationStageIso 0) (-(q : ℤ)),
      ?_, HEq.rfl, by rfl⟩
    let hProvider : (⊥ : EInt) ≤ ((0 : ℤ) : EInt) := by simp
    let hCoordinate : (⊥ : EInt) ≤ ((0 : ℤ) : EInt) := by simp
    let eProvider :=
      B.partialTotalSpectralObjectHObjIso
        (-(q : ℤ)) hProvider
    let eCoordinate :=
      B.partialTotalSpectralObjectHObjIso
        (-(q : ℤ)) hCoordinate
    have hHObj : eProvider = eCoordinate := by
      dsimp only [eProvider, eCoordinate]
    let eZeroProvider :=
      CochainComplex.mappingConeZeroSourceHomologyIso
        (B.partialTotalCochainFiltrationBottomStageMap 0)
        B.isZero_partialTotalCochainFiltration_obj_bot
        (-(q : ℤ))
    let eZeroCoordinate :=
      CochainComplex.mappingConeZeroSourceHomologyIso
        (B.partialTotalCochainFiltration.map
          (homOfLE hCoordinate))
        B.isZero_partialTotalCochainFiltration_obj_bot
        (-(q : ℤ))
    have hZero : eZeroProvider = eZeroCoordinate := by
      dsimp only [eZeroProvider, eZeroCoordinate,
        partialTotalCochainFiltrationBottomStageMap]
    rw [B.partialTotalSpectralStepHomologyIso_inv q 0]
    change
      ((eExtProvider.inv ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalCochainFiltrationStageIso 0)
          (-(q : ℤ))).inv ≫
        eZeroProvider.inv ≫
        eProvider.inv) ≫
          (Iso.refl _).hom ≫ eCoordinate.hom =
        eExtCoordinate.inv ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalCochainFiltrationStageIso 0)
          (-(q : ℤ))).inv ≫
        eZeroCoordinate.inv)
    rw [hExt]
    rw [hZero]
    rw [hHObj]
    simp only [Iso.refl_hom, Category.id_comp]
    have hAssoc :
        ((eExtCoordinate.inv ≫
          (HomologicalComplex.homologyMapIso
            (B.partialTotalCochainFiltrationStageIso 0)
            (-(q : ℤ))).inv ≫
          eZeroCoordinate.inv ≫
          eCoordinate.inv) ≫ eCoordinate.hom) =
        eExtCoordinate.inv ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalCochainFiltrationStageIso 0)
          (-(q : ℤ))).inv ≫
        eZeroCoordinate.inv ≫
        (eCoordinate.inv ≫ eCoordinate.hom) := by
      simp only [Category.assoc]
    calc
      ((eExtCoordinate.inv ≫
        (HomologicalComplex.homologyMapIso
          (B.partialTotalCochainFiltrationStageIso 0)
          (-(q : ℤ))).inv ≫
        eZeroCoordinate.inv ≫
        eCoordinate.inv) ≫ eCoordinate.hom) =
          eExtCoordinate.inv ≫
          (HomologicalComplex.homologyMapIso
            (B.partialTotalCochainFiltrationStageIso 0)
            (-(q : ℤ))).inv ≫
          eZeroCoordinate.inv ≫
          (eCoordinate.inv ≫ eCoordinate.hom) := hAssoc
      _ = eExtCoordinate.inv ≫
          (HomologicalComplex.homologyMapIso
            (B.partialTotalCochainFiltrationStageIso 0)
            (-(q : ℤ))).inv ≫
          eZeroCoordinate.inv := by
        simp only [eCoordinate.inv_hom_id, Category.comp_id]
  exact coordinateOf ((core).deg (0, q)) ((core).i₂ (0, q))
    (by
      rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
      change -(q : ℤ) = -(0 : ℤ) - (q : ℤ)
      omega)
    (by
      rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂]
      rfl)

/-- The bundled StageZero stage coordinate is the homology isomorphism
induced by the canonical finite-stage coordinate. -/
theorem partialTotalStageZeroSourceCoordinate_stageIso_heq (q : ℕ) :
    HEq (B.partialTotalStageZeroSourceCoordinate q).2.1
      (HomologicalComplex.homologyMapIso
        (B.partialTotalCochainFiltrationStageIso 0)
        ((core).deg (0, q))) :=
  (B.partialTotalStageZeroSourceCoordinate q).2.2.2.1

/-- The literal bottom-to-zero StageZero H-object is canonically identified
with the increasing-core bottom interval. -/
noncomputable def partialTotalStageZeroSourceIso (q : ℕ) :
    ((B.partialTotalSpectralObject.H (-(q : ℤ))).obj
      (mk₁ (homOfLE
        (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ≅
    ((B.partialTotalSpectralObject.H ((core).deg (0, q))).obj
      (mk₁ (homOfLE
        (show (⊥ : EInt) ≤ (core).i₂ (0, q) by simp)))) :=
  (B.partialTotalStageZeroSourceCoordinate q).1

/-- The StageZero source presentation is the canonical equality transport
from the literal bottom-to-zero H-object to the increasing-core H-object. -/
theorem partialTotalStageZeroSourceIso_hom_eqToHom (q : ℕ) :
    (B.partialTotalStageZeroSourceIso q).hom = eqToHom (by
      simp only [
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
      rw [show -(q : ℤ) = -(0 : ℤ) - (q : ℤ) by omega]
      simp only [Int.cast_ofNat_Int, Int.neg_zero]
      congr 1) := by
  simpa only [partialTotalStageZeroSourceIso] using
    (B.partialTotalStageZeroSourceCoordinate q).2.2.2.2

/-- The literal StageZero homology coordinate followed by the source
presentation agrees with the canonical bottom-cone homology coordinate. -/
theorem partialTotalStageZeroSourceIso_homology_compatibility (q : ℕ) :
    (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
        (B.partialTotalStageZeroSourceIso q).hom ≫
        (B.partialTotalSpectralObjectHObjIso
          ((core).deg (0, q))
          (show (⊥ : EInt) ≤ (core).i₂ (0, q) by simp)).hom =
      ((B.partialTotal 0).extendHomologyIso
        ComplexShape.embeddingDownNat (by
          rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
          change -(q : ℤ) = -(0 : ℤ) - (q : ℤ)
          omega)).inv ≫
      (B.partialTotalStageZeroSourceCoordinate q).2.1.inv ≫
      (CochainComplex.mappingConeZeroSourceHomologyIso
        (B.partialTotalCochainFiltration.map
          (homOfLE (show (⊥ : EInt) ≤ (core).i₂ (0, q) by simp)))
        B.isZero_partialTotalCochainFiltration_obj_bot
        ((core).deg (0, q))).inv := by
  simpa only [partialTotalStageZeroSourceIso] using
    (B.partialTotalStageZeroSourceCoordinate q).2.2.1

/-- The literal StageZero spectral object is canonically isomorphic to the
standard first-page core object. -/
noncomputable def partialTotalSpectralStepZeroCoreIso (q : ℕ) :
    ((B.partialTotalSpectralObject.H (-(q : ℤ))).obj
      (mk₁ (homOfLE
        (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ≅
    ((B.partialTotalSpectralObject.H ((core).deg (0, q))).obj
      (mk₁ (homOfLE ((core).le₁₂ (0, q))))) := by
  let Y := B.partialTotalSpectralObject
  let pq : ℕ × ℕ := (0, q)
  let d : ℤ := (core).deg pq
  let b : EInt := ⊥
  let m : EInt := (core).i₁ pq
  let z : EInt := (core).i₂ pq
  let hbm : b ≤ m := bot_le
  let hmz : m ≤ z := (core).le₁₂ pq
  let f₁ : b ⟶ m := homOfLE hbm
  let f₂ : m ⟶ z := homOfLE hmz
  let f₁₂ : b ⟶ z := homOfLE (hbm.trans hmz)
  let αCan : mk₁ f₁₂ ⟶ mk₁ f₂ :=
    twoδ₁Toδ₀' b m z hbm hmz
  have hm : m = (((-1 : ℤ) : EInt)) := by
    dsimp only [m, pq]
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁]
    congr 1
  have hZeroAt (k : ℤ) (x : EInt)
      (hx : x = (((-1 : ℤ) : EInt))) (hbx : (⊥ : EInt) ≤ x) :
      IsZero ((Y.H k).obj (mk₁ (homOfLE hbx))) := by
    subst x
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      k (-1) (by omega)
  have hZero₀ : IsZero ((Y.H d).obj (mk₁ f₁)) :=
    hZeroAt d m hm hbm
  have hZero₁ : IsZero ((Y.H (d + 1)).obj (mk₁ f₁)) :=
    hZeroAt (d + 1) m hm hbm
  let _ : IsIso ((Y.H d).map αCan) :=
    Y.isIso_H_map_twoδ₁Toδ₀'
      d (d + 1) rfl b m z hbm hmz hZero₀ hZero₁
  exact B.partialTotalStageZeroSourceIso q ≪≫
    asIso ((Y.H d).map αCan)

/-- The structural StageZero core isomorphism factors through the canonical
source presentation and the canonical spectral map. -/
theorem partialTotalSpectralStepZeroCoreIso_hom (q : ℕ) :
    (B.partialTotalSpectralStepZeroCoreIso q).hom =
      (B.partialTotalStageZeroSourceIso q).hom ≫
        (B.partialTotalSpectralObject.H ((core).deg (0, q))).map
          (twoδ₁Toδ₀' (⊥ : EInt)
            ((core).i₁ (0, q)) ((core).i₂ (0, q))
            bot_le ((core).le₁₂ (0, q))) := by
  rfl

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- The canonical morphism from the bottom-to-stage-zero spectral homology
object to the package-chosen first-page object in bidegree `(0,q)`. -/
noncomputable def partialTotalSpectralStepZeroToFirstPage (q : ℕ) :
    ((B.partialTotalSpectralObject.H (-(q : ℤ))).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ((0 : ℤ) : EInt) by simp)))) ⟶
      B.partialTotalFirstPageChoice.pageOne.X (0, q) :=
  (B.partialTotalSpectralStepZeroCoreIso q).hom ≫
    (B.partialTotalFirstPageChoice.firstPageCoreIsoAt 0 q).inv

private theorem partialTotalZeroRowToPartialTotal_comp_rowQuotient_f
    (n : ℕ) :
    ((B.partialTotalZeroRowToPartialTotal ≫
        B.partialTotalRowQuotient 0).f n) =
      (B.totalRowXIso 0 n n (Nat.zero_add n)).inv := by
  simp only [HomologicalComplex.comp_f,
    B.partialTotalZeroRowToPartialTotal_f]
  simpa using B.partialTotalComponent_comp_partialTotalRowQuotient
    0 n n (Nat.zero_add n)


private noncomputable def partialTotalZeroTotalRowIso :
    B.totalRow 0 ≅ B.X 0 :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ B.totalRowXIso 0 q q (Nat.zero_add q))
    (fun i j _ ↦ by
      rw [B.totalRow_d_eq 0 i j i j (Nat.zero_add i) (Nat.zero_add j)]
      simp)

private noncomputable def partialTotalZeroExtendCyclesIsoAt (q : ℕ) :
    (B.totalRow 0).cycles q ≅ (B.signedRow 0).cycles q := by
  let e := ComplexShape.embeddingDown'Add 1 0
  change ((B.signedRow 0).extend e).cycles q ≅
    (B.signedRow 0).cycles q
  exact (B.signedRow 0).extendCyclesIso e (by
    change q + 0 = q
    omega)

@[reassoc]
private theorem partialTotalZeroExtendCyclesIsoAt_hom_iCycles (q : ℕ) :
    (B.partialTotalZeroExtendCyclesIsoAt q).hom ≫
        (B.signedRow 0).iCycles q =
      (B.totalRow 0).iCycles q ≫
        (B.totalRowXIso 0 q q (Nat.zero_add q)).hom := by
  let e := ComplexShape.embeddingDown'Add 1 0
  let hq : e.f q = q := by
    change q + 0 = q
    omega
  change ((B.signedRow 0).extendCyclesIso e hq).hom ≫
      (B.signedRow 0).iCycles q =
    ((B.signedRow 0).extend e).iCycles q ≫
      ((B.signedRow 0).extendXIso e hq).hom
  exact HomologicalComplex.extendCyclesIso_hom_iCycles
    (K := B.signedRow 0) (e := e) (j := q) (j' := q) hq

private theorem partialTotalZero_cyclesMap_totalRowIso_hom (q : ℕ) :
    HomologicalComplex.cyclesMap
        (B.partialTotalZeroTotalRowIso).hom q =
      (B.partialTotalZeroExtendCyclesIsoAt q).hom ≫
        HomologicalComplex.cyclesMap (B.signedRowIso 0).hom q := by
  apply (cancel_mono ((B.X 0).iCycles q)).1
  rw [HomologicalComplex.cyclesMap_i]
  simp only [Category.assoc]
  rw [HomologicalComplex.cyclesMap_i]
  rw [B.partialTotalZeroExtendCyclesIsoAt_hom_iCycles_assoc q]
  simp only [partialTotalZeroTotalRowIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f]
  rw [B.signedRowIso_hom_f]
  change _ = _ ≫
    (((ComplexShape.down ℕ).ε 0) ^ q • 𝟙 ((B.X 0).X q))
  simp

private noncomputable def partialTotalZeroTotalRowCyclesIso (q : ℕ) :
    (B.totalRow 0).cycles q ≅ (B.X 0).cycles q :=
  HomologicalComplex.cyclesMapIso B.partialTotalZeroTotalRowIso q

@[reassoc]
private theorem partialTotalZeroTotalRowCyclesIso_hom_iCycles (q : ℕ) :
    (B.partialTotalZeroTotalRowCyclesIso q).hom ≫
        (B.X 0).iCycles q =
      (B.totalRow 0).iCycles q ≫
        (B.totalRowXIso 0 q q (Nat.zero_add q)).hom := by
  change HomologicalComplex.cyclesMap
      (B.partialTotalZeroTotalRowIso).hom q ≫
        (B.X 0).iCycles q =
    (B.totalRow 0).iCycles q ≫
      (B.partialTotalZeroTotalRowIso).hom.f q
  exact HomologicalComplex.cyclesMap_i
    (B.partialTotalZeroTotalRowIso).hom q

@[reassoc]
private theorem partialTotalZeroRowToPartialTotal_cycles_comp (q : ℕ) :
    let t := B.partialTotalZeroRowToPartialTotal ≫
      B.partialTotalRowQuotient 0
    HomologicalComplex.cyclesMap t q ≫
        (B.partialTotalZeroTotalRowCyclesIso q).hom =
      𝟙 ((B.X 0).cycles q) := by
  dsimp
  apply (cancel_mono ((B.X 0).iCycles q)).1
  simp only [Category.assoc]
  rw [B.partialTotalZeroTotalRowCyclesIso_hom_iCycles q]
  rw [HomologicalComplex.cyclesMap_i_assoc]
  rw [B.partialTotalZeroRowToPartialTotal_comp_rowQuotient_f q]
  simp only [Iso.inv_hom_id, Category.comp_id, Category.id_comp]

private noncomputable def partialTotalZeroTotalRowHomologyIso (q : ℕ) :
    (B.totalRow 0).homology q ≅ (B.X 0).homology q :=
  HomologicalComplex.homologyMapIso B.partialTotalZeroTotalRowIso q

@[reassoc]
private theorem partialTotalZero_homologyπ_comp_totalRowHomologyIsoAt_hom
    (q : ℕ) :
    (B.totalRow 0).homologyπ q ≫
        (B.totalRowHomologyIsoAt 0 q q (Nat.zero_add q)).hom =
      (B.partialTotalZeroExtendCyclesIsoAt q).hom ≫
        HomologicalComplex.cyclesMap (B.signedRowIso 0).hom q ≫
        (B.X 0).homologyπ q := by
  let e := ComplexShape.embeddingDown'Add 1 0
  let hq : e.f q = q := by
    change q + 0 = q
    omega
  change ((B.signedRow 0).extend e).homologyπ q ≫
      ((B.signedRow 0).extendHomologyIso e hq).hom ≫
      HomologicalComplex.homologyMap (B.signedRowIso 0).hom q =
    ((B.signedRow 0).extendCyclesIso e hq).hom ≫
      (HomologicalComplex.cyclesMap (B.signedRowIso 0).hom q ≫
        (B.X 0).homologyπ q)
  have hExt :
      ((B.signedRow 0).extend e).homologyπ q ≫
          ((B.signedRow 0).extendHomologyIso e hq).hom =
        ((B.signedRow 0).extendCyclesIso e hq).hom ≫
          (B.signedRow 0).homologyπ q :=
    HomologicalComplex.homologyπ_extendHomologyIso_hom
      (K := B.signedRow 0) (e := e) (j := q) (j' := q) hq
  rw [← Category.assoc, hExt, Category.assoc]
  rw [HomologicalComplex.homologyπ_naturality]

private theorem partialTotalZeroTotalRowHomologyIso_eq_at (q : ℕ) :
    B.partialTotalZeroTotalRowHomologyIso q =
      B.totalRowHomologyIsoAt 0 q q (Nat.zero_add q) := by
  apply Iso.ext
  apply (cancel_epi ((B.totalRow 0).homologyπ q)).1
  simp only [partialTotalZeroTotalRowHomologyIso,
    HomologicalComplex.homologyMapIso_hom]
  rw [HomologicalComplex.homologyπ_naturality]
  rw [B.partialTotalZero_cyclesMap_totalRowIso_hom q]
  rw [Category.assoc]
  rw [← B.partialTotalZero_homologyπ_comp_totalRowHomologyIsoAt_hom q]

@[reassoc]
private theorem partialTotalZero_homologyπ_comp_totalRowHomologyIso_hom
    (q : ℕ) :
    (B.totalRow 0).homologyπ q ≫
        (B.partialTotalZeroTotalRowHomologyIso q).hom =
      (B.partialTotalZeroTotalRowCyclesIso q).hom ≫
        (B.X 0).homologyπ q := by
  simpa only [partialTotalZeroTotalRowHomologyIso,
    partialTotalZeroTotalRowCyclesIso,
    HomologicalComplex.homologyMapIso_hom,
    HomologicalComplex.cyclesMapIso_hom] using
      (HomologicalComplex.homologyπ_naturality
        (K := B.totalRow 0) (L := B.X 0)
        (B.partialTotalZeroTotalRowIso).hom q)

private theorem partialTotalZeroRowToPartialTotal_homology_comp (q : ℕ) :
    HomologicalComplex.homologyMap
          (B.partialTotalZeroRowToPartialTotal ≫
            B.partialTotalRowQuotient 0) q ≫
        (B.partialTotalZeroTotalRowHomologyIso q).hom =
      𝟙 ((B.X 0).homology q) := by
  apply (cancel_epi ((B.X 0).homologyπ q)).1
  rw [Category.comp_id]
  simp only [HomologicalComplex.homologyπ_naturality_assoc]
  rw [B.partialTotalZero_homologyπ_comp_totalRowHomologyIso_hom q]
  rw [B.partialTotalZeroRowToPartialTotal_cycles_comp_assoc q]

private theorem
    partialTotalZeroRowToPartialTotal_homologyMap_comp_rowQuotient_chain
    (q : ℕ) :
    HomologicalComplex.homologyMap
          B.partialTotalZeroRowToPartialTotal q ≫
        HomologicalComplex.homologyMap
          (B.partialTotalRowQuotient 0) q =
      (B.partialTotalZeroTotalRowHomologyIso q).inv := by
  rw [← HomologicalComplex.homologyMap_comp]
  apply (cancel_mono (B.partialTotalZeroTotalRowHomologyIso q).hom).1
  rw [B.partialTotalZeroRowToPartialTotal_homology_comp q]
  exact (B.partialTotalZeroTotalRowHomologyIso q).inv_hom_id.symm

private theorem partialTotalZeroRowToPartialTotal_homologyMap_comp_rowQuotient_A5At
    (q : ℕ) :
    HomologicalComplex.homologyMap
          B.partialTotalZeroRowToPartialTotal q ≫
        HomologicalComplex.homologyMap
          (B.partialTotalRowQuotient 0) q =
      (B.totalRowHomologyIsoAt 0 q q (Nat.zero_add q)).inv := by
  rw [B.partialTotalZeroRowToPartialTotal_homologyMap_comp_rowQuotient_chain q]
  rw [B.partialTotalZeroTotalRowHomologyIso_eq_at q]

private theorem partialTotalFirstPageRowIsoAt_inv_core_prefix
    (q : ℕ) :
    let χ := B.partialTotalFirstPageChoice
    (χ.firstPageRowIsoAt 0 q q (Nat.zero_add q)).inv =
      (B.partialTotalStepE₁HomologyIsoAt
        0 q q (Nat.zero_add q)).inv ≫
      (B.partialTotalSpectralObjectHStepIso 0 q).inv ≫
      (χ.firstPageCoreIsoAt 0 q).inv := by
  dsimp only [PartialTotalFirstPageChoice.firstPageRowIsoAt,
    Iso.trans_inv]
  simp only [Category.assoc]


private theorem partialTotalSpectralStepZeroToFirstPage_B11At
    (q : ℕ) :
    let χ := B.partialTotalFirstPageChoice
    (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
        B.partialTotalSpectralStepZeroToFirstPage q =
      HomologicalComplex.homologyMap
          (B.partialTotalRowQuotient 0) q ≫
        (χ.firstPageRowIsoAt 0 q q (Nat.zero_add q)).inv := by
  dsimp only
  let χ := B.partialTotalFirstPageChoice
  let Y := B.partialTotalSpectralObject
  let F := B.partialTotalCochainFiltration
  let pq : ℕ × ℕ := (0, q)
  let b : EInt := ⊥
  let m : EInt := (core).i₁ pq
  let z : EInt := (core).i₂ pq
  let n₁ : ℤ := (core).deg pq
  let n₀ : ℤ := n₁ - 1
  let n₂ : ℤ := n₁ + 1
  have hn₁ : n₀ + 1 = n₁ := by omega
  have hn₂ : n₁ + 1 = n₂ := rfl
  have hbm : b ≤ m := bot_le
  have hmz : m ≤ z := (core).le₁₂ pq
  let f₁ : b ⟶ m := homOfLE hbm
  let f₂ : m ⟶ z := homOfLE hmz
  let f₁₂ : b ⟶ z := homOfLE (hbm.trans hmz)
  let αMinusOne : mk₁ f₁₂ ⟶ mk₁ f₂ :=
    homMk₁ f₁ (𝟙 z) (by subsingleton)
  let u₀ := F.map f₁₂
  let u₁ := F.map f₂
  let a := F.map f₁
  let d := 𝟙 (F.obj z)
  have hSquare : u₀ ≫ d = a ≫ u₁ := by
    dsimp only [d]
    rw [Category.comp_id]
    dsimp only [u₀, u₁, a]
    rw [← F.map_comp]
    apply F.congr_map
    subsingleton
  let coneAlpha :=
    CochainComplex.mappingCone.map u₀ u₁ a d hSquare
  have hConeAlpha :
      (HomotopyCategory.composableArrowsFunctor C).map
          ((F.mapComposableArrows 1).map αMinusOne) =
        coneAlpha := by
    dsimp only [coneAlpha, HomotopyCategory.composableArrowsFunctor]
    congr 2
    · change F.map (𝟙 _) = 𝟙 _
      exact F.map_id _
  let S := B.partialTotalStepCochainShortComplex 0
  let eStep := B.partialTotalE₁CochainStepIso 0 q
  let aStep := (eStep.app 0).hom
  let dStep := (eStep.app 1).hom
  have hStepSquare : u₁ ≫ dStep = aStep ≫ S.f := by
    exact CategoryTheory.ComposableArrows.naturality' eStep.hom 0 1
  let coneStep :=
    (HomotopyCategory.composableArrowsFunctor C).map eStep.hom
  have hConeStep :
      coneStep =
        CochainComplex.mappingCone.map
          u₁ S.f aStep dStep hStepSquare := by
    dsimp only [coneStep, HomotopyCategory.composableArrowsFunctor]
    congr 2
  let coneStepMap :=
    CochainComplex.mappingCone.map
      u₁ S.f aStep dStep hStepSquare
  have hConeStepMap : coneStep = coneStepMap := hConeStep
  have hInrAlpha :
      CochainComplex.mappingCone.inr u₀ ≫ coneAlpha =
        d ≫ CochainComplex.mappingCone.inr u₁ := by
    dsimp only [coneAlpha]
    rw [CochainComplex.mappingCone.map_eq_mapOfHomotopy]
    exact CochainComplex.mappingCone.triangleMapOfHomotopy_comm₂ _
  have hInrStep :
      CochainComplex.mappingCone.inr u₁ ≫ coneStep =
        dStep ≫ CochainComplex.mappingCone.inr S.f := by
    rw [hConeStep]
    rw [CochainComplex.mappingCone.map_eq_mapOfHomotopy]
    exact CochainComplex.mappingCone.triangleMapOfHomotopy_comm₂ _
  have hUpper :
      (B.partialTotalCochainFiltrationStageIso 0).inv ≫ dStep =
        𝟙 _ := by
    let E := ComplexShape.embeddingDownNat.extendFunctor C
    have hApp :
        eStep.app 1 =
          E.mapIso ((B.partialTotalE₁StepIso 0 q).app 1) := by
      apply Iso.ext
      change (𝟙 _ ≫
        E.map ((B.partialTotalE₁StepIso 0 q).app 1).hom ≫ 𝟙 _) =
          E.map ((B.partialTotalE₁StepIso 0 q).app 1).hom
      simp only [Category.id_comp, Category.comp_id]
    have hRaw :
        (B.partialTotalE₁StepIso 0 q).app 1 =
          B.partialTotalEIntFiltrationObjIso 0 :=
      eq_of_heq (B.partialTotalE₁StepIso_app_one_heq 0 q)
    have hDStep :
        dStep = (B.partialTotalCochainFiltrationStageIso 0).hom := by
      dsimp only [dStep]
      rw [hApp, hRaw]
      rfl
    rw [hDStep]
    exact (B.partialTotalCochainFiltrationStageIso 0).inv_hom_id
  have hQuotient :
      S.g ≫ (B.partialTotalStepCochainX₃Iso 0).hom =
        HomologicalComplex.extendMap
          (B.partialTotalRowQuotient 0)
            ComplexShape.embeddingDownNat := by
    exact eq_of_heq
      (B.partialTotalStepCochain_g_comp_X₃Iso_hom_heq 0)
  have hChain :
      (B.partialTotalCochainFiltrationStageIso 0).inv ≫
          CochainComplex.mappingCone.inr u₀ ≫
          coneAlpha ≫ coneStep ≫
          CochainComplex.mappingCone.descShortComplex S ≫
          (B.partialTotalStepCochainX₃Iso 0).hom =
        HomologicalComplex.extendMap
          (B.partialTotalRowQuotient 0)
            ComplexShape.embeddingDownNat := by
    let U := (B.partialTotal 0).extend ComplexShape.embeddingDownNat
    let M := F.obj (((0 : ℤ) : EInt))
    let stageInv : U ⟶ M :=
      (B.partialTotalCochainFiltrationStageIso 0).inv
    let inr₀ : M ⟶ CochainComplex.mappingCone u₀ :=
      CochainComplex.mappingCone.inr u₀
    let idM : M ⟶ M := 𝟙 M
    let inr₁ : M ⟶ CochainComplex.mappingCone u₁ :=
      CochainComplex.mappingCone.inr u₁
    let coneStep₀ : CochainComplex.mappingCone u₁ ⟶
        CochainComplex.mappingCone S.f := coneStep
    let dStep₀ : M ⟶ U := dStep
    let inrS : U ⟶ CochainComplex.mappingCone S.f :=
      CochainComplex.mappingCone.inr S.f
    have hInrAlpha₀ : inr₀ ≫ coneAlpha = idM ≫ inr₁ := by
      exact hInrAlpha
    have hInrStep₀ : inr₁ ≫ coneStep₀ = dStep₀ ≫ inrS := by
      exact hInrStep
    have hUpper₀ : stageInv ≫ dStep₀ = 𝟙 U := by
      exact hUpper
    have hUpperInr : stageInv ≫ (dStep₀ ≫ inrS) = inrS := by
      calc
        _ = (stageInv ≫ dStep₀) ≫ inrS := by
          exact (Category.assoc _ _ _).symm
        _ = (𝟙 U) ≫ inrS :=
          congrArg (fun k => k ≫ inrS) hUpper₀
        _ = _ := Category.id_comp _
    have hInrDesc :
        inrS ≫
            (CochainComplex.mappingCone.descShortComplex S ≫
              (B.partialTotalStepCochainX₃Iso 0).hom) =
          S.g ≫ (B.partialTotalStepCochainX₃Iso 0).hom := by
      calc
        _ = (CochainComplex.mappingCone.inr S.f ≫
              CochainComplex.mappingCone.descShortComplex S) ≫
            (B.partialTotalStepCochainX₃Iso 0).hom := by
          exact (Category.assoc _ _ _).symm
        _ = _ := congrArg
          (fun k => k ≫ (B.partialTotalStepCochainX₃Iso 0).hom)
          (CochainComplex.mappingCone.inr_descShortComplex S)
    change stageInv ≫ inr₀ ≫ coneAlpha ≫ coneStep₀ ≫
        CochainComplex.mappingCone.descShortComplex S ≫
        (B.partialTotalStepCochainX₃Iso 0).hom = _
    rw [reassoc_of% hInrAlpha₀]
    dsimp only [idM]
    simp only [Category.id_comp]
    rw [reassoc_of% hInrStep₀]
    rw [reassoc_of% hUpperInr]
    rw [hInrDesc]
    exact hQuotient
  have hChainHom :
      HomologicalComplex.homologyMap
          (B.partialTotalCochainFiltrationStageIso 0).inv n₁ ≫
        HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr u₀) n₁ ≫
        HomologicalComplex.homologyMap coneAlpha n₁ ≫
        HomologicalComplex.homologyMap coneStep n₁ ≫
        HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.descShortComplex S) n₁ ≫
        HomologicalComplex.homologyMap
          (B.partialTotalStepCochainX₃Iso 0).hom n₁ =
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (B.partialTotalRowQuotient 0)
            ComplexShape.embeddingDownNat) n₁ := by
    let U := (B.partialTotal 0).extend ComplexShape.embeddingDownNat
    let M := F.obj (((0 : ℤ) : EInt))
    let stageInv : U ⟶ M :=
      (B.partialTotalCochainFiltrationStageIso 0).inv
    let inr₀ : M ⟶ CochainComplex.mappingCone u₀ :=
      CochainComplex.mappingCone.inr u₀
    let coneStep₀ : CochainComplex.mappingCone u₁ ⟶
        CochainComplex.mappingCone S.f := coneStep
    change HomologicalComplex.homologyMap stageInv n₁ ≫
        HomologicalComplex.homologyMap inr₀ n₁ ≫
        HomologicalComplex.homologyMap coneAlpha n₁ ≫
        HomologicalComplex.homologyMap coneStep₀ n₁ ≫
        HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.descShortComplex S) n₁ ≫
        HomologicalComplex.homologyMap
          (B.partialTotalStepCochainX₃Iso 0).hom n₁ = _
    have h := congrArg
      (fun f => HomologicalComplex.homologyMap f n₁) hChain
    change HomologicalComplex.homologyMap
        (stageInv ≫ inr₀ ≫ coneAlpha ≫ coneStep₀ ≫
          CochainComplex.mappingCone.descShortComplex S ≫
          (B.partialTotalStepCochainX₃Iso 0).hom) n₁ = _ at h
    simpa only [HomologicalComplex.homologyMap_comp,
      Category.assoc] using h
  have hChainHomMap :
      HomologicalComplex.homologyMap
          (B.partialTotalCochainFiltrationStageIso 0).inv n₁ ≫
        HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr u₀) n₁ ≫
        HomologicalComplex.homologyMap coneAlpha n₁ ≫
        HomologicalComplex.homologyMap coneStepMap n₁ ≫
        HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.descShortComplex S) n₁ ≫
        HomologicalComplex.homologyMap
          (B.partialTotalStepCochainX₃Iso 0).hom n₁ =
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap
          (B.partialTotalRowQuotient 0)
            ComplexShape.embeddingDownNat) n₁ := by
    rw [← hConeStepMap]
    exact hChainHom
  have hH :
      (Y.H n₁).map αMinusOne ≫
          (B.partialTotalSpectralObjectHObjIso n₁ hmz).hom =
        (B.partialTotalSpectralObjectHObjIso
            n₁ (hbm.trans hmz)).hom ≫
          HomologicalComplex.homologyMap coneAlpha n₁ := by
    have h :=
      B.partialTotalSpectralObjectHObjIso_hom_naturality
        n₁ (hbm.trans hmz) hmz αMinusOne
    have hConeAlphaHom := congrArg
      (fun k => HomologicalComplex.homologyMap k n₁) hConeAlpha
    rw [hConeAlphaHom] at h
    exact h
  let eZero :=
    CochainComplex.mappingConeZeroSourceHomologyIso
      u₀ B.isZero_partialTotalCochainFiltration_obj_bot n₁
  have hZeroInv :
      eZero.inv =
        HomologicalComplex.homologyMap
          (CochainComplex.mappingCone.inr u₀) n₁ := by
    apply (cancel_mono eZero.hom).1
    rw [eZero.inv_hom_id]
    exact
      (CochainComplex.homologyMap_inr_comp_mappingConeZeroSourceHomologyIso_hom
        u₀ B.isZero_partialTotalCochainFiltration_obj_bot n₁).symm
  have hdeg : ComplexShape.embeddingDownNat.f q = n₁ := by
    dsimp only [n₁, pq]
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
    change -((q : ℕ) : ℤ) = -(0 : ℤ) - (q : ℤ)
    omega
  have hExt :=
    HomologicalComplex.extendHomologyIso_hom_naturality
      (φ := B.partialTotalRowQuotient 0)
      (e := ComplexShape.embeddingDownNat)
      (j := q) (j' := n₁) (hj' := hdeg)
  let αCan : mk₁ f₁₂ ⟶ mk₁ f₂ :=
    twoδ₁Toδ₀' b m z hbm hmz
  have hAlpha : αCan = αMinusOne := by
    apply hom_ext₁ <;> subsingleton
  have hm : m = (((-1 : ℤ) : EInt)) := by
    dsimp only [m, pq]
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁]
    congr 1
  have hZeroAt (k : ℤ) (x : EInt)
      (hx : x = (((-1 : ℤ) : EInt))) (hbx : (⊥ : EInt) ≤ x) :
      IsZero ((Y.H k).obj (mk₁ (homOfLE hbx))) := by
    subst x
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      k (-1) (by omega)
  have hZeroCan₀ : IsZero ((Y.H n₁).obj (mk₁ f₁)) :=
    hZeroAt n₁ m hm hbm
  have hZeroCan₁ : IsZero ((Y.H (n₁ + 1)).obj (mk₁ f₁)) :=
    hZeroAt (n₁ + 1) m hm hbm
  let _ : IsIso ((Y.H n₁).map αCan) :=
    Y.isIso_H_map_twoδ₁Toδ₀'
      n₁ (n₁ + 1) rfl b m z hbm hmz hZeroCan₀ hZeroCan₁
  let eMapCan := asIso ((Y.H n₁).map αCan)
  let eStage := (B.partialTotalStageZeroSourceCoordinate q).2.1
  let eExt :=
    (B.partialTotal 0).extendHomologyIso
      ComplexShape.embeddingDownNat hdeg
  let eCanH :=
    B.partialTotalSpectralObjectHObjIso n₁ (hbm.trans hmz)
  let eTargetH :=
    B.partialTotalSpectralObjectHObjIso n₁ hmz
  have hStageIso :
      eStage = HomologicalComplex.homologyMapIso
        (B.partialTotalCochainFiltrationStageIso 0) n₁ := by
    apply eq_of_heq
    dsimp only [eStage, n₁, pq]
    exact B.partialTotalStageZeroSourceCoordinate_stageIso_heq q
  have hStageInv :
      eStage.inv = HomologicalComplex.homologyMap
        (B.partialTotalCochainFiltrationStageIso 0).inv n₁ := by
    rw [hStageIso]
    exact HomologicalComplex.homologyMapIso_inv _ _
  have hHAlias :
      (Y.H n₁).map αMinusOne ≫ eTargetH.hom =
        eCanH.hom ≫
          HomologicalComplex.homologyMap coneAlpha n₁ := by
    dsimp only [eCanH, eTargetH]
    exact hH
  have hMapCan :
      eMapCan.hom = (Y.H n₁).map αMinusOne := by
    dsimp only [eMapCan]
    simp only [asIso_hom]
    rw [hAlpha]
  have hPresentationPrefix :
      (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
          (B.partialTotalSpectralStepZeroCoreIso q).hom ≫
          eMapCan.inv ≫ eCanH.hom =
        eExt.inv ≫ eStage.inv ≫ eZero.inv := by
    rw [B.partialTotalSpectralStepZeroCoreIso_hom q]
    have hCoreMap :
        (B.partialTotalSpectralObject.H ((core).deg (0, q))).map
            (twoδ₁Toδ₀' (⊥ : EInt)
              ((core).i₁ (0, q)) ((core).i₂ (0, q))
              bot_le ((core).le₁₂ (0, q))) =
          eMapCan.hom := by
      dsimp only [eMapCan]
      simp only [asIso_hom]
      rfl
    rw [hCoreMap]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have h :=
      B.partialTotalStageZeroSourceIso_homology_compatibility q
    dsimp only [eCanH, eExt, eStage, eZero, n₁, pq, z, f₁₂, u₀, F]
    simpa only using h
  have hSourceCone :
      (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
          (B.partialTotalSpectralStepZeroCoreIso q).hom ≫
          eTargetH.hom =
        eExt.inv ≫ eStage.inv ≫ eZero.inv ≫
          HomologicalComplex.homologyMap coneAlpha n₁ := by
    calc
      _ = (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
            (B.partialTotalSpectralStepZeroCoreIso q).hom ≫
            eMapCan.inv ≫ eMapCan.hom ≫ eTargetH.hom := by
          simp only [Iso.inv_hom_id_assoc]
      _ = (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
            (B.partialTotalSpectralStepZeroCoreIso q).hom ≫
            eMapCan.inv ≫ eCanH.hom ≫
              HomologicalComplex.homologyMap coneAlpha n₁ := by
          rw [hMapCan]
          rw [hHAlias]
      _ = eExt.inv ≫ eStage.inv ≫ eZero.inv ≫
            HomologicalComplex.homologyMap coneAlpha n₁ := by
          simpa only [Category.assoc] using congrArg
            (fun k => k ≫ HomologicalComplex.homologyMap coneAlpha n₁)
            hPresentationPrefix
  have hSourceConeLeft :
      (((B.partialTotalSpectralStepHomologyIso q 0).inv ≫
          (B.partialTotalSpectralStepZeroCoreIso q).hom) ≫
          eTargetH.hom) =
        eExt.inv ≫ eStage.inv ≫ eZero.inv ≫
          HomologicalComplex.homologyMap coneAlpha n₁ := by
    calc
      _ = (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
          (B.partialTotalSpectralStepZeroCoreIso q).hom ≫
          eTargetH.hom := Category.assoc _ _ _
      _ = _ := hSourceCone
  have hHStep :
      (B.partialTotalSpectralObjectHStepIso 0 q).hom =
        eTargetH.hom ≫
          HomologicalComplex.homologyMap coneStepMap n₁ := by
    dsimp only [partialTotalSpectralObjectHStepIso, eTargetH,
      coneStep, eStep, n₁, pq]
    change eTargetH.hom ≫
        HomologicalComplex.homologyMap coneStep n₁ =
      eTargetH.hom ≫
        HomologicalComplex.homologyMap coneStepMap n₁
    rw [hConeStepMap]
    rfl
  have hRow :
      (B.partialTotalStepE₁HomologyIsoAt
        0 q q (Nat.zero_add q)).hom =
        HomologicalComplex.homologyMap
            (CochainComplex.mappingCone.descShortComplex S) n₁ ≫
          HomologicalComplex.homologyMap
            (B.partialTotalStepCochainX₃Iso 0).hom n₁ ≫
          ((B.totalRow 0).extendHomologyIso
            ComplexShape.embeddingDownNat hdeg).hom := by
    dsimp only [partialTotalStepE₁HomologyIsoAt, S, n₁, pq]
    simp only [Iso.trans_hom,
      HomologicalComplex.homologyMapIso_hom, asIso_hom]
  have hPostPrefix :
      (((B.partialTotalSpectralStepHomologyIso q 0).inv ≫
          (B.partialTotalSpectralStepZeroCoreIso q).hom) ≫
          (B.partialTotalSpectralObjectHStepIso 0 q).hom) =
        ((eExt.inv ≫ eStage.inv ≫ eZero.inv ≫
          HomologicalComplex.homologyMap coneAlpha n₁) ≫
          HomologicalComplex.homologyMap coneStepMap n₁) := by
    calc
      _ = (((B.partialTotalSpectralStepHomologyIso q 0).inv ≫
            (B.partialTotalSpectralStepZeroCoreIso q).hom) ≫
            eTargetH.hom) ≫
          HomologicalComplex.homologyMap coneStepMap n₁ := by
        rw [hHStep]
        exact (Category.assoc _ _ _).symm
      _ = _ := congrArg
        (fun k => k ≫ HomologicalComplex.homologyMap coneStepMap n₁)
        hSourceConeLeft
  have hPost :
      (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
          (B.partialTotalSpectralStepZeroCoreIso q).hom ≫
          (B.partialTotalSpectralObjectHStepIso 0 q).hom ≫
          (B.partialTotalStepE₁HomologyIsoAt
            0 q q (Nat.zero_add q)).hom =
        HomologicalComplex.homologyMap
          (B.partialTotalRowQuotient 0) q := by
    simp only [← Category.assoc]
    rw [hPostPrefix, hRow]
    simp only [Category.assoc]
    have hChainCoordinate :
        eStage.inv ≫ eZero.inv ≫
          HomologicalComplex.homologyMap coneAlpha n₁ ≫
          HomologicalComplex.homologyMap coneStepMap n₁ ≫
          HomologicalComplex.homologyMap
            (CochainComplex.mappingCone.descShortComplex S) n₁ ≫
          HomologicalComplex.homologyMap
            (B.partialTotalStepCochainX₃Iso 0).hom n₁ =
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap
            (B.partialTotalRowQuotient 0)
              ComplexShape.embeddingDownNat) n₁ := by
      rw [hStageInv]
      rw [hZeroInv]
      exact hChainHomMap
    calc
      _ = eExt.inv ≫
          (eStage.inv ≫ eZero.inv ≫
            HomologicalComplex.homologyMap coneAlpha n₁ ≫
            HomologicalComplex.homologyMap coneStepMap n₁ ≫
            HomologicalComplex.homologyMap
              (CochainComplex.mappingCone.descShortComplex S) n₁ ≫
            HomologicalComplex.homologyMap
              (B.partialTotalStepCochainX₃Iso 0).hom n₁) ≫
          ((B.totalRow 0).extendHomologyIso
            ComplexShape.embeddingDownNat hdeg).hom := by
        simp only [Category.assoc]
      _ = eExt.inv ≫
          HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap
              (B.partialTotalRowQuotient 0)
                ComplexShape.embeddingDownNat) n₁ ≫
          ((B.totalRow 0).extendHomologyIso
            ComplexShape.embeddingDownNat hdeg).hom := by
        simpa only [Category.assoc] using congrArg
          (fun k => eExt.inv ≫ k ≫
            ((B.totalRow 0).extendHomologyIso
              ComplexShape.embeddingDownNat hdeg).hom)
          hChainCoordinate
      _ = HomologicalComplex.homologyMap
          (B.partialTotalRowQuotient 0) q := by
        dsimp only [eExt]
        simpa only [Category.assoc, Iso.inv_hom_id_assoc] using congrArg
          (fun k =>
            ((B.partialTotal 0).extendHomologyIso
              ComplexShape.embeddingDownNat hdeg).inv ≫ k)
          hExt
  have hPrefix :=
    B.partialTotalFirstPageRowIsoAt_inv_core_prefix q
  rw [hPrefix]
  unfold partialTotalSpectralStepZeroToFirstPage
  rw [← hPost]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]


/-- The fixed row-zero first-page coordinate is the stage-zero spectral
homology coordinate induced by the canonical row inclusion. -/
theorem
    partialTotalZeroRowToPartialTotal_homologyMap_comp_stepZeroToFirstPage
    (q : ℕ) :
    HomologicalComplex.homologyMap
          B.partialTotalZeroRowToPartialTotal q ≫
        (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
        B.partialTotalSpectralStepZeroToFirstPage q =
      (B.totalRowHomologyIsoAt 0 q q (Nat.zero_add q)).inv ≫
          (B.partialTotalFirstPageChoice.firstPageRowIsoAt
          0 q q (Nat.zero_add q)).inv := by
  rw [B.partialTotalSpectralStepZeroToFirstPage_B11At q]
  simp only [← Category.assoc]
  rw [B.partialTotalZeroRowToPartialTotal_homologyMap_comp_rowQuotient_A5At q]
end HomologicalComplex₂

end
