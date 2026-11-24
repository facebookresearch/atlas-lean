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

public import MathlibExt.Algebra.Homology.PartialTotalSecondPageVerticalHomology

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

example (m q : ℕ) :
    B.partialTotalE₁AdjacentCochainMap m q =
      (B.partialTotalAdjacentStepCochainIso m).inv ≫
        (B.partialTotalStepCochainShortComplex (m + 1)).f :=
  B.partialTotalE₁AdjacentCochainMap_eq m q

example (p p' q : ℕ) :
    (B.signedVerticalHomologyComplex q).d p p' =
      (ComplexShape.down ℕ).ε q •
        HomologicalComplex.homologyMap (B.d p p') q := by
  simp

example (p p' : ℕ) :
    (B.signedVerticalHomologyComplex 0).d p p' =
      HomologicalComplex.homologyMap (B.d p p') 0 := by
  simp

example (p p' : ℕ) :
    (B.signedVerticalHomologyComplex 1).d p p' =
      -HomologicalComplex.homologyMap (B.d p p') 1 := by
  simp

example (p q : ℕ) :
    (B.signedVerticalHomologyIso q).hom.f p =
      ((ComplexShape.down ℕ).ε q) ^ p •
        𝟙 ((B.X p).homology q) := by
  simp

example (p q : ℕ) :
    (B.signedVerticalHomologyIso q).inv.f p =
      (((ComplexShape.down ℕ).ε q) ^ p)⁻¹ •
        𝟙 ((B.X p).homology q) := by
  simp

example (p q : ℕ) :
    B.partialTotalHorizontalRowHomology p q ≫
        (B.totalRowHomologyIso p q).hom =
      (B.totalRowHomologyIso (p + 1) q).hom ≫
        (B.signedVerticalHomologyComplex q).d (p + 1) p :=
  B.partialTotalHorizontalRowHomology_totalRowHomologyIso p q

set_option backward.isDefEq.respectTransparency false in
example (p : ℕ) :
    B.partialTotalHorizontalRowHomology p 0 ≫
        (B.totalRowHomologyIso p 0).hom =
      (B.totalRowHomologyIso (p + 1) 0).hom ≫
        HomologicalComplex.homologyMap (B.d (p + 1) p) 0 := by
  simpa using
    B.partialTotalHorizontalRowHomology_totalRowHomologyIso p 0

set_option backward.isDefEq.respectTransparency false in
example (p : ℕ) :
    B.partialTotalHorizontalRowHomology p 1 ≫
        (B.totalRowHomologyIso p 1).hom =
      (B.totalRowHomologyIso (p + 1) 1).hom ≫
        (-HomologicalComplex.homologyMap (B.d (p + 1) p) 1) := by
  simpa only [signedVerticalHomologyComplex_d,
    ComplexShape.ε_down_ℕ, pow_one, Units.neg_smul, one_smul] using
    B.partialTotalHorizontalRowHomology_totalRowHomologyIso p 1

example (p q : ℕ) :
    ((((B.partialTotalSpectralObject.spectralSequence core).page 1).restriction
        (partialTotalFirstPageRowEmbedding q)).homology p) ≅
      ((B.partialTotalSpectralObject.spectralSequence core).page 1).homology
        (p, q) :=
  B.partialTotalFirstPageRowRestrictionHomologyIso p q

example (q : ℕ) :
    ((((B.partialTotalSpectralObject.spectralSequence core).page 1).restriction
        (partialTotalFirstPageRowEmbedding q)).homology 0) ≅
      ((B.partialTotalSpectralObject.spectralSequence core).page 1).homology
        (0, q) :=
  B.partialTotalFirstPageRowRestrictionHomologyIso 0 q

example (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).restriction
        (partialTotalFirstPageRowEmbedding q) ≅
      B.signedVerticalHomologyComplex q :=
  B.partialTotalFirstPageSignedVerticalHomologyIso q

example (p q : ℕ) :
    (B.partialTotalFirstPageSignedVerticalHomologyIso q).hom.f p =
      (B.partialTotalSpectralSequenceFirstPageRowIso p q).hom ≫
        (B.totalRowHomologyIso p q).hom :=
  B.partialTotalFirstPageSignedVerticalHomologyIso_hom_f p q

example (p q : ℕ) :
    (B.partialTotalFirstPageSignedVerticalHomologyIso q).inv.f p =
      (B.totalRowHomologyIso p q).inv ≫
        (B.partialTotalSpectralSequenceFirstPageRowIso p q).inv :=
  B.partialTotalFirstPageSignedVerticalHomologyIso_inv_f p q

example (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).restriction
        (partialTotalFirstPageRowEmbedding q) ≅
      B.verticalHomologyComplex q :=
  B.partialTotalFirstPageVerticalHomologyIso q

example (p q : ℕ) : C :=
  B.partialTotalSpectralSequencePageTwoCoordinate p q

example : C :=
  B.partialTotalSpectralSequencePageTwoCoordinate 0 0

example (p q : ℕ) : C :=
  HomologicalComplex₂.partialTotalSpectralSequencePageTwoCoordinate
    (B := (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))) p q

example (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page (2 : ℤ)).X
        (p, q) ≅
      B.partialTotalSpectralSequencePageTwoCoordinate p q :=
  B.partialTotalSpectralSequencePageTwoIso p q

example (p : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page (2 : ℤ)).X
        (p, 0) ≅
      B.partialTotalSpectralSequencePageTwoCoordinate p 0 :=
  B.partialTotalSpectralSequencePageTwoIso p 0

example (p : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page (2 : ℤ)).X
        (p, 1) ≅
      B.partialTotalSpectralSequencePageTwoCoordinate p 1 :=
  B.partialTotalSpectralSequencePageTwoIso p 1

example (p q : ℕ) :=
  HomologicalComplex₂.partialTotalSpectralSequencePageTwoIso
    (B := (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))) p q

example (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page (1 : ℤ)).homology
        (p, q) ≅
      B.partialTotalSpectralSequencePageTwoCoordinate p q :=
  B.partialTotalSpectralSequencePageOneHomologyCoordinateIso p q

example (p : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page (1 : ℤ)).homology
        (p, 0) ≅
      B.partialTotalSpectralSequencePageTwoCoordinate p 0 :=
  B.partialTotalSpectralSequencePageOneHomologyCoordinateIso p 0

example (p : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page (1 : ℤ)).homology
        (p, 1) ≅
      B.partialTotalSpectralSequencePageTwoCoordinate p 1 :=
  B.partialTotalSpectralSequencePageOneHomologyCoordinateIso p 1

example (p q : ℕ) :=
  HomologicalComplex₂.partialTotalSpectralSequencePageOneHomologyCoordinateIso
    (B := (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))) p q

example (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 1).homology
        (p, q) ≅
      ((B.partialTotalSpectralObject.spectralSequence core).page 2).X
        (p, q) :=
  B.partialTotalSpectralSequencePageOneTwoIso p q

example (p q : ℕ) :
    B.partialTotalSpectralSequencePageOneTwoIso p q =
      B.partialTotalSpectralSequencePageOneHomologyCoordinateIso p q ≪≫
        (B.partialTotalSpectralSequencePageTwoIso p q).symm := by
  rfl

example (q : ℕ) :
    (B.partialTotalSpectralSequencePageOneTwoIso 0 q).hom ≫
        (B.partialTotalSpectralSequencePageTwoIso 0 q).hom =
      (B.partialTotalSpectralSequencePageOneHomologyCoordinateIso 0 q).hom :=
  B.partialTotalSpectralSequencePageOneTwoIso_zero_hom_comp_pageTwoIso_hom q

example :
    (B.partialTotalSpectralSequencePageOneTwoIso 0 0).hom ≫
        (B.partialTotalSpectralSequencePageTwoIso 0 0).hom =
      (B.partialTotalSpectralSequencePageOneHomologyCoordinateIso 0 0).hom :=
  B.partialTotalSpectralSequencePageOneTwoIso_zero_hom_comp_pageTwoIso_hom 0

example :
    (B.partialTotalSpectralSequencePageOneTwoIso 0 1).hom ≫
        (B.partialTotalSpectralSequencePageTwoIso 0 1).hom =
      (B.partialTotalSpectralSequencePageOneHomologyCoordinateIso 0 1).hom :=
  B.partialTotalSpectralSequencePageOneTwoIso_zero_hom_comp_pageTwoIso_hom 1

example (q : ℕ) :=
  HomologicalComplex₂.partialTotalSpectralSequencePageOneTwoIso_zero_hom_comp_pageTwoIso_hom
    (B := (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))) q

example (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page 2).X
        (p, q) ≅
      (B.verticalHomologyComplex q).homology p :=
  B.partialTotalSecondPageVerticalHomologyIso p q

example :
    ((B.partialTotalSpectralObject.spectralSequence core).page 2).X
        (0, 0) ≅
      (B.verticalHomologyComplex 0).homology 0 :=
  B.partialTotalSecondPageVerticalHomologyIso 0 0

example (p q : ℕ) :
    (B.partialTotalSecondPageVerticalHomologyIso p q).hom =
      (B.partialTotalSpectralSequencePageOneTwoIso p q).inv ≫
        (B.partialTotalFirstPageRowRestrictionHomologyIso p q).inv ≫
        HomologicalComplex.homologyMap
          (B.partialTotalFirstPageVerticalHomologyIso q).hom p :=
  B.partialTotalSecondPageVerticalHomologyIso_hom p q


unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
example (χ : PartialTotalFirstPageChoice B)
    (p q : ℕ) (k : EInt)
    (hk : k = (core).i₁ (p, q))
    (n₀ n₂ : ℤ)
    (hn₀ : n₀ + 1 = (core).deg (p, q))
    (hn₂ : (core).deg (p, q) + 1 = n₂) :
    let Y := B.partialTotalSpectralObject
    χ.firstPageCoreIsoAtOfCut p q k hk n₀ n₂ hn₀ hn₂ =
      (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
          Y core 1 χ.pageOneBound (p, q)
          k k ((core).i₂ (p, q)) ((core).i₂ (p, q))
          (by rw [hk, ← (core).hi₀₁]) hk rfl
          (by rw [(core).hi₂₃])
          n₀ ((core).deg (p, q)) n₂ rfl hn₀ hn₂ ≪≫
        Y.EIsoH
          (homOfLE ((core).le₁₂' (p, q) hk rfl))
          n₀ ((core).deg (p, q)) n₂ hn₀ hn₂) :=
  χ.firstPageCoreIsoAtOfCut_eq p q k hk n₀ n₂ hn₀ hn₂

example (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.firstPageCoreIsoAt p q =
      χ.firstPageCoreIsoAtOfCut p q
        ((core).i₁ (p, q)) rfl
        ((core).deg (p, q) - 1)
        ((core).deg (p, q) + 1)
        (by omega) rfl :=
  rfl

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
example (χ : PartialTotalFirstPageChoice B) (m q : ℕ) : True := by
  let Y := B.partialTotalSpectralObject
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  have hnn' : n + 1 = n' := by
    dsimp only [n, n',
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    omega
  have hmid : (core).i₂ (m, q) = (core).i₁ (m + 1, q) := by
    change ((m : ℤ) : EInt) =
      ((((m + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
    congr 1
    omega
  have hPrev : (n - 1) + 1 = n := by omega
  let fRight := homOfLE ((core).le₁₂' (m + 1, q) hmid rfl)
  let ePageSourceCore := χ.firstPageCoreIsoAtOfCut
    (m + 1) q ((core).i₂ (m, q)) hmid
    (n - 1) n' hPrev hnn'
  let ePageSourceCoreX :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      Y core 1 χ.pageOneBound (m + 1, q)
      ((core).i₂ (m, q)) ((core).i₂ (m, q))
      ((core).i₂ (m + 1, q)) ((core).i₂ (m + 1, q))
      (by rw [hmid, ← (core).hi₀₁]) hmid rfl
      (by rw [(core).hi₂₃])
      (n - 1) n n' rfl hPrev hnn'
  let ePageSourceCoreH := Y.EIsoH fRight (n - 1) n n' hPrev hnn'
  have hSourceFactors :
      ePageSourceCore.hom =
        ePageSourceCoreX.hom ≫ ePageSourceCoreH.hom := by
    have h := congrArg Iso.hom
      (χ.firstPageCoreIsoAtOfCut_eq
        (m + 1) q ((core).i₂ (m, q)) hmid
        (n - 1) n' hPrev hnn')
    change ePageSourceCore.hom =
      ePageSourceCoreX.hom ≫ ePageSourceCoreH.hom at h
    exact h
  exact True.intro

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
example (χ : PartialTotalFirstPageChoice B) (m q : ℕ) : True := by
  let Y := B.partialTotalSpectralObject
  let n : ℤ := (core).deg (m + 1, q)
  let n' : ℤ := (core).deg (m, q)
  have hnn' : n + 1 = n' := by
    dsimp only [n, n',
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat]
    omega
  have hNext : n' + 1 = n' + 1 := rfl
  let fLeft := homOfLE ((core).le₁₂ (m, q))
  let ePageTargetRaw := χ.firstPageCoreIsoAtOfCut
    m q ((core).i₁ (m, q)) rfl n (n' + 1) hnn' hNext
  let ePageTargetRawX :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      Y core 1 χ.pageOneBound (m, q)
      ((core).i₁ (m, q)) ((core).i₁ (m, q))
      ((core).i₂ (m, q)) ((core).i₂ (m, q))
      (by rw [← (core).hi₀₁]) rfl rfl
      (by rw [(core).hi₂₃])
      n n' (n' + 1) rfl hnn' hNext
  let ePageTargetRawH := Y.EIsoH fLeft n n' (n' + 1) hnn' hNext
  have hTargetFactors :
      ePageTargetRaw.inv =
        ePageTargetRawH.inv ≫ ePageTargetRawX.inv := by
    have h := congrArg Iso.inv
      (χ.firstPageCoreIsoAtOfCut_eq
        m q ((core).i₁ (m, q)) rfl
        n (n' + 1) hnn' hNext)
    change ePageTargetRaw.inv =
      ePageTargetRawH.inv ≫ ePageTargetRawX.inv at h
    exact h
  exact True.intro

example (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    χ.pageOne.X (0, q) ≅
      (B.partialTotalSpectralObject.H ((core).deg (0, q))).obj
        (ComposableArrows.mk₁ (homOfLE ((core).le₁₂ (0, q)))) :=
  χ.firstPageCoreIsoAt 0 q

#check PartialTotalFirstPageChoice.pageOneBound
#check PartialTotalFirstPageChoice.pageOneToTwo
#check PartialTotalFirstPageChoice.pageTwoBound
#check partialTotalFirstPageChoice
#check fun (χ : PartialTotalFirstPageChoice B) => χ.pageOne
#check fun (χ : PartialTotalFirstPageChoice B) => χ.pageTwo
#check fun (χ : PartialTotalFirstPageChoice B) => χ.rowRestriction 0
#check fun (χ : PartialTotalFirstPageChoice B) => χ.rowRestriction 1
#check PartialTotalFirstPageChoice.firstPageCoreIsoAtOfCut

#check PartialTotalFirstPageChoice.firstPageCoreIsoAtOfCut_eq

#check fun (χ : PartialTotalFirstPageChoice B) (p q : ℕ) =>
  χ.firstPageCoreIsoAt p q
#check fun (χ : PartialTotalFirstPageChoice B) =>
  χ.firstPageRowIsoAt 0 0 0 rfl
#check fun (χ : PartialTotalFirstPageChoice B) =>
  χ.firstPageRowIsoAt 1 0 1 rfl
#check fun (χ : PartialTotalFirstPageChoice B) (p q : ℕ) =>
  χ.restrictionIndex p q
#check fun (χ : PartialTotalFirstPageChoice B) (p q : ℕ) =>
  χ.restrictionXIso (χ.restrictionIndex p q)
#check fun (χ : PartialTotalFirstPageChoice B) (p q : ℕ) =>
  χ.restrictionCyclesIso (χ.restrictionIndex p q)
#check fun (χ : PartialTotalFirstPageChoice B) (p q : ℕ) =>
  χ.restrictionHomologyIso (χ.restrictionIndex p q)
#check fun (χ : PartialTotalFirstPageChoice B) (p q : ℕ) =>
  χ.componentIso q p
#check PartialTotalFirstPageChoice.restrictionCyclesIso_hom_iCycles
#check PartialTotalFirstPageChoice.homologyπ_restrictionHomologyIso_hom
example (χ : PartialTotalFirstPageChoice B)
    (p q n : ℕ) (h : p + q = n) :
    χ.firstPageRowIsoAt p q n h =
      χ.firstPageCoreIsoAt p q ≪≫
        B.partialTotalSpectralObjectHStepIso p q ≪≫
        B.partialTotalStepE₁HomologyIsoAt p q n h :=
  rfl

/- Final chosen-page and representative clients. -/
example (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageTwo.X (p, q) ≅
      (B.verticalHomologyComplex q).homology p :=
  χ.secondPageVerticalHomologyIso p q

example (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.secondPageVerticalHomologyIso p q =
      (χ.pageOneTwoIso p q).symm ≪≫
        (χ.restrictionHomologyIso (χ.restrictionIndex p q)).symm ≪≫
        HomologicalComplex.homologyMapIso (χ.verticalHomologyIso q) p := by
  rfl

example (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    (B.verticalHomologyComplex q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀
          (B.verticalHomologyComplex q)).inv ≫
        (χ.secondPageVerticalHomologyIso 0 q).inv =
      (χ.componentIso q 0).inv ≫
        (χ.rowRestriction q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀
          (χ.rowRestriction q)).inv ≫
        (χ.restrictionHomologyIso
          (χ.restrictionIndex 0 q)).hom ≫
        (χ.pageOneTwoIso 0 q).hom :=
  χ.secondPageVerticalHomologyIso_inv_representation_zero q

example (p q : ℕ) :
    (B.partialTotalFirstPageChoice).pageTwo.X (p, q) ≅
      (B.verticalHomologyComplex q).homology p :=
  (B.partialTotalFirstPageChoice).secondPageVerticalHomologyIso p q

example :
    (B.verticalHomologyComplex 0).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀
          (B.verticalHomologyComplex 0)).inv ≫
        ((B.partialTotalFirstPageChoice).secondPageVerticalHomologyIso
          0 0).inv =
      ((B.partialTotalFirstPageChoice).componentIso 0 0).inv ≫
        ((B.partialTotalFirstPageChoice).rowRestriction 0).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀
          ((B.partialTotalFirstPageChoice).rowRestriction 0)).inv ≫
        ((B.partialTotalFirstPageChoice).restrictionHomologyIso
          ((B.partialTotalFirstPageChoice).restrictionIndex 0 0)).hom ≫
        ((B.partialTotalFirstPageChoice).pageOneTwoIso 0 0).hom :=
  (B.partialTotalFirstPageChoice).secondPageVerticalHomologyIso_inv_representation_zero 0

example :
    (B.verticalHomologyComplex 1).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀
          (B.verticalHomologyComplex 1)).inv ≫
        ((B.partialTotalFirstPageChoice).secondPageVerticalHomologyIso
          0 1).inv =
      ((B.partialTotalFirstPageChoice).componentIso 1 0).inv ≫
        ((B.partialTotalFirstPageChoice).rowRestriction 1).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀
          ((B.partialTotalFirstPageChoice).rowRestriction 1)).inv ≫
        ((B.partialTotalFirstPageChoice).restrictionHomologyIso
          ((B.partialTotalFirstPageChoice).restrictionIndex 0 1)).hom ≫
        ((B.partialTotalFirstPageChoice).pageOneTwoIso 0 1).hom :=
  (B.partialTotalFirstPageChoice).secondPageVerticalHomologyIso_inv_representation_zero 1

/- Vertical-homology packet. -/

example (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    χ.rowRestriction q ≅ B.verticalHomologyComplex q :=
  χ.verticalHomologyIso q

example (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    (χ.verticalHomologyIso q).inv.f 0 =
      (χ.componentIso q 0).inv :=
  χ.verticalHomologyIso_inv_f_zero q

example :
    (B.partialTotalFirstPageChoice).rowRestriction 0 ≅
      B.verticalHomologyComplex 0 :=
  (B.partialTotalFirstPageChoice).verticalHomologyIso 0

example :
    ((B.partialTotalFirstPageChoice).verticalHomologyIso 1).inv.f 0 =
      ((B.partialTotalFirstPageChoice).componentIso 1 0).inv :=
  (B.partialTotalFirstPageChoice).verticalHomologyIso_inv_f_zero 1

/- HomologyData packet. -/

example (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.PageTransitionIndex p q :=
  χ.pageTransitionIndex p q

example (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    let η := χ.pageTransitionIndex p q
    (χ.pageOne.sc' η.pqPrev (p, q) η.pqNext).HomologyData :=
  χ.pageOneHomologyData p q

#check PartialTotalFirstPageChoice.PageTransitionIndex
#check PartialTotalFirstPageChoice.pageTransitionIndex
#check PartialTotalFirstPageChoice.pageOneHomologyData
#check PartialTotalFirstPageChoice.pageOneHomologyData_left_i
#check PartialTotalFirstPageChoice.pageOneHomologyData_left_i_assoc
#check PartialTotalFirstPageChoice.pageOneHomologyData_left_π
#check PartialTotalFirstPageChoice.pageOneHomologyData_left_π_assoc

/- Common page-two coordinate and P12. -/

example (χ : PartialTotalFirstPageChoice B) (p q : ℕ) : C :=
  χ.pageTwoCoordinate p q

example (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageTwo.X (p, q) ≅ χ.pageTwoCoordinate p q :=
  χ.pageTwoCoordinateIso p q

example (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    let η := χ.pageTransitionIndex p q
    B.partialTotalSpectralObject.E
        (homOfLE η.hi₀'₁) (homOfLE η.hi₁₂) (homOfLE η.hi₂₃')
        η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ≅
      χ.pageTwoCoordinate p q :=
  χ.pageTwoRawCoordinateIso p q

example (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    let η := χ.pageTransitionIndex 0 q
    B.partialTotalSpectralObject.E
        (homOfLE η.hi₀'₁) (homOfLE η.hi₁₂) (homOfLE η.hi₂₃')
        η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ≅
      χ.pageTwoCoordinate 0 q :=
  χ.pageTwoRawCoordinateIso 0 q

example (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageOne.homology (p, q) ≅ χ.pageTwoCoordinate p q :=
  χ.pageOneHomologyCoordinateIso p q

example (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageOne.homology (p, q) ≅ χ.pageTwo.X (p, q) :=
  χ.pageOneTwoIso p q

example (χ : PartialTotalFirstPageChoice B) (p q : ℕ) :
    χ.pageOneTwoIso p q =
      χ.pageOneHomologyCoordinateIso p q ≪≫
        (χ.pageTwoCoordinateIso p q).symm :=
  rfl

example (χ : PartialTotalFirstPageChoice B) (q : ℕ) :
    (χ.pageOneTwoIso 0 q).hom ≫
        (χ.pageTwoCoordinateIso 0 q).hom =
      (χ.pageOneHomologyCoordinateIso 0 q).hom :=
  χ.pageOneTwoIso_zero_hom_comp_pageTwoCoordinateIso_hom q

#check PartialTotalFirstPageChoice.pageOneTwoIso_zero_hom_comp_pageTwoCoordinateIso_hom_assoc

/- The canonical zero bicomplex. -/

example (p q : ℕ) :=
  (HomologicalComplex₂.partialTotalFirstPageChoice
    (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))).pageTransitionIndex p q

example (p q : ℕ) :=
  (HomologicalComplex₂.partialTotalFirstPageChoice
    (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))).pageOneHomologyData p q

example (p q : ℕ) :=
  (HomologicalComplex₂.partialTotalFirstPageChoice
    (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))).pageOneTwoIso p q

example (p q : ℕ) :=
  (HomologicalComplex₂.partialTotalFirstPageChoice
    (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))).secondPageVerticalHomologyIso p q

example (q : ℕ) :=
  (HomologicalComplex₂.partialTotalFirstPageChoice
    (HomologicalComplex.zero : HomologicalComplex₂ C
      (ComplexShape.down ℕ) (ComplexShape.down ℕ))).secondPageVerticalHomologyIso_inv_representation_zero
    q

end HomologicalComplex₂

end
