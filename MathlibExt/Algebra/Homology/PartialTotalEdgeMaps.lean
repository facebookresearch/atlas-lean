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

public import MathlibExt.Algebra.Homology.PartialTotalStablePage
public import MathlibExt.Algebra.Homology.PartialTotalStageZeroRowCoordinate
public import MathlibExt.Algebra.Homology.PartialTotalCoordinates

/-!
# Boundary edge maps for the partial-total spectral sequence

The two boundary edges of a first-quadrant partial-total spectral sequence
are constructed directly from page two, the stable interval, and the literal
image filtration on total homology.  No page at infinity or filtration
splitting is introduced.
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

/-- The shared stable-side source of the page-two zero-column comparison. -/
noncomputable abbrev partialTotalZeroColumnStableSource (q : ℕ) : C :=
  let χ := B.partialTotalFirstPageChoice
  let η := χ.pageTransitionIndex 0 q
  B.partialTotalSpectralObject.E
    (homOfLE η.hiBot₁) (homOfLE η.hi₁₂)
    (homOfLE η.hi₂₃') η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂

/-- The stable-side source is canonically isomorphic to the package-owned
page-two coordinate. -/
noncomputable def partialTotalZeroColumnPageTwoLeftIso (q : ℕ) :
    B.partialTotalZeroColumnStableSource q ≅
      B.partialTotalFirstPageChoice.pageTwoCoordinate 0 q := by
  let χ := B.partialTotalFirstPageChoice
  let η := χ.pageTransitionIndex 0 q
  let Y := B.partialTotalSpectralObject
  have hi₀' : η.i₀' = ((-2 : ℤ) : EInt) := by
    dsimp only [η, PartialTotalFirstPageChoice.pageTransitionIndex]
    congr 1
  have hLeftAt (x : EInt) (hx : x = ((-2 : ℤ) : EInt))
      (hbx : (⊥ : EInt) ≤ x) :
      IsZero ((Y.H η.n₂).obj (mk₁ (homOfLE hbx))) := by
    subst x
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      η.n₂ (-2) (by omega)
  have hLeft : IsZero ((Y.H η.n₂).obj
      (mk₁ (homOfLE η.hiBot₀'))) :=
    hLeftAt η.i₀' hi₀' η.hiBot₀'
  let eLeftRaw := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) η.i₀' η.i₁ η.i₂ η.i₃'
    η.hiBot₀' η.hi₀'₁ η.hi₁₂ η.hi₂₃'
    η.n₀ η.n₁ η.n₂ hLeft η.hn₁ η.hn₂
  exact eLeftRaw ≪≫ χ.pageTwoRawCoordinateIso 0 q

/-- The eta-owned terminal right `E` object is the direct zero-column stable
target. -/
noncomputable def partialTotalZeroColumnStableTargetIso (q : ℕ) :
    let χ := B.partialTotalFirstPageChoice
    let η := χ.pageTransitionIndex 0 q
    let Y := B.partialTotalSpectralObject
    Y.E (homOfLE η.hiBot₁) (homOfLE η.hi₁₂)
        (homOfLE (η.hi₂₃'.trans η.hi₃'Top))
        η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ≅
      B.partialTotalStableObj q 0 := by
  let χ := B.partialTotalFirstPageChoice
  let η := χ.pageTransitionIndex 0 q
  let Y := B.partialTotalSpectralObject
  have hTarget :
      Y.E (homOfLE η.hiBot₁) (homOfLE η.hi₁₂)
          (homOfLE (η.hi₂₃'.trans η.hi₃'Top))
          η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ =
        B.partialTotalStableObj q 0 := by
    dsimp only [η, PartialTotalFirstPageChoice.pageTransitionIndex,
      partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      partialTotalHomologyPreviousIndex]
    congr 1 <;> omega
  exact eqToIso hTarget

/-- The exact stable tail after the package-owned page-two left coordinate. -/
noncomputable def partialTotalZeroColumnStableTail (q : ℕ) :
    B.partialTotalZeroColumnStableSource q ⟶
      B.partialTotalStableObj q 0 := by
  let χ := B.partialTotalFirstPageChoice
  let η := χ.pageTransitionIndex 0 q
  let Y := B.partialTotalSpectralObject
  exact Y.mapFourδ₄Toδ₃'
      (⊥ : EInt) η.i₁ η.i₂ η.i₃' (⊤ : EInt)
      η.hiBot₁ η.hi₁₂ η.hi₂₃' η.hi₃'Top
      η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ≫
    (B.partialTotalZeroColumnStableTargetIso q).hom

/-- The package-chosen page-two zero column maps canonically to its stable
interval through the one named left coordinate and stable tail. -/
noncomputable def partialTotalZeroColumnPageToStable (q : ℕ) :
    B.partialTotalFirstPageChoice.pageTwo.X (0, q) ⟶
      B.partialTotalStableObj q 0 :=
  (B.partialTotalFirstPageChoice.pageTwoCoordinateIso 0 q).hom ≫
    (B.partialTotalZeroColumnPageTwoLeftIso q).inv ≫
    B.partialTotalZeroColumnStableTail q

/-- The page-to-stable map is the page-two coordinate followed by the
stable-side comparison and stable tail. -/
@[reassoc]
theorem partialTotalZeroColumnPageToStable_eq_pageTwoCoordinate (q : ℕ) :
    B.partialTotalZeroColumnPageToStable q =
      (B.partialTotalFirstPageChoice.pageTwoCoordinateIso 0 q).hom ≫
        (B.partialTotalZeroColumnPageTwoLeftIso q).inv ≫
        B.partialTotalZeroColumnStableTail q := by
  rfl

/-- The package-chosen page-two zero-column edge maps into total homology
through the zero-stage image filtration. -/
noncomputable def partialTotalZeroColumnEdge (q : ℕ) :
    B.partialTotalFirstPageChoice.pageTwo.X (0, q) ⟶
      (B.total (ComplexShape.down ℕ)).homology q :=
  B.partialTotalZeroColumnPageToStable q ≫
    (B.partialTotalStableGradedIso q 0).hom ≫
    (B.partialTotalHomologyGradedZeroIso q).inv ≫
    (B.partialTotalHomologyFiltration q).ι.app ((0 : ℤ) : EInt)

/-- The stable interval on the top row maps canonically to page two. -/
noncomputable def partialTotalTopRowStableToPage (p : ℕ) :
    B.partialTotalStableObj p p ⟶
      ((B.partialTotalSpectralObject.spectralSequence core).page (2 : ℤ)).X
        (p, 0) := by
  let Y := B.partialTotalSpectralObject
  let r : ℤ := 2
  let i₀ : EInt := (((p : ℕ) : ℤ) - 2 : ℤ)
  let i₁ : EInt := partialTotalHomologyPreviousIndex p
  let i₂ : EInt := ((p : ℕ) : ℤ)
  let i₃ : EInt := (((p + 1 : ℕ) : ℤ) : EInt)
  let n₀ : ℤ := -((p + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -(p : ℤ)
  let n₂ : ℤ := -(p : ℤ) + 1
  have hr : (1 : ℤ) ≤ r := by omega
  have h₀ : i₀ = (core).i₀ r (p, 0) := by
    change i₀ = (((p : ℤ) - r : ℤ) : EInt)
    dsimp only [i₀, r]
  have h₁ : i₁ = (core).i₁ (p, 0) := by
    change i₁ = (((p : ℤ) - 1 : ℤ) : EInt)
    dsimp only [i₁]
    rcases p with _ | p
    · rfl
    · change ((p : ℤ) : EInt) =
        ((((p + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
      congr 1
      omega
  have h₂ : i₂ = (core).i₂ (p, 0) := rfl
  have h₃ : i₃ = (core).i₃ r (p, 0) hr := by
    change i₃ = (((p : ℤ) + r - 1 : ℤ) : EInt)
    dsimp only [i₃, r]
    congr 1
    omega
  have hn : n₁ = (core).deg (p, 0) := by
    change n₁ = -(p : ℤ) - (0 : ℤ)
    dsimp only [n₁]
    omega
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  have hi₀₁ : i₀ ≤ i₁ := by
    dsimp only [i₀, i₁, partialTotalHomologyPreviousIndex]
    rcases p with _ | p <;> simp only [WithBotTop.coe_le_coe] <;> omega
  have hi₁₂ : i₁ ≤ i₂ := partialTotalHomologyPreviousIndex_le p
  have hi₂₃ : i₂ ≤ i₃ := by
    dsimp only [i₂, i₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hiBot₀ : (⊥ : EInt) ≤ i₀ := by simp
  have hi₃Top : i₃ ≤ (⊤ : EInt) := by simp
  have hRight : IsZero ((Y.H n₀).obj
      (mk₁ (homOfLE (show i₃ ≤ (⊤ : EInt) by simp)))) := by
    exact B.isZero_partialTotalSpectralObjectHObj_stage_to_top
      (p + 1) p (by omega)
  let leftOuterMap := Y.mapFourδ₁Toδ₀'
    (⊥ : EInt) i₀ i₁ i₂ ⊤ hiBot₀ hi₀₁ hi₁₂ (by simp)
      n₀ n₁ n₂ hn₁ hn₂
  let eRight := Y.isoMapFourδ₄Toδ₃'
    i₀ i₁ i₂ i₃ ⊤ hi₀₁ hi₁₂ hi₂₃ hi₃Top
      n₀ n₁ n₂ hRight (hn₁ := hn₁) (hn₂ := hn₂)
  let ePage := Y.spectralSequencePageXIso core r hr (p, 0)
    i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ hn
      (hn₁ := hn₁) (hn₂ := hn₂)
  have hSource :
      Y.E (homOfLE (show (⊥ : EInt) ≤ i₁ by simp)) (homOfLE hi₁₂)
          (homOfLE (show i₂ ≤ (⊤ : EInt) by simp)) n₀ n₁ n₂ hn₁ hn₂ =
        B.partialTotalStableObj p p := by
    dsimp only [partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      n₀, n₁, n₂]
    congr 1
    all_goals omega
  exact (eqToIso hSource).inv ≫ leftOuterMap ≫ eRight.inv ≫ ePage.inv

/-- Total homology maps to the page-two top row through the exhaustive top
filtration stage. -/
noncomputable def partialTotalTopRowEdge (p : ℕ) :
    (B.total (ComplexShape.down ℕ)).homology p ⟶
      ((B.partialTotalSpectralObject.spectralSequence core).page (2 : ℤ)).X
        (p, 0) := by
  let f := (B.partialTotalHomologyFiltration p).ι.app
    (((p : ℕ) : ℤ) : EInt)
  let _ : IsIso f := B.partialTotalHomologyFiltration_exhaustive_at_degree p
  exact inv f ≫ B.partialTotalHomologyFiltrationToStable p p ≫
    B.partialTotalTopRowStableToPage p

private theorem isIso_canonicalRightIncrement_of_isZeroIncoming
    (n r s : ℕ) (hr : 2 ≤ r) (hrs : r + s = n + 1)
    (hzero : IsZero
      ((((B.partialTotalSpectralObject.spectralSequence
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).page
        (r : ℤ) (by omega)).X (r, s)))) :
    let i₀ : EInt := ((-(r : ℤ) : ℤ) : EInt)
    let i₁ : EInt := ((-1 : ℤ) : EInt)
    let i₂ : EInt := ((0 : ℤ) : EInt)
    let i₃ : EInt := (((r : ℤ) - 1 : ℤ) : EInt)
    let i₃' : EInt := ((r : ℤ) : EInt)
    IsIso (B.partialTotalSpectralObject.mapFourδ₄Toδ₃'
      i₀ i₁ i₂ i₃ i₃'
      (by
        dsimp only [i₀, i₁]
        simp only [WithBotTop.coe_le_coe]
        omega)
      (by
        dsimp only [i₁, i₂]
        simp only [WithBotTop.coe_le_coe]
        omega)
      (by
        dsimp only [i₂, i₃]
        simp only [WithBotTop.coe_le_coe]
        omega)
      (by
        dsimp only [i₃, i₃']
        simp only [WithBotTop.coe_le_coe]
        omega)
      (-(0 : ℤ) - (n : ℤ) - 1) (-(0 : ℤ) - (n : ℤ))
      (-(0 : ℤ) - (n : ℤ) + 1)
      (by omega) (by omega)) := by
  dsimp only
  let rZ : ℤ := r
  let rZ' : ℤ := r + 1
  let pq : ℕ × ℕ := (r, s)
  let pq' : ℕ × ℕ := (0, n)
  let i₀ : EInt := ((-(r : ℤ) : ℤ) : EInt)
  let i₁ : EInt := ((-1 : ℤ) : EInt)
  let i₂ : EInt := ((0 : ℤ) : EInt)
  let i₃ : EInt := (((r : ℤ) - 1 : ℤ) : EInt)
  let i₃' : EInt := ((r : ℤ) : EInt)
  let n₀ : ℤ := -(0 : ℤ) - (n : ℤ) - 1
  let n₁ : ℤ := -(0 : ℤ) - (n : ℤ)
  let n₂ : ℤ := -(0 : ℤ) - (n : ℤ) + 1
  have hrr' : rZ + 1 = rZ' := by
    dsimp only [rZ, rZ']
  have hrZ : (1 : ℤ) ≤ rZ := by
    dsimp only [rZ]
    omega
  have hpqRel : (ComplexShape.spectralSequenceNat
      (-(rZ), rZ - 1)).Rel pq pq' := by
    constructor
    · dsimp only [pq, pq', rZ]
      omega
    · dsimp only [pq, pq', rZ]
      omega
  have hpq : (ComplexShape.spectralSequenceNat
      (-(rZ), rZ - 1)).prev pq' = pq :=
    (ComplexShape.spectralSequenceNat (-(rZ), rZ - 1)).prev_eq' hpqRel
  have hi₀ : i₀ =
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₀
        rZ pq' hrZ := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
    dsimp only [i₀, rZ, pq']
    congr 1
    omega
  have hi₁ : i₁ =
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₁
        pq' := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₁]
    dsimp only [i₁, pq']
    congr 1
  have hi₂ : i₂ =
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₂
        pq' := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₂]
    dsimp only [i₂, pq']
    congr 1
  have hi₃ : i₃ =
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₃
        rZ pq' hrZ := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
    dsimp only [i₃, rZ, pq']
    congr 1
    omega
  have hi₃' : i₃' =
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₃
        rZ' pq' (by omega) := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
    dsimp only [i₃', rZ', pq']
    congr 1
    omega
  have hn : n₁ =
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.deg
        pq' := by
    change n₁ = (core).deg (0, n)
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
    rfl
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  let S := CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.ccSc
    B.partialTotalSpectralObject
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
      rZ rZ' hrr' hrZ pq pq'
      i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃'
      n₀ n₁ n₂ hn hn₁ hn₂
  have hzeroAttached : IsZero
      ((((B.partialTotalSpectralObject.spectralSequence
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat).page
        rZ hrZ).X pq)) := by
    simpa only [rZ, pq] using hzero
  let eAttachedIncoming :=
    B.partialTotalSpectralObject.spectralSequencePageXIso
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
      rZ hrZ pq
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₀
        rZ pq hrZ)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₁
        pq)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₂
        pq)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₃
        rZ pq hrZ)
      rfl rfl rfl rfl
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.deg
        pq - 1)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.deg
        pq)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.deg
        pq + 1)
      rfl (hn₁ := by omega) (hn₂ := by omega)
  let eInternalIncoming :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      B.partialTotalSpectralObject
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
      rZ hrZ pq
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₀
        rZ pq hrZ)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₁
        pq)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₂
        pq)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.i₃
        rZ pq hrZ)
      rfl rfl rfl rfl
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.deg
        pq - 1)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.deg
        pq)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.deg
        pq + 1)
      rfl (hn₁ := by omega) (hn₂ := by omega)
  let eIncoming := eInternalIncoming ≪≫ eAttachedIncoming.symm
  have hzeroInternal : IsZero
      (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageX
        B.partialTotalSpectralObject
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
        rZ pq hrZ) :=
    IsZero.of_iso hzeroAttached eIncoming
  have hzeroS : IsZero S.X₁ := by
    change IsZero
      (CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageX
        B.partialTotalSpectralObject
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
        rZ pq hrZ)
    exact hzeroInternal
  have hExact : S.Exact := by
    exact CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.ccSc_exact
      B.partialTotalSpectralObject
        CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
        rZ rZ' hrr' hrZ pq pq' hpq
        i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃'
        n₀ n₁ n₂ hn hn₁ hn₂
  let _ : Mono S.f := hzeroS.isInitial.mono_from S.f
  have hShort : S.ShortExact :=
    ShortComplex.ShortExact.mk' hExact (inferInstance : Mono S.f)
      (inferInstance : Epi S.g)
  let hIsoSg : IsIso S.g := (hShort.isIso_g_iff).2 hzeroS
  let eOutgoing :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      B.partialTotalSpectralObject
      CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
      rZ hrZ pq' i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃
      n₀ n₁ n₂ hn (hn₁ := hn₁) (hn₂ := hn₂)
  let rightIncrement :=
    B.partialTotalSpectralObject.mapFourδ₄Toδ₃'
      i₀ i₁ i₂ i₃ i₃'
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.le₀₁'
        rZ hrZ pq' hi₀ hi₁)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.le₁₂'
        pq' hi₁ hi₂)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.le₂₃'
        rZ hrZ pq' hi₂ hi₃)
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat.le₃₃'
        hrr' hrZ pq' hi₃ hi₃')
      n₀ n₁ n₂ hn₁ hn₂
  rw [CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.ccSc_g
    B.partialTotalSpectralObject
    CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat
    rZ rZ' hrr' hrZ pq pq'
    i₀ i₁ i₂ i₃ i₃' hi₀ hi₁ hi₂ hi₃ hi₃'
    n₀ n₁ n₂ hn hn₁ hn₂] at hIsoSg
  change IsIso (eOutgoing.hom ≫ rightIncrement) at hIsoSg
  let _ : IsIso (eOutgoing.hom ≫ rightIncrement) := hIsoSg
  change IsIso rightIncrement
  exact IsIso.of_isIso_comp_left eOutgoing.hom rightIncrement

private theorem isIso_bottomRightIncrement_of_isZeroIncoming
    (n r s : ℕ) (hr : 2 ≤ r) (hrs : r + s = n + 1)
    (hzero : IsZero
      ((((B.partialTotalSpectralObject.spectralSequence core).page
        (r : ℤ) (by omega)).X (r, s)))) :
    let i₁ : EInt := ((-1 : ℤ) : EInt)
    let i₂ : EInt := ((0 : ℤ) : EInt)
    let i₃ : EInt := (((r : ℤ) - 1 : ℤ) : EInt)
    let i₃' : EInt := ((r : ℤ) : EInt)
    IsIso (B.partialTotalSpectralObject.mapFourδ₄Toδ₃'
      (⊥ : EInt) i₁ i₂ i₃ i₃'
      (by simp)
      (by dsimp only [i₁, i₂]; simp)
      (by dsimp only [i₂, i₃]; simp only [WithBotTop.coe_le_coe]; omega)
      (by dsimp only [i₃, i₃']; simp only [WithBotTop.coe_le_coe]; omega)
      (-(0 : ℤ) - (n : ℤ) - 1) (-(0 : ℤ) - (n : ℤ))
      (-(0 : ℤ) - (n : ℤ) + 1)
      (by omega) (by omega)) := by
  dsimp only
  let Y := B.partialTotalSpectralObject
  let i₀ : EInt := ((-(r : ℤ) : ℤ) : EInt)
  let i₁ : EInt := ((-1 : ℤ) : EInt)
  let i₂ : EInt := ((0 : ℤ) : EInt)
  let i₃ : EInt := (((r : ℤ) - 1 : ℤ) : EInt)
  let i₃' : EInt := ((r : ℤ) : EInt)
  let n₀ : ℤ := -(0 : ℤ) - (n : ℤ) - 1
  let n₁ : ℤ := -(0 : ℤ) - (n : ℤ)
  let n₂ : ℤ := -(0 : ℤ) - (n : ℤ) + 1
  have hiBot₀ : (⊥ : EInt) ≤ i₀ := by simp
  have hi₀₁ : i₀ ≤ i₁ := by
    dsimp only [i₀, i₁]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₁₂ : i₁ ≤ i₂ := by
    dsimp only [i₁, i₂]
    simp
  have hi₂₃ : i₂ ≤ i₃ := by
    dsimp only [i₂, i₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₃₃' : i₃ ≤ i₃' := by
    dsimp only [i₃, i₃']
    simp only [WithBotTop.coe_le_coe]
    omega
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  have hLeft : IsZero ((Y.H n₂).obj
      (mk₁ (homOfLE hiBot₀))) := by
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      n₂ (-(r : ℤ)) (by omega)
  let Lold := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) i₀ i₁ i₂ i₃ hiBot₀ hi₀₁ hi₁₂ hi₂₃
      n₀ n₁ n₂ hLeft (hn₁ := hn₁) (hn₂ := hn₂)
  let Lnew := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) i₀ i₁ i₂ i₃' hiBot₀ hi₀₁ hi₁₂
      (hi₂₃.trans hi₃₃') n₀ n₁ n₂ hLeft
      (hn₁ := hn₁) (hn₂ := hn₂)
  let Cinc := Y.mapFourδ₄Toδ₃'
    i₀ i₁ i₂ i₃ i₃' hi₀₁ hi₁₂ hi₂₃ hi₃₃'
      n₀ n₁ n₂ hn₁ hn₂
  let Binc := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) i₁ i₂ i₃ i₃' (by simp) hi₁₂ hi₂₃ hi₃₃'
      n₀ n₁ n₂ hn₁ hn₂
  let _ : IsIso Cinc :=
    B.isIso_canonicalRightIncrement_of_isZeroIncoming n r s hr hrs hzero
  have hSquare : Lold.hom ≫ Cinc = Binc ≫ Lnew.hom := by
    exact Y.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'
      (⊥ : EInt) i₀ i₁ i₂ i₃ i₃'
      hiBot₀ hi₀₁ hi₁₂ hi₂₃ hi₃₃'
      n₀ n₁ n₂ hn₁ hn₂
  have hComposite : IsIso (Binc ≫ Lnew.hom) := by
    rw [← hSquare]
    infer_instance
  let _ : IsIso (Binc ≫ Lnew.hom) := hComposite
  change IsIso Binc
  exact IsIso.of_isIso_comp_right Binc Lnew.hom

theorem isIso_partialTotalZeroColumnPageToStable_of_isZero_incoming
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (n : ℕ)
    (hIncoming : ∀ (r s : ℕ) (hr : 2 ≤ r), r + s = n + 1 →
      IsZero
        ((((B.partialTotalSpectralObject.spectralSequence core).page
          (r : ℤ) (by omega)).X (r, s)))) :
    IsIso (B.partialTotalZeroColumnPageToStable n) := by
  rcases n with _ | m
  · let χ := B.partialTotalFirstPageChoice
    let η := χ.pageTransitionIndex 0 0
    let Y := B.partialTotalSpectralObject
    have hTerminalZero : IsZero ((Y.H η.n₀).obj
        (mk₁ (homOfLE η.hi₃'Top))) := by
      dsimp only [η, PartialTotalFirstPageChoice.pageTransitionIndex]
      exact B.isZero_partialTotalSpectralObjectHObj_stage_to_top 1 0 le_rfl
    let rightOuter := Y.mapFourδ₄Toδ₃'
      (⊥ : EInt) η.i₁ η.i₂ η.i₃' ⊤
      η.hiBot₁ η.hi₁₂ η.hi₂₃' η.hi₃'Top
      η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
    let _ : IsIso rightOuter := Y.isIso_mapFourδ₄Toδ₃'
      (⊥ : EInt) η.i₁ η.i₂ η.i₃' ⊤
      η.hiBot₁ η.hi₁₂ η.hi₂₃' η.hi₃'Top
      η.n₀ η.n₁ η.n₂ hTerminalZero η.hn₁ η.hn₂
    unfold partialTotalZeroColumnPageToStable
      partialTotalZeroColumnStableTail
    dsimp only
    infer_instance
  · let χ := B.partialTotalFirstPageChoice
    let η := χ.pageTransitionIndex 0 (Nat.succ m)
    let Y := B.partialTotalSpectralObject
    let i₁ : EInt := η.i₁
    let i₂ : EInt := η.i₂
    let iBase : EInt := η.i₃'
    let n₀ : ℤ := η.n₀
    let n₁ : ℤ := η.n₁
    let n₂ : ℤ := η.n₂
    have hiBot₁ : (⊥ : EInt) ≤ i₁ := η.hiBot₁
    have hi₁₂ : i₁ ≤ i₂ := η.hi₁₂
    have hi₂Base : i₂ ≤ iBase := η.hi₂₃'
    have hn₁ : n₀ + 1 = n₁ := η.hn₁
    have hn₂ : n₁ + 1 = n₂ := η.hn₂
    have hOneK (k : ℕ) (hk : 1 ≤ k) :
        iBase ≤ (((k : ℕ) : ℤ) : EInt) := by
      dsimp only [iBase, η, PartialTotalFirstPageChoice.pageTransitionIndex]
      simp only [WithBotTop.coe_le_coe]
      omega
    let R (k : ℕ) (hk : 1 ≤ k) :=
      Y.mapFourδ₄Toδ₃'
        (⊥ : EInt) i₁ i₂ iBase ((k : ℤ) : EInt)
        hiBot₁ hi₁₂ hi₂Base
        (hOneK k hk)
        n₀ n₁ n₂ hn₁ hn₂
    have hFinite : ∀ (d : ℕ) (hd : d + 2 ≤ m + 2),
        IsIso (R (d + 2) (by omega)) := by
      intro d
      induction d with
      | zero =>
          intro _
          have hz := hIncoming 2 m (by omega) (by omega)
          dsimp only [R, i₁, i₂, iBase, n₀, n₁, n₂, η,
            PartialTotalFirstPageChoice.pageTransitionIndex]
          exact B.isIso_bottomRightIncrement_of_isZeroIncoming
            (Nat.succ m) 2 m (by omega) (by omega) hz
      | succ d ih =>
          intro hd
          have hPrev : d + 2 ≤ m + 2 := by omega
          have hkPrev : 1 ≤ d + 2 := by omega
          have hkNext : 1 ≤ d + 3 := by omega
          let prevMap := R (d + 2) hkPrev
          let _ : IsIso prevMap := by
            dsimp only [prevMap]
            exact ih hPrev
          let r : ℕ := d + 3
          have hrLe : r ≤ Nat.succ m + 1 := by
            dsimp only [r]
            omega
          obtain ⟨s, hrsRev⟩ := Nat.exists_eq_add_of_le hrLe
          have hrs : r + s = Nat.succ m + 1 := hrsRev.symm
          have hrTwo : 2 ≤ r := by
            dsimp only [r]
            omega
          have hz := hIncoming r s hrTwo hrs
          let iLower : EInt := (((r : ℤ) - 1 : ℤ) : EInt)
          let iNorm : EInt := (((d + 2 : ℕ) : ℤ) : EInt)
          let iNext : EInt := (((d + 3 : ℕ) : ℤ) : EInt)
          have hCut : iLower = iNorm := by
            dsimp only [iLower, iNorm, r]
            congr 1
            omega
          let I := {x : EInt // x = iNorm}
          let sl : I := ⟨iLower, hCut⟩
          let sn : I := ⟨iNorm, rfl⟩
          have hln : sl = sn := by
            apply Subtype.ext
            exact hCut
          have hi₂x (x : I) : i₂ ≤ x.1 := by
            rw [x.2]
            dsimp only [i₂, iNorm, η,
              PartialTotalFirstPageChoice.pageTransitionIndex]
            simp only [WithBotTop.coe_le_coe]
            omega
          have hxNext (x : I) : x.1 ≤ iNext := by
            rw [x.2]
            dsimp only [iNorm, iNext]
            simp only [WithBotTop.coe_le_coe]
            omega
          have hi₂Next : i₂ ≤ iNext := by
            dsimp only [i₂, iNext, η,
              PartialTotalFirstPageChoice.pageTransitionIndex]
            simp only [WithBotTop.coe_le_coe]
            omega
          let X₂ (x : I) := Y.E
            (homOfLE hiBot₁) (homOfLE hi₁₂) (homOfLE (hi₂x x))
            n₀ n₁ n₂ hn₁ hn₂
          let XNext := Y.E
            (homOfLE hiBot₁) (homOfLE hi₁₂) (homOfLE hi₂Next)
            n₀ n₁ n₂ hn₁ hn₂
          let stepF (x : I) : X₂ x ⟶ XNext :=
            Y.mapFourδ₄Toδ₃'
              (⊥ : EInt) i₁ i₂ x.1 iNext
              hiBot₁ hi₁₂ (hi₂x x) (hxNext x)
              n₀ n₁ n₂ hn₁ hn₂
          let _ : IsIso (stepF sl) := by
            dsimp only [stepF, sl, X₂, XNext, iLower, iNext]
            exact B.isIso_bottomRightIncrement_of_isZeroIncoming
              (Nat.succ m) r s hrTwo hrs hz
          have hStepNaturality :
              stepF sl =
                eqToHom (congrArg X₂ hln) ≫ stepF sn := by
            have h := CategoryTheory.eqToHom_naturality stepF hln
            simpa only [eqToHom_refl, Category.comp_id] using h
          let stepMap := stepF sn
          have hIsoTransported : IsIso
              (eqToHom (congrArg X₂ hln) ≫ stepMap) := by
            rw [← hStepNaturality]
            infer_instance
          let _ : IsIso
              (eqToHom (congrArg X₂ hln) ≫ stepMap) := hIsoTransported
          let _ : IsIso stepMap :=
            IsIso.of_isIso_comp_left
              (eqToHom (congrArg X₂ hln)) stepMap
          have hiBasePrev :
              iBase ≤ (((d + 2 : ℕ) : ℤ) : EInt) :=
            hOneK (d + 2) hkPrev
          have hiPrevNext :
              (((d + 2 : ℕ) : ℤ) : EInt) ≤
                (((d + 3 : ℕ) : ℤ) : EInt) := by
            simp only [WithBotTop.coe_le_coe]
            omega
          have hCompNamed :
              prevMap ≫ stepMap = R (d + 3) hkNext := by
            dsimp only [prevMap, stepMap, stepF, sn, X₂, XNext,
              iNorm, iNext, R]
            exact Y.mapFourδ₄Toδ₃'_comp
              (⊥ : EInt) i₁ i₂ iBase
              (((d + 2 : ℕ) : ℤ) : EInt)
              (((d + 3 : ℕ) : ℤ) : EInt)
              hiBot₁ hi₁₂ hi₂Base hiBasePrev hiPrevNext
              n₀ n₁ n₂ hn₁ hn₂
          change IsIso (R (d + 3) hkNext)
          rw [← hCompNamed]
          infer_instance
    let _ : IsIso (R (m + 2) (by omega)) := hFinite m (by omega)
    let iLast : EInt := (((m + 2 : ℕ) : ℤ) : EInt)
    have hiBaseLast : iBase ≤ iLast := hOneK (m + 2) (by omega)
    have hiLastTop : iLast ≤ (⊤ : EInt) := by simp
    have hi₂Last : i₂ ≤ iLast := by
      dsimp only [i₂, iLast, η,
        PartialTotalFirstPageChoice.pageTransitionIndex]
      simp only [WithBotTop.coe_le_coe]
      omega
    have hTerminalZero : IsZero ((Y.H n₀).obj
        (mk₁ (homOfLE hiLastTop))) := by
      exact B.isZero_partialTotalSpectralObjectHObj_stage_to_top
        (m + 2) (Nat.succ m) (by omega)
    let T := Y.mapFourδ₄Toδ₃'
      (⊥ : EInt) i₁ i₂ iLast ⊤ hiBot₁ hi₁₂
        hi₂Last hiLastTop n₀ n₁ n₂ hn₁ hn₂
    let _ : IsIso T := Y.isIso_mapFourδ₄Toδ₃'
      (⊥ : EInt) i₁ i₂ iLast ⊤ hiBot₁ hi₁₂
        hi₂Last hiLastTop n₀ n₁ n₂ hTerminalZero hn₁ hn₂
    let rightOuter := Y.mapFourδ₄Toδ₃'
      (⊥ : EInt) η.i₁ η.i₂ η.i₃' ⊤
      η.hiBot₁ η.hi₁₂ η.hi₂₃' η.hi₃'Top
      η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
    have hFinalComp : R (m + 2) (by omega) ≫ T = rightOuter := by
      exact Y.mapFourδ₄Toδ₃'_comp
        (⊥ : EInt) i₁ i₂ iBase iLast ⊤
        hiBot₁ hi₁₂ hi₂Base hiBaseLast hiLastTop
        n₀ n₁ n₂ hn₁ hn₂
    have hOuterIso : IsIso rightOuter := by
      rw [← hFinalComp]
      infer_instance
    let _ : IsIso rightOuter := hOuterIso
    unfold partialTotalZeroColumnPageToStable
      partialTotalZeroColumnStableTail
    dsimp only
    infer_instance


unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in
/-- The chosen page-two zero-column representative is homology of the
literal zeroth-row inclusion into the total complex. -/
theorem partialTotalZeroColumnEdge_representation (q : ℕ) :
    let χ := B.partialTotalFirstPageChoice
    (B.verticalHomologyComplex q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀ (B.verticalHomologyComplex q)).inv ≫
        (χ.secondPageVerticalHomologyIso 0 q).inv ≫
        B.partialTotalZeroColumnEdge q =
      HomologicalComplex.homologyMap B.partialTotalZeroRowToTotal q := by
  let χ := B.partialTotalFirstPageChoice
  let η := χ.pageTransitionIndex 0 q
  let ρ := χ.restrictionIndex 0 q
  let Y := B.partialTotalSpectralObject
  let K := χ.rowRestriction q
  let H0 := (B.X 0).homology q
  let V := B.verticalHomologyComplex q
  let P1 := χ.pageOne.X (0, q)
  let P2 := χ.pageTwo.X (0, q)
  let StableSource := B.partialTotalZeroColumnStableSource q
  let n : ℤ := -(q : ℤ)
  let i : EInt := (((0 : ℕ) : ℤ) : EInt)
  let S0 := Y.stableIntervalStep n i
  let Stable0 := B.partialTotalStableObj q 0
  let HStage := (B.partialTotal 0).homology q
  let HTotal := (B.total (ComplexShape.down ℕ)).homology q
  let s : B.X 0 ⟶ B.partialTotal 0 :=
    B.partialTotalZeroRowToPartialTotal
  let ιStage : B.partialTotal 0 ⟶ B.total (ComplexShape.down ℕ) :=
    B.partialTotalι 0
  let eX : K.X 0 ≅ P1 := χ.restrictionXIso ρ
  let eCycles : K.cycles 0 ≅ χ.pageOne.cycles (0, q) :=
    χ.restrictionCyclesIso ρ
  let eRestr : K.homology 0 ≅ χ.pageOne.homology (0, q) :=
    χ.restrictionHomologyIso ρ
  let eF : P1 ≅ (B.totalRow 0).homology q :=
    χ.firstPageRowIsoAt 0 q q (Nat.zero_add q)
  let eH : (B.totalRow 0).homology q ≅ H0 :=
    B.totalRowHomologyIsoAt 0 q q (Nat.zero_add q)
  let eComponent : K.X 0 ≅ H0 := χ.componentIso q 0
  let eP12 : χ.pageOne.homology (0, q) ≅ P2 :=
    χ.pageOneTwoIso 0 q
  let ePageTwo : P2 ≅ χ.pageTwoCoordinate 0 q :=
    χ.pageTwoCoordinateIso 0 q
  let eV : P2 ≅ V.homology 0 :=
    χ.secondPageVerticalHomologyIso 0 q
  let eStepCanonical : S0 ≅ HStage := by
    change
      ((Y.H (-(q : ℤ))).obj
        (CategoryTheory.ComposableArrows.mk₁
          (homOfLE (show (⊥ : EInt) ≤ (((0 : ℕ) : ℤ) : EInt) by simp)))) ≅
        HStage
    exact B.partialTotalSpectralStepHomologyIso q 0
  let stepP1 : S0 ⟶ P1 :=
    B.partialTotalSpectralStepZeroToFirstPage q
  let pageStable : P2 ⟶ Stable0 :=
    B.partialTotalZeroColumnPageToStable q
  let eLeft : StableSource ≅ χ.pageTwoCoordinate 0 q :=
    B.partialTotalZeroColumnPageTwoLeftIso q
  let stableTail : StableSource ⟶ Stable0 :=
    B.partialTotalZeroColumnStableTail q
  have hRepresentative :=
    χ.secondPageVerticalHomologyIso_inv_representation_zero q
  dsimp only at hRepresentative ⊢
  change
    (B.verticalHomologyComplex q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀ (B.verticalHomologyComplex q)).inv ≫ eV.inv ≫
        B.partialTotalZeroColumnEdge q =
      HomologicalComplex.homologyMap B.partialTotalZeroRowToTotal q
  change
    (B.verticalHomologyComplex q).pOpcycles 0 ≫
        (ChainComplex.isoHomologyι₀ (B.verticalHomologyComplex q)).inv ≫ eV.inv =
      eComponent.inv ≫ K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫
        eRestr.hom ≫ eP12.hom at hRepresentative
  have hStageZero :
      HomologicalComplex.homologyMap s q ≫ eStepCanonical.inv ≫ stepP1 =
        eH.inv ≫ eF.inv := by
    change
      HomologicalComplex.homologyMap
            B.partialTotalZeroRowToPartialTotal q ≫
          (B.partialTotalSpectralStepHomologyIso q 0).inv ≫
          B.partialTotalSpectralStepZeroToFirstPage q =
        (B.totalRowHomologyIsoAt 0 q q (Nat.zero_add q)).inv ≫
          (χ.firstPageRowIsoAt 0 q q (Nat.zero_add q)).inv
    exact
      B.partialTotalZeroRowToPartialTotal_homologyMap_comp_stepZeroToFirstPage q
  let D := χ.pageOneHomologyData 0 q
  let S := χ.pageOne.sc' η.pqPrev (0, q) η.pqNext
  have hRestrictionCyclesInclusion :
      eCycles.hom ≫ χ.pageOne.iCycles (0, q) =
        K.iCycles 0 ≫ eX.hom := by
    exact χ.restrictionCyclesIso_hom_iCycles ρ
  have hRestrictionProjection :
      K.homologyπ 0 ≫ eRestr.hom =
        eCycles.hom ≫ χ.pageOne.homologyπ (0, q) := by
    exact χ.homologyπ_restrictionHomologyIso_hom ρ
  let rightIncrementRaw := Y.mapFourδ₄Toδ₃'
    η.i₀' η.i₁ η.i₂ η.i₃ η.i₃'
      η.hi₀'₁ η.hi₁₂ η.hi₂₃ η.hi₃₃'
      η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  let rightIncrement : D.left.K ⟶ D.left.H := by
    exact rightIncrementRaw
  have hLeftProjection : D.left.π = rightIncrement := by
    dsimp only [rightIncrement]
    exact χ.pageOneHomologyData_left_π 0 q
  have hLeftInclusion := χ.pageOneHomologyData_left_i 0 q
  let leftIncrementRaw := Y.mapFourδ₁Toδ₀'
    η.i₀' η.i₀ η.i₁ η.i₂ η.i₃
      η.hi₀'₀ η.hi₀₁ η.hi₁₂ η.hi₂₃
      η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  let ePageOneRaw :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      Y core 1 χ.pageOneBound (0, q)
      η.i₀ η.i₁ η.i₂ η.i₃
      η.hi₀ η.hi₁ η.hi₂ η.hi₃
      η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂
  have hDataInclusion : D.left.i = leftIncrementRaw ≫ ePageOneRaw.inv := by
    exact hLeftInclusion
  have hLeft : IsZero ((Y.H η.n₂).obj
      (CategoryTheory.ComposableArrows.mk₁ (homOfLE η.hiBot₀'))) := by
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      η.n₂ ((0 : ℤ) - 2) (by omega)
  let eLeftOldRaw := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) η.i₀' η.i₁ η.i₂ η.i₃
      η.hiBot₀' η.hi₀'₁ η.hi₁₂ η.hi₂₃
      η.n₀ η.n₁ η.n₂ hLeft (hn₁ := η.hn₁) (hn₂ := η.hn₂)
  let bottomRight := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) η.i₁ η.i₂ η.i₃ η.i₃'
      η.hiBot₁ η.hi₁₂ η.hi₂₃ η.hi₃₃'
      η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  let eLeftNewRaw := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) η.i₀' η.i₁ η.i₂ η.i₃'
      η.hiBot₀' η.hi₀'₁ η.hi₁₂ η.hi₂₃'
      η.n₀ η.n₁ η.n₂ hLeft (hn₁ := η.hn₁) (hn₂ := η.hn₂)
  let eRawCoordinate := χ.pageTwoRawCoordinateIso 0 q
  let ePageTwoRaw : χ.pageTwo.X (0, q) ≅
      Y.E (homOfLE η.hi₀'₁) (homOfLE η.hi₁₂) (homOfLE η.hi₂₃')
        η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ :=
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
      Y core 2 χ.pageTwoBound (0, q)
      η.i₀' η.i₁ η.i₂ η.i₃'
      η.hi₀' η.hi₁ η.hi₂ η.hi₃'
      η.n₀ η.n₁ η.n₂ η.hn η.hn₁ η.hn₂
  have hRawCoordinate :
      eRawCoordinate = ePageTwoRaw.symm ≪≫ ePageTwoRaw := by
    rfl
  have hRawCoordinateHom : eRawCoordinate.hom =
      𝟙 (Y.E (homOfLE η.hi₀'₁) (homOfLE η.hi₁₂)
        (homOfLE η.hi₂₃') η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂) := by
    rw [hRawCoordinate]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.inv_hom_id]
    rfl
  have hRawInter : eLeftOldRaw.hom ≫ rightIncrementRaw =
      bottomRight ≫ eLeftNewRaw.hom := by
    exact Y.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃'
      (⊥ : EInt) η.i₀' η.i₁ η.i₂ η.i₃ η.i₃'
      η.hiBot₀' η.hi₀'₁ η.hi₁₂ η.hi₂₃ η.hi₃₃'
      η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  have hInter : (eLeftOldRaw.hom ≫ rightIncrementRaw) ≫
      eRawCoordinate.hom =
      bottomRight ≫ eLeft.hom := by
    calc
      _ = (bottomRight ≫ eLeftNewRaw.hom) ≫
          eRawCoordinate.hom :=
        congrArg (fun k => k ≫ eRawCoordinate.hom) hRawInter
      _ = _ := by
        dsimp only [eLeft, partialTotalZeroColumnPageTwoLeftIso,
          eRawCoordinate, Iso.trans_hom]
        simp only [Category.assoc]
        rfl
  have hCrossRaw :
      rightIncrementRaw ≫ (eRawCoordinate.hom ≫ eLeft.inv) =
        eLeftOldRaw.inv ≫ bottomRight := by
    apply (cancel_epi eLeftOldRaw.hom).1
    calc
      eLeftOldRaw.hom ≫
          (rightIncrementRaw ≫ (eRawCoordinate.hom ≫ eLeft.inv)) =
          (((eLeftOldRaw.hom ≫ rightIncrementRaw) ≫
            eRawCoordinate.hom) ≫ eLeft.inv) := by
        simp only [Category.assoc]
      _ = (bottomRight ≫ eLeft.hom) ≫ eLeft.inv :=
        congrArg (fun k => k ≫ eLeft.inv) hInter
      _ = bottomRight := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = eLeftOldRaw.hom ≫
          (eLeftOldRaw.inv ≫ bottomRight) := by
        simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc] at hCrossRaw
  rw [hRawCoordinateHom] at hCrossRaw
  have hCompId := Category.comp_id rightIncrementRaw
  have hWhole :
      (rightIncrementRaw ≫
          𝟙 (Y.E (homOfLE η.hi₀'₁) (homOfLE η.hi₁₂)
            (homOfLE η.hi₂₃') η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂)) ≫ eLeft.inv =
        rightIncrementRaw ≫ eLeft.inv :=
    congrArg (fun k => k ≫ eLeft.inv) hCompId
  have hCross : rightIncrementRaw ≫ eLeft.inv =
      eLeftOldRaw.inv ≫ bottomRight := by
    exact hWhole.symm.trans hCrossRaw
  let f₁ : (⊥ : EInt) ⟶ η.i₁ := homOfLE η.hiBot₁
  let f₂ : η.i₁ ⟶ η.i₂ := homOfLE η.hi₁₂
  let f₃old : η.i₂ ⟶ η.i₃ := homOfLE η.hi₂₃
  let f₃ : η.i₂ ⟶ η.i₃' := homOfLE η.hi₂₃'
  let f₁₂ : (⊥ : EInt) ⟶ η.i₂ :=
    homOfLE (η.hiBot₀'.trans (η.hi₀'₁.trans η.hi₁₂))
  let sourceIso : S0 ≅ (Y.H η.n₁).obj (mk₁ f₁₂) := by
    exact B.partialTotalStageZeroSourceIso q
  let α : CategoryTheory.ComposableArrows.mk₃ f₁ f₂ f₃old ⟶
      CategoryTheory.ComposableArrows.mk₃ f₁ f₂ f₃ :=
    CategoryTheory.ComposableArrows.homMk₃
      (𝟙 _) (𝟙 _) (𝟙 _) (homOfLE η.hi₃₃')
      (by subsingleton) (by subsingleton) (by subsingleton)
  let β : CategoryTheory.ComposableArrows.mk₂ f₁₂ f₃old ⟶
      CategoryTheory.ComposableArrows.mk₂ f₁₂ f₃ :=
    CategoryTheory.ComposableArrows.homMk₂
      (𝟙 _) (𝟙 _) (homOfLE η.hi₃₃')
      (by subsingleton) (by subsingleton)
  let oldOpE := Y.opcyclesToE f₁ f₂ f₃old f₁₂
    (by subsingleton) η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  let newOpE := Y.opcyclesToE f₁ f₂ f₃ f₁₂
    (by subsingleton) η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  have hPageOpMap : oldOpE ≫ bottomRight =
      Y.opcyclesMap f₁₂ f₃old f₁₂ f₃ β η.n₁ ≫ newOpE := by
    exact Y.opcyclesToE_map f₁ f₂ f₃old f₁₂ (by subsingleton)
      f₁ f₂ f₃ f₁₂ (by subsingleton) α β η.n₀ η.n₁ η.n₂
  let γ : CategoryTheory.ComposableArrows.mk₁ f₁₂ ⟶
      CategoryTheory.ComposableArrows.mk₁ f₁₂ := 𝟙 _
  have hPageP : Y.pOpcycles f₁₂ f₃old η.n₁ ≫
      Y.opcyclesMap f₁₂ f₃old f₁₂ f₃ β η.n₁ =
        Y.pOpcycles f₁₂ f₃ η.n₁ := by
    have h := Y.p_opcyclesMap f₁₂ f₃old f₁₂ f₃ β γ η.n₁
      (by subsingleton)
    have hγ : (Y.H η.n₁).map γ = 𝟙 _ := by
      dsimp only [γ]
      exact (Y.H η.n₁).map_id _
    simpa only [hγ, Category.id_comp] using h
  have hPageOpTailCore :
      Y.pOpcycles f₁₂ f₃old η.n₁ ≫ oldOpE ≫ bottomRight =
      Y.pOpcycles f₁₂ f₃ η.n₁ ≫ newOpE := by
    slice_lhs 2 3 => rw [hPageOpMap]
    slice_lhs 1 2 => rw [hPageP]
  let eData : S.homology ≅ χ.pageTwoCoordinate 0 q := by
    exact D.left.homologyIso
  let pageOneCoordinateRaw : χ.pageOne.homology (0, q) ≅
      χ.pageTwoCoordinate 0 q :=
    χ.pageOne.homologyIsoSc'
      η.pqPrev (0, q) η.pqNext η.hpq η.hpq' ≪≫ eData
  have hCoordinate :
      (χ.pageOneHomologyCoordinateIso 0 q).hom =
        pageOneCoordinateRaw.hom := by
    rfl
  have hData : eData.hom = D.left.homologyIso.hom := by
    rfl
  let dataRepresentative : S.cycles ⟶ χ.pageTwoCoordinate 0 q := by
    exact D.left.cyclesIso.hom ≫ D.left.π
  have hDataProjection :
      S.homologyπ ≫ eData.hom = dataRepresentative := by
    rw [hData]
    change S.homologyπ ≫ D.left.homologyIso.hom =
      D.left.cyclesIso.hom ≫ D.left.π
    exact D.left.homologyπ_comp_homologyIso_hom
  let rightRepresentative : S.cycles ⟶ χ.pageTwoCoordinate 0 q := by
    exact D.left.cyclesIso.hom ≫ rightIncrement
  have hDataToRight : dataRepresentative = rightRepresentative := by
    dsimp only [dataRepresentative, rightRepresentative]
    rw [hLeftProjection]
  let bottomCyclesRepresentative : S.cycles ⟶ StableSource := by
    exact rightRepresentative ≫ eLeft.inv
  have hDataRepresentative :
      dataRepresentative ≫ eLeft.inv = bottomCyclesRepresentative := by
    rw [hDataToRight]
  let eDataBottom : D.left.H ⟶ StableSource := by
    exact eLeft.inv
  let eDataOld :
      Y.E f₁ f₂ (homOfLE η.hi₂₃)
        η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ≅ D.left.K := by
    exact eLeftOldRaw
  let bottomLeftRaw := Y.mapFourδ₁Toδ₀'
    (⊥ : EInt) η.i₀ η.i₁ η.i₂ η.i₃
      (η.hiBot₀'.trans η.hi₀'₀) η.hi₀₁ η.hi₁₂ η.hi₂₃
      η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  let pageOneCoordinate := Y.E
    (homOfLE η.hi₀₁) (homOfLE η.hi₁₂) (homOfLE η.hi₂₃)
    η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  let leftIncrementData : D.left.K ⟶ pageOneCoordinate := by
    exact leftIncrementRaw
  let pageOneInvData : pageOneCoordinate ⟶ S.X₂ := by
    exact ePageOneRaw.inv
  let bottomLeftData :
      Y.E f₁ f₂ f₃old η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ⟶
        pageOneCoordinate := by
    exact bottomLeftRaw
  have hLeftComp : eLeftOldRaw.hom ≫ leftIncrementRaw = bottomLeftRaw := by
    exact Y.mapFourδ₁Toδ₀'_comp
      (⊥ : EInt) η.i₀' η.i₀ η.i₁ η.i₂ η.i₃
      η.hiBot₀' η.hi₀'₀ η.hi₀₁ η.hi₁₂ η.hi₂₃
      η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  have hDataInclusionPack : D.left.i =
      leftIncrementData ≫ pageOneInvData := by
    exact hDataInclusion
  have hLeftCompPack : eDataOld.hom ≫ leftIncrementData =
      bottomLeftData := by
    exact hLeftComp
  let bottomToPage :
      Y.E f₁ f₂ f₃old η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ ⟶ S.X₂ :=
    bottomLeftData ≫ pageOneInvData
  have hDataOldInclusion : eDataOld.hom ≫ D.left.i =
      bottomToPage := by
    dsimp only [bottomToPage]
    rw [hDataInclusionPack]
    slice_lhs 1 2 => rw [hLeftCompPack]
  have hRightTail : rightIncrement ≫ eDataBottom =
      eDataOld.inv ≫ bottomRight := by
    change rightIncrementRaw ≫ eLeft.inv =
      eLeftOldRaw.inv ≫ bottomRight
    exact hCross
  let bottomCyclesRaw : S.cycles ⟶ StableSource := by
    exact D.left.cyclesIso.hom ≫ rightIncrement ≫ eDataBottom
  have hBottomCyclesRaw : bottomCyclesRepresentative = bottomCyclesRaw := by
    change (D.left.cyclesIso.hom ≫ rightIncrement) ≫ eDataBottom =
      D.left.cyclesIso.hom ≫ rightIncrement ≫ eDataBottom
    simp only [Category.assoc]
  let pageOneToBottomRaw : χ.pageOne.homology (0, q) ≅ StableSource :=
    pageOneCoordinateRaw ≪≫ eLeft.symm
  have hPageOneToBottom :
      (χ.pageOneHomologyCoordinateIso 0 q).hom ≫ eLeft.inv =
        pageOneToBottomRaw.hom := by
    rw [hCoordinate]
    dsimp only [pageOneToBottomRaw]
    simp only [Iso.trans_hom, Iso.symm_hom]
  let rawRowCoordinate : S0 ⟶ K.X 0 := stepP1 ≫ eX.inv
  let oldRepresentativeCore : (Y.H η.n₁).obj (mk₁ f₁₂) ⟶
      Y.E f₁ f₂ f₃old η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ :=
    Y.pOpcycles f₁₂ f₃old η.n₁ ≫ oldOpE
  let bottomRepresentativeCore : (Y.H η.n₁).obj (mk₁ f₁₂) ⟶
      StableSource :=
    Y.pOpcycles f₁₂ f₃ η.n₁ ≫ newOpE
  let oldRepresentative : S0 ⟶
      Y.E f₁ f₂ f₃old η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ :=
    sourceIso.hom ≫ oldRepresentativeCore
  let bottomRepresentative : S0 ⟶ StableSource :=
    sourceIso.hom ≫ bottomRepresentativeCore
  have hStepP1Terminal : oldRepresentative ≫ bottomToPage = stepP1 := by
    let pq : ℕ × ℕ := (0, q)
    let b : EInt := ⊥
    let m : EInt := (core).i₁ pq
    let z : EInt := (core).i₂ pq
    let n₁ : ℤ := (core).deg pq
    let n₀ : ℤ := n₁ - 1
    let n₂ : ℤ := n₁ + 1
    have hn₁ : n₀ + 1 = n₁ := by omega
    have hn₂ : n₁ + 1 = n₂ := rfl
    have hbb : b ≤ b := le_rfl
    have hbm : b ≤ m := bot_le
    have hmm : m ≤ m := le_rfl
    have hmz : m ≤ z := (core).le₁₂ pq
    have hzz : z ≤ z := le_rfl
    let f₁c : b ⟶ m := homOfLE bot_le
    let f₂c : m ⟶ z := homOfLE ((core).le₁₂ pq)
    let f₁₂c : b ⟶ z :=
      homOfLE (bot_le.trans ((core).le₁₂ pq))
    have hIdSource : (𝟙 b) ≫ f₁₂c = f₁₂c := by simp
    have hComp : f₁c ≫ f₂c = f₁₂c := by subsingleton
    let αCan : mk₁ f₁₂c ⟶ mk₁ f₂c :=
      twoδ₁Toδ₀' b m z bot_le ((core).le₁₂ pq)
    let sourcePacket :
        (Y.H n₁).obj (mk₁ f₁₂c) ⟶
          Y.E (𝟙 b) f₁₂c (𝟙 z) n₀ n₁ n₂ hn₁ hn₂ :=
      Y.pOpcycles f₁₂c (𝟙 z) n₁ ≫
        Y.opcyclesToE (𝟙 b) f₁₂c (𝟙 z) f₁₂c hIdSource
          n₀ n₁ n₂ hn₁ hn₂
    let eSourceH := Y.EIsoH f₁₂c n₀ n₁ n₂ hn₁ hn₂
    let eTargetH := Y.EIsoH f₂c n₀ n₁ n₂ hn₁ hn₂
    have hSource : sourcePacket = eSourceH.inv := by
      apply (cancel_mono eSourceH.hom).1
      dsimp only [sourcePacket]
      simp only [Category.assoc]
      rw [Y.p_opcyclesToE_assoc (𝟙 b) f₁₂c (𝟙 z) f₁₂c hIdSource
        n₀ n₁ n₂ hn₁ hn₂]
      dsimp only [eSourceH]
      rw [Y.πE_EIsoH_hom f₁₂c n₀ n₁ n₂ hn₁ hn₂]
      rw [Y.cyclesIsoH_inv_hom_id f₁₂c n₁ n₂ hn₂]
      exact eSourceH.inv_hom_id.symm
    let βSplit :
        mk₃ (𝟙 b) f₁₂c (𝟙 z) ⟶ mk₃ f₁c f₂c (𝟙 z) :=
      fourδ₂Toδ₁' b b m z z hbb hbm hmz hzz
    let βCut :
        mk₃ f₁c f₂c (𝟙 z) ⟶ mk₃ (𝟙 m) f₂c (𝟙 z) :=
      fourδ₁Toδ₀' b m m z z hbm hmm hmz hzz
    let βDirect :
        mk₃ (𝟙 b) f₁₂c (𝟙 z) ⟶ mk₃ (𝟙 m) f₂c (𝟙 z) :=
      homMk₃ f₁c f₁c (𝟙 z) (𝟙 z)
        (by subsingleton) (naturality' αCan 0 1)
        (by subsingleton)
    have hβ : βSplit ≫ βCut = βDirect := by
      apply hom_ext₃ <;> subsingleton
    let mapSplit :=
      Y.map (𝟙 b) f₁₂c (𝟙 z) f₁c f₂c (𝟙 z) βSplit
        n₀ n₁ n₂ hn₁ hn₂
    let mapCut :=
      Y.map f₁c f₂c (𝟙 z) (𝟙 m) f₂c (𝟙 z) βCut
        n₀ n₁ n₂ hn₁ hn₂
    let mapDirect :=
      Y.map (𝟙 b) f₁₂c (𝟙 z) (𝟙 m) f₂c (𝟙 z) βDirect
        n₀ n₁ n₂ hn₁ hn₂
    have hDirect : mapSplit ≫ mapCut = mapDirect := by
      dsimp only [mapSplit, mapCut, mapDirect]
      rw [← Y.map_comp (𝟙 b) f₁₂c (𝟙 z)
        f₁c f₂c (𝟙 z) (𝟙 m) f₂c (𝟙 z)
        βSplit βCut n₀ n₁ n₂ hn₁ hn₂]
      rw [hβ]
    let βId : mk₂ f₁₂c (𝟙 z) ⟶ mk₂ f₁₂c (𝟙 z) := 𝟙 _
    have hOp :=
      Y.opcyclesToE_map
        (𝟙 b) f₁₂c (𝟙 z) f₁₂c hIdSource
        f₁c f₂c (𝟙 z) f₁₂c hComp
        βSplit βId n₀ n₁ n₂
        (h₀ := by subsingleton) (h₁ := by subsingleton)
        (hn₁ := hn₁) (hn₂ := hn₂)
    let rawOld :
        (Y.H n₁).obj (mk₁ f₁₂c) ⟶
          Y.E f₁c f₂c (𝟙 z) n₀ n₁ n₂ hn₁ hn₂ :=
      Y.pOpcycles f₁₂c (𝟙 z) n₁ ≫
        Y.opcyclesToE f₁c f₂c (𝟙 z) f₁₂c hComp
          n₀ n₁ n₂ hn₁ hn₂
    have hSplit : sourcePacket ≫ mapSplit = rawOld := by
      dsimp only [sourcePacket, mapSplit, rawOld]
      simp only [Category.assoc]
      rw [hOp]
      dsimp only [βId]
      rw [Y.opcyclesMap_id]
      simp only [Category.id_comp]
    have hNat : mapDirect ≫ eTargetH.hom =
        eSourceH.hom ≫ (Y.H n₁).map αCan := by
      dsimp only [mapDirect, eTargetH, eSourceH]
      exact Y.EIsoH_hom_naturality
        f₁₂c f₂c αCan βDirect n₀ n₁ n₂
        (hβ := by apply hom_ext₃ <;> subsingleton)
        (hn₁ := hn₁) (hn₂ := hn₂)
    have hRaw : rawOld ≫ mapCut =
        (Y.H n₁).map αCan ≫ eTargetH.inv := by
      apply (cancel_mono eTargetH.hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [← reassoc_of% hSplit]
      rw [reassoc_of% hDirect]
      rw [hSource]
      rw [hNat]
      simp only [Iso.inv_hom_id_assoc]
    let ePage : χ.pageOne.X (0, q) ≅ Y.E (𝟙 m) f₂c (𝟙 z)
        n₀ n₁ n₂ hn₁ hn₂ := by
      exact CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso
        Y core 1 χ.pageOneBound pq
        m m z z
        (by rw [(core).hi₀₁]) rfl rfl
        (by rw [← (core).hi₂₃])
        n₀ n₁ n₂ rfl hn₁ hn₂
    let eCore := χ.firstPageCoreIsoAt 0 q
    have hCoreBody : eCore = ePage ≪≫ eTargetH := by
      apply Iso.ext
      have h := congrArg Iso.hom
        (χ.firstPageCoreIsoAtOfCut_eq
          0 q m rfl n₀ n₂ hn₁ hn₂)
      change eCore.hom = ePage.hom ≫ eTargetH.hom at h
      simpa only [Iso.trans_hom] using h
    have hRawTerminal : rawOld ≫ mapCut ≫ ePage.inv =
        (Y.H n₁).map αCan ≫ eCore.inv := by
      rw [hCoreBody]
      simp only [Iso.trans_inv]
      exact (reassoc_of% hRaw) ePage.inv
    have hCoreHom : (B.partialTotalSpectralStepZeroCoreIso q).hom =
        sourceIso.hom ≫ (Y.H n₁).map αCan := by
      exact B.partialTotalSpectralStepZeroCoreIso_hom q
    have hOldCore : oldRepresentativeCore = rawOld := by
      rfl
    have hBottomPage : bottomToPage = mapCut ≫ ePage.inv := by
      rfl
    have hCoreWhisker :
        (sourceIso.hom ≫ (Y.H n₁).map αCan) ≫ eCore.inv =
          (B.partialTotalSpectralStepZeroCoreIso q).hom ≫ eCore.inv :=
      congrArg (fun k => k ≫ eCore.inv) hCoreHom.symm
    have hOuterAssoc :
        (sourceIso.hom ≫ rawOld) ≫ (mapCut ≫ ePage.inv) =
          sourceIso.hom ≫ (rawOld ≫ mapCut ≫ ePage.inv) :=
      Category.assoc sourceIso.hom rawOld (mapCut ≫ ePage.inv)
    have hRawWhisker :
        sourceIso.hom ≫ (rawOld ≫ mapCut ≫ ePage.inv) =
          sourceIso.hom ≫ ((Y.H n₁).map αCan ≫ eCore.inv) :=
      congrArg (fun k => sourceIso.hom ≫ k) hRawTerminal
    have hInnerAssoc :
        sourceIso.hom ≫ ((Y.H n₁).map αCan ≫ eCore.inv) =
          (sourceIso.hom ≫ (Y.H n₁).map αCan) ≫ eCore.inv :=
      (Category.assoc sourceIso.hom ((Y.H n₁).map αCan) eCore.inv).symm
    have hStepDef :
        (B.partialTotalSpectralStepZeroCoreIso q).hom ≫ eCore.inv =
          stepP1 := by
      rfl
    dsimp only [oldRepresentative]
    rw [hOldCore, hBottomPage]
    exact hOuterAssoc.trans
      (hRawWhisker.trans (hInnerAssoc.trans (hCoreWhisker.trans hStepDef)))
  have hOldBottom :
      sourceIso.hom ≫ Y.pOpcycles f₁₂ f₃old η.n₁ ≫ oldOpE ≫
          bottomToPage = stepP1 := by
    simpa only [oldRepresentative, oldRepresentativeCore, Category.assoc]
      using hStepP1Terminal
  have hDegreeZero :
      K.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ K).inv =
        (ChainComplex.cycles₀Iso K).inv ≫ K.homologyπ 0 := by
    apply (cancel_mono (K.homologyι 0)).1
    simp only [Category.assoc]
    rw [HomologicalComplex.homology_π_ι]
    change K.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ K).inv ≫
        (ChainComplex.isoHomologyι₀ K).hom =
      (ChainComplex.cycles₀Iso K).inv ≫
        (ChainComplex.cycles₀Iso K).hom ≫ K.pOpcycles 0
    simp only [Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
  have hPageCyclesInclusion :
      (χ.pageOne.cyclesIsoSc'
          η.pqPrev (0, q) η.pqNext η.hpq η.hpq').hom ≫
          S.iCycles =
        χ.pageOne.iCycles (0, q) := by
    exact χ.pageOne.cyclesIsoSc'_hom_iCycles
      η.pqPrev (0, q) η.pqNext η.hpq η.hpq'
  let pageICycles : χ.pageOne.cycles (0, q) ⟶ S.X₂ :=
    χ.pageOne.iCycles (0, q)
  have hPageCyclesData :
      (χ.pageOne.cyclesIsoSc'
          η.pqPrev (0, q) η.pqNext η.hpq η.hpq').hom ≫
          S.iCycles = pageICycles := by
    exact hPageCyclesInclusion
  let stepP1Sc : S0 ⟶ S.X₂ := by
    exact stepP1
  have hOldBottomSc :
      sourceIso.hom ≫ Y.pOpcycles f₁₂ f₃old η.n₁ ≫ oldOpE ≫
          bottomToPage = stepP1Sc := by
    exact hOldBottom
  let eRestrictionScX : K.X 0 ≅ S.X₂ := eX
  let rawRowCoordinateSc : S0 ⟶ K.X 0 :=
    stepP1Sc ≫ eRestrictionScX.inv
  have hRawRowSc : rawRowCoordinate = rawRowCoordinateSc := by
    rfl
  have hRestrictionCyclesSc : eCycles.hom ≫ pageICycles =
      K.iCycles 0 ≫ eRestrictionScX.hom := by
    exact hRestrictionCyclesInclusion
  have hCyclesZero : (ChainComplex.cycles₀Iso K).inv ≫ K.iCycles 0 = 𝟙 _ := by
    exact (ChainComplex.cycles₀Iso K).inv_hom_id
  have hOldPrefix :
      rawRowCoordinateSc ≫ (ChainComplex.cycles₀Iso K).inv ≫
          eCycles.hom ≫
          (χ.pageOne.cyclesIsoSc'
            η.pqPrev (0, q) η.pqNext η.hpq η.hpq').hom ≫
          D.left.cyclesIso.hom ≫ eDataOld.inv =
        oldRepresentative := by
    apply (cancel_mono eDataOld.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply (cancel_mono D.left.i).1
    simp only [Category.assoc]
    rw [D.left.cyclesIso_hom_comp_i]
    slice_rhs 4 5 => rw [hDataOldInclusion]
    rw [hPageCyclesData]
    rw [hRestrictionCyclesSc]
    rw [reassoc_of% hCyclesZero]
    rw [hOldBottomSc]
    dsimp only [rawRowCoordinateSc]
    calc
      (stepP1Sc ≫ eRestrictionScX.inv) ≫ eRestrictionScX.hom =
          stepP1Sc ≫ (eRestrictionScX.inv ≫ eRestrictionScX.hom) :=
        Category.assoc _ _ _
      _ = stepP1Sc ≫ 𝟙 _ := congrArg
        (fun k => stepP1Sc ≫ k) eRestrictionScX.inv_hom_id
      _ = stepP1Sc := Category.comp_id _
  have hOldToNew : oldRepresentative ≫ bottomRight =
      bottomRepresentative := by
    dsimp only [oldRepresentative, oldRepresentativeCore,
      bottomRepresentative, bottomRepresentativeCore]
    simpa only [Category.assoc] using congrArg
      (fun k => sourceIso.hom ≫ k) hPageOpTailCore
  have hRawRow : rawRowCoordinate = stepP1 ≫ eX.inv := by
    rfl
  have hPublicSc : stepP1 ≫ eX.inv = rawRowCoordinateSc :=
    hRawRow.symm.trans hRawRowSc
  have hOldPrefixPublic := hOldPrefix
  rw [← hPublicSc] at hOldPrefixPublic
  have hDataRepresentativeRaw :
      D.left.cyclesIso.hom ≫ D.left.π ≫ eLeft.inv =
        bottomCyclesRepresentative := by
    simpa only [dataRepresentative, Category.assoc] using
      hDataRepresentative
  have hRawCoordinate :
      stepP1 ≫ eX.inv ≫ K.pOpcycles 0 ≫
          (ChainComplex.isoHomologyι₀ K).inv ≫ eRestr.hom ≫
          (χ.pageOneHomologyCoordinateIso 0 q).hom ≫ eLeft.inv =
        bottomRepresentative := by
    slice_lhs 1 2 => rw [← hRawRow]
    slice_lhs 3 4 => rw [hDegreeZero]
    slice_lhs 6 7 => rw [hPageOneToBottom]
    dsimp only [pageOneToBottomRaw, pageOneCoordinateRaw,
      Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc]
    rw [reassoc_of% hRestrictionProjection]
    rw [reassoc_of% HomologicalComplex.π_homologyIsoSc'_hom]
    rw [reassoc_of% hDataProjection]
    slice_lhs 6 8 => rw [hDataRepresentativeRaw]
    rw [hBottomCyclesRaw]
    dsimp only [bottomCyclesRaw]
    slice_lhs 7 8 => rw [hRightTail]
    rw [reassoc_of% hOldPrefixPublic]
    rw [hOldToNew]
  let f₃Top : η.i₂ ⟶ (⊤ : EInt) :=
    homOfLE (η.hi₂₃'.trans η.hi₃'Top)
  let αRight : CategoryTheory.ComposableArrows.mk₃ f₁ f₂ f₃ ⟶
      CategoryTheory.ComposableArrows.mk₃ f₁ f₂ f₃Top :=
    CategoryTheory.ComposableArrows.homMk₃
      (𝟙 _) (𝟙 _) (𝟙 _) (homOfLE η.hi₃'Top)
      (by subsingleton) (by subsingleton) (by subsingleton)
  let βRight : CategoryTheory.ComposableArrows.mk₂ f₁₂ f₃ ⟶
      CategoryTheory.ComposableArrows.mk₂ f₁₂ f₃Top :=
    CategoryTheory.ComposableArrows.homMk₂
      (𝟙 _) (𝟙 _) (homOfLE η.hi₃'Top)
      (by subsingleton) (by subsingleton)
  let topOpE := Y.opcyclesToE f₁ f₂ f₃Top f₁₂
    (by subsingleton) η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  let rightOuter := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) η.i₁ η.i₂ η.i₃' ⊤
    η.hiBot₁ η.hi₁₂ η.hi₂₃' η.hi₃'Top
    η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂
  let eStableTarget := B.partialTotalZeroColumnStableTargetIso q
  have hStableOpMapRaw : newOpE ≫ rightOuter =
      Y.opcyclesMap f₁₂ f₃ f₁₂ f₃Top βRight η.n₁ ≫ topOpE
      := by
    change newOpE ≫
        Y.map f₁ f₂ f₃ f₁ f₂ f₃Top αRight
          η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ = _
    exact Y.opcyclesToE_map f₁ f₂ f₃ f₁₂ (by subsingleton)
      f₁ f₂ f₃Top f₁₂ (by subsingleton) αRight βRight
        η.n₀ η.n₁ η.n₂
  have hStableOpMap : newOpE ≫ stableTail =
      Y.opcyclesMap f₁₂ f₃ f₁₂ f₃Top βRight η.n₁ ≫ topOpE ≫
        eStableTarget.hom := by
    have h := congrArg (fun k => k ≫ eStableTarget.hom) hStableOpMapRaw
    dsimp only [stableTail, partialTotalZeroColumnStableTail,
      rightOuter, eStableTarget]
    simpa only [Category.assoc] using h
  let γRight : CategoryTheory.ComposableArrows.mk₁ f₁₂ ⟶
      CategoryTheory.ComposableArrows.mk₁ f₁₂ := 𝟙 _
  have hStableP : Y.pOpcycles f₁₂ f₃ η.n₁ ≫
      Y.opcyclesMap f₁₂ f₃ f₁₂ f₃Top βRight η.n₁ =
        Y.pOpcycles f₁₂ f₃Top η.n₁ := by
    have h := Y.p_opcyclesMap f₁₂ f₃ f₁₂ f₃Top βRight γRight η.n₁
      (by subsingleton)
    have hγ : (Y.H η.n₁).map γRight = 𝟙 _ := by
      dsimp only [γRight]
      exact (Y.H η.n₁).map_id _
    simpa only [hγ, Category.id_comp] using h
  have hStableOpTailCore : bottomRepresentativeCore ≫ stableTail =
      Y.pOpcycles f₁₂ f₃Top η.n₁ ≫ topOpE ≫
        eStableTarget.hom := by
    dsimp only [bottomRepresentativeCore]
    change (Y.pOpcycles f₁₂ f₃ η.n₁ ≫ newOpE) ≫ stableTail = _
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [hStableOpMap]
    slice_lhs 1 2 => rw [hStableP]
    exact Category.assoc _ _ _
  have hStableOpTail : bottomRepresentative ≫ stableTail =
      sourceIso.hom ≫ Y.pOpcycles f₁₂ f₃Top η.n₁ ≫ topOpE ≫
        eStableTarget.hom := by
    dsimp only [bottomRepresentative]
    simpa only [Category.assoc] using congrArg
      (fun k => sourceIso.hom ≫ k) hStableOpTailCore
  let gLiteral : S0 ⟶ Stable0 :=
    bottomRepresentative ≫ stableTail
  have hLiteral :
      gLiteral =
        Y.stableIntervalStepToStable n
          (partialTotalHomologyPreviousIndex_le 0) := by
    dsimp only [gLiteral]
    rw [hStableOpTail]
    let hSourceEta : S0 = (Y.H η.n₁).obj (mk₁ f₁₂) := by
      dsimp only [S0, n, i, stableIntervalStep,
        stableIntervalLeftMiddle, f₁₂, η,
        PartialTotalFirstPageChoice.pageTransitionIndex]
      rw [show -(q : ℤ) = -(0 : ℤ) - (q : ℤ) by omega]
      simp only [Int.cast_ofNat_Int, Int.neg_zero]
    have hSourceEtaLaw : sourceIso.hom = eqToHom hSourceEta := by
      dsimp only [sourceIso]
      exact B.partialTotalStageZeroSourceIso_hom_eqToHom q
    rw [hSourceEtaLaw]
    change eqToHom hSourceEta ≫
      (Y.pOpcycles f₁₂ f₃Top η.n₁ ≫ topOpE ≫
        eStableTarget.hom) = _
    apply eq_of_heq
    rw [CategoryTheory.eqToHom_comp_heq_iff]
    dsimp only [topOpE]
    rw [← Category.assoc]
    rw [Y.p_opcyclesToE f₁ f₂ f₃Top f₁₂ (by subsingleton)
      η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂]
    dsimp only [eStableTarget, partialTotalZeroColumnStableTargetIso]
    rw [CategoryTheory.eqToIso.hom]
    rw [CategoryTheory.comp_eqToHom_heq_iff]
    let ℓ₁ := stableIntervalLeft (partialTotalHomologyPreviousIndex 0)
    let ℓ₂ := stableIntervalMiddle (partialTotalHomologyPreviousIndex_le 0)
    let ℓ₁₂ := stableIntervalLeftMiddle (((0 : ℕ) : ℤ) : EInt)
    let ℓ₃ := stableIntervalRight (((0 : ℕ) : ℤ) : EInt)
    dsimp only [stableIntervalStepToStable,
      stableIntervalCokernelSequence, stableIntervalLeft,
      stableIntervalMiddle, stableIntervalRight,
      stableIntervalLeftMiddle,
      CategoryTheory.Abelian.SpectralObject.cokernelSequenceE]
    have hSource :
        (Y.H η.n₁).obj (mk₁ f₁₂) =
          (Y.H n).obj (mk₁ ℓ₁₂) := by
      simpa only [S0, stableIntervalStep] using hSourceEta.symm
    have hMiddle :
        Y.cycles f₁ f₂ η.n₁ =
          Y.cycles ℓ₁ ℓ₂ n := by
      dsimp only [f₁, f₂, ℓ₁, ℓ₂, n, η,
        PartialTotalFirstPageChoice.pageTransitionIndex,
        stableIntervalLeft, stableIntervalMiddle,
        partialTotalHomologyPreviousIndex]
      (congr 1; omega)
    have hTarget :
        Y.E f₁ f₂ f₃Top η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂ =
          Y.E ℓ₁ ℓ₂ ℓ₃ (n - 1) n (n + 1)
            (by omega) (by omega) := by
      dsimp only [f₁, f₂, f₃Top, ℓ₁, ℓ₂, ℓ₃, n, η,
        PartialTotalFirstPageChoice.pageTransitionIndex,
        stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
        partialTotalHomologyPreviousIndex]
      congr 1 <;> omega
    have hToCycles :
        HEq
          (Y.toCycles f₁ f₂ f₁₂ (by subsingleton) η.n₁)
          (Y.toCycles ℓ₁ ℓ₂ ℓ₁₂
            (stableIntervalLeft_comp_middle
              (partialTotalHomologyPreviousIndex_le 0)) n) := by
      dsimp only [f₁, f₂, f₁₂, ℓ₁, ℓ₂, ℓ₁₂, n, η,
        PartialTotalFirstPageChoice.pageTransitionIndex,
        stableIntervalLeft, stableIntervalMiddle,
        stableIntervalLeftMiddle, partialTotalHomologyPreviousIndex]
      (congr 1; omega)
    have hPiE :
        HEq
          (Y.πE f₁ f₂ f₃Top
            η.n₀ η.n₁ η.n₂ η.hn₁ η.hn₂)
          (Y.πE ℓ₁ ℓ₂ ℓ₃
            (n - 1) n (n + 1) (by omega) (by omega)) := by
      dsimp only [f₁, f₂, f₃Top, ℓ₁, ℓ₂, ℓ₃, n, η,
        PartialTotalFirstPageChoice.pageTransitionIndex,
        stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
        partialTotalHomologyPreviousIndex]
      congr 1 <;> first | subsingleton | omega
    exact CategoryTheory.heq_comp
      hSource hMiddle hTarget hToCycles hPiE
  have hPageStable :
      pageStable = ePageTwo.hom ≫ eLeft.inv ≫ stableTail := by
    exact B.partialTotalZeroColumnPageToStable_eq_pageTwoCoordinate q
  have hPageOneTwo : eP12.hom ≫ ePageTwo.hom =
      (χ.pageOneHomologyCoordinateIso 0 q).hom := by
    exact χ.pageOneTwoIso_zero_hom_comp_pageTwoCoordinateIso_hom q
  have hBridgeCRaw :
      stepP1 ≫ eX.inv ≫ K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫
          eRestr.hom ≫ eP12.hom ≫ pageStable =
        gLiteral := by
    rw [hPageStable]
    rw [reassoc_of% hPageOneTwo]
    rw [reassoc_of% hRawCoordinate]
  have hBridgeCAt :
      (B.verticalHomologyComplex q).pOpcycles 0 ≫
          (ChainComplex.isoHomologyι₀ (B.verticalHomologyComplex q)).inv ≫ eV.inv ≫
          pageStable =
      HomologicalComplex.homologyMap s q ≫ eStepCanonical.inv ≫
          gLiteral := by
    have hComponentInv : eComponent.inv =
        eH.inv ≫ eF.inv ≫ eX.inv := by
      dsimp only [eComponent,
        PartialTotalFirstPageChoice.componentIso, eH, eF, eX, ρ]
      simp only [Nat.add_zero, Iso.trans_inv, Category.assoc]
    rw [reassoc_of% hRepresentative]
    rw [hComponentInv]
    rw [← reassoc_of% hStageZero]
    have hAssoc :
        ((HomologicalComplex.homologyMap s q ≫ eStepCanonical.inv ≫
            stepP1 ≫ eX.inv) ≫ K.pOpcycles 0 ≫
            K.isoHomologyι₀.inv ≫ eRestr.hom ≫ eP12.hom) ≫
            pageStable =
          HomologicalComplex.homologyMap s q ≫ eStepCanonical.inv ≫
            (stepP1 ≫ eX.inv ≫ K.pOpcycles 0 ≫
              K.isoHomologyι₀.inv ≫ eRestr.hom ≫ eP12.hom ≫
              pageStable) := by
      simp only [Category.assoc]
    exact hAssoc.trans (congrArg
      (fun k => HomologicalComplex.homologyMap s q ≫
        eStepCanonical.inv ≫ k) hBridgeCRaw)
  have hGradedZero : B.partialTotalHomologyGradedπ q 0 =
      (B.partialTotalHomologyGradedZeroIso q).hom := by
    dsimp only [partialTotalHomologyGradedZeroIso]
    rfl
  have hF2Canonical :
      B.partialTotalSpectralStepToFiltration q 0 ≫
          (B.partialTotalHomologyFiltration q).ι.app i =
        eStepCanonical.hom ≫
          HomologicalComplex.homologyMap ιStage q := by
    change
      B.partialTotalSpectralStepToFiltration q 0 ≫
          (B.partialTotalHomologyFiltration q).ι.app
            (((0 : ℕ) : ℤ) : EInt) =
        (B.partialTotalSpectralStepHomologyIso q 0).hom ≫
          HomologicalComplex.homologyMap (B.partialTotalι 0) q
    exact B.partialTotalSpectralStepToFiltration_comp_ι q 0
  have hBF2Cancel :
      eStepCanonical.inv ≫ gLiteral ≫
          (B.partialTotalStableGradedIso q 0).hom ≫
          (B.partialTotalHomologyGradedZeroIso q).inv ≫
          (B.partialTotalHomologyFiltration q).ι.app i =
        HomologicalComplex.homologyMap ιStage q := by
    rw [hLiteral]
    rw [← B.partialTotalSpectralStepToFiltration_comp_toStable_assoc q 0]
    rw [B.partialTotalHomologyFiltrationToStable_comp_stableGradedIso_hom_assoc q 0]
    rw [hGradedZero]
    simp only [Iso.hom_inv_id_assoc]
    rw [hF2Canonical]
    exact eStepCanonical.inv_hom_id_assoc _
  have hBridgeZ : s ≫ ιStage = B.partialTotalZeroRowToTotal := by
    simpa only [s, ιStage] using
      B.partialTotalZeroRowToPartialTotal_comp_partialTotalι
  dsimp only [partialTotalZeroColumnEdge]
  let finalTail : Stable0 ⟶ HTotal :=
    (B.partialTotalStableGradedIso q 0).hom ≫
      (B.partialTotalHomologyGradedZeroIso q).inv ≫
      (B.partialTotalHomologyFiltration q).ι.app i
  have hInitial :
      (B.verticalHomologyComplex q).pOpcycles 0 ≫
          (ChainComplex.isoHomologyι₀ (B.verticalHomologyComplex q)).inv ≫ eV.inv ≫
          pageStable ≫ (B.partialTotalStableGradedIso q 0).hom ≫
          (B.partialTotalHomologyGradedZeroIso q).inv ≫
          (B.partialTotalHomologyFiltration q).ι.app i =
        ((B.verticalHomologyComplex q).pOpcycles 0 ≫
          (ChainComplex.isoHomologyι₀ (B.verticalHomologyComplex q)).inv ≫ eV.inv ≫
          pageStable) ≫ finalTail := by
    dsimp only [finalTail]
    simp only [Category.assoc]
  have hBridgeTail :
      ((B.verticalHomologyComplex q).pOpcycles 0 ≫
          (ChainComplex.isoHomologyι₀ (B.verticalHomologyComplex q)).inv ≫ eV.inv ≫
          pageStable) ≫ finalTail =
        ((HomologicalComplex.homologyMap s q ≫ eStepCanonical.inv ≫
          gLiteral) ≫ finalTail :
            (B.verticalHomologyComplex q).X 0 ⟶ HTotal) :=
    congrArg (fun k => k ≫ finalTail) hBridgeCAt
  have hRightCancel :
      ((HomologicalComplex.homologyMap s q ≫ eStepCanonical.inv ≫
          gLiteral) ≫ finalTail :
            (B.verticalHomologyComplex q).X 0 ⟶ HTotal) =
        (HomologicalComplex.homologyMap s q ≫
          HomologicalComplex.homologyMap ιStage q :
            (B.verticalHomologyComplex q).X 0 ⟶ HTotal) := by
    have hRightAssoc :
        ((HomologicalComplex.homologyMap s q ≫ eStepCanonical.inv ≫
            gLiteral) ≫ finalTail :
              (B.verticalHomologyComplex q).X 0 ⟶ HTotal) =
          (HomologicalComplex.homologyMap s q ≫
            (eStepCanonical.inv ≫ gLiteral ≫ finalTail) :
                (B.verticalHomologyComplex q).X 0 ⟶ HTotal) := by
      have hRightAssocRaw :
          (HomologicalComplex.homologyMap s q ≫ eStepCanonical.inv ≫
              gLiteral) ≫ finalTail =
            HomologicalComplex.homologyMap s q ≫
              (eStepCanonical.inv ≫ gLiteral ≫ finalTail) :=
        (Category.assoc (HomologicalComplex.homologyMap s q)
          (eStepCanonical.inv ≫ gLiteral) finalTail).trans
          (congrArg (fun k => HomologicalComplex.homologyMap s q ≫ k)
            (Category.assoc eStepCanonical.inv gLiteral finalTail))
      simpa only [HomologicalComplex₂.verticalHomologyComplex_X] using
        hRightAssocRaw
    have hCancelWhisker :
        (HomologicalComplex.homologyMap s q ≫
            (eStepCanonical.inv ≫ gLiteral ≫ finalTail) :
                (B.verticalHomologyComplex q).X 0 ⟶ HTotal) =
          (HomologicalComplex.homologyMap s q ≫
            HomologicalComplex.homologyMap ιStage q :
              (B.verticalHomologyComplex q).X 0 ⟶ HTotal) :=
      by
        simpa only [finalTail] using congrArg
          (fun k => (HomologicalComplex.homologyMap s q ≫ k :
            (B.verticalHomologyComplex q).X 0 ⟶ HTotal)) hBF2Cancel
    exact hRightAssoc.trans hCancelWhisker
  have hTotal :
      (HomologicalComplex.homologyMap s q ≫
          HomologicalComplex.homologyMap ιStage q :
            (B.verticalHomologyComplex q).X 0 ⟶ HTotal) =
        (HomologicalComplex.homologyMap
          B.partialTotalZeroRowToTotal q :
            (B.verticalHomologyComplex q).X 0 ⟶ HTotal) := by
    have hTotalRaw :
        HomologicalComplex.homologyMap s q ≫
            HomologicalComplex.homologyMap ιStage q =
          HomologicalComplex.homologyMap
            B.partialTotalZeroRowToTotal q := by
      rw [← HomologicalComplex.homologyMap_comp]
      rw [hBridgeZ]
    simpa only [HomologicalComplex₂.verticalHomologyComplex_X] using hTotalRaw
  simpa only [pageStable, i, Int.cast_ofNat_Int] using
    hInitial.trans (hBridgeTail.trans (hRightCancel.trans hTotal))

end HomologicalComplex₂

end
