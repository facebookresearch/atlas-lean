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

public import MathlibExt.Algebra.Homology.PartialTotalConvergence
public import MathlibExt.Algebra.Homology.PartialTotalHasSpectralSequence

/-!
# A finite stable page of the partial-total spectral sequence

Let `B` be a first-quadrant bicomplex in an abelian category. In bidegree `(p, q)`, page `p +
q + 2` is isomorphic to the stable interval object for total homology degree `p + q` and
filtration index `p`.

Write `I_p H_n` for the image of `H_n(B.partialTotal p) ⟶ H_n(B.total (.down ℕ))`, and take
`I_-1 H_n = 0`. The stable-page object is isomorphic to the adjacent quotient `I_p H_(p+q) /
I_(p-1) H_(p+q)`. The filtration-to-page composite agrees with this quotient map. At column
zero the stable coordinate is expressed in total degree `q`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

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


/-- Stage-to-top interval vanishing below its remaining support.

For natural `s` and `k` with `k + 1 ≤ s`, the partial-total spectral-object homology in
cochain degree `-(k + 1)` of the interval `s ⟶ ⊤` is zero. -/
theorem isZero_partialTotalSpectralObjectHObj_stage_to_top
    (s k : ℕ) (hks : k + 1 ≤ s) :
    IsZero ((B.partialTotalSpectralObject.H (-((k + 1 : ℕ) : ℤ))).obj
      (ComposableArrows.mk₁
        (homOfLE (show ((s : ℤ) : EInt) ≤ ⊤ by simp)))) := by
  let Y := B.partialTotalSpectralObject
  let i : EInt := ((s : ℤ) : EInt)
  let f : (⊥ : EInt) ⟶ i := stableIntervalLeftMiddle i
  let g : i ⟶ (⊤ : EInt) := stableIntervalRight i
  let fg : (⊥ : EInt) ⟶ (⊤ : EInt) := stableIntervalFull
  let hfg : f ≫ g = fg := Subsingleton.elim _ _
  let d : ℤ := -((k + 1 : ℕ) : ℤ)
  let d' : ℤ := -(k : ℤ)
  have hdd' : d + 1 = d' := by
    dsimp only [d, d']
    omega
  let m := (Y.H d).map (twoδ₂Toδ₁ f g fg hfg)
  let m' := (Y.H d').map (twoδ₂Toδ₁ f g fg hfg)
  have hArrow : twoδ₂Toδ₁ f g fg hfg =
      B.partialTotalSpectralStepToAbutmentArrow s := by
    apply ComposableArrows.hom_ext₁ <;> subsingleton
  let _ : Epi (HomologicalComplex.homologyMap (B.partialTotalι s) (k + 1)) :=
    B.epi_homologyMap_partialTotalι_of_le s (k + 1) hks
  have hmComp : Epi
      (m ≫ (B.partialTotalSpectralAbutmentHomologyIso (k + 1)).hom) := by
    rw [show m = (Y.H d).map
      (B.partialTotalSpectralStepToAbutmentArrow s) by
        dsimp only [m]
        rw [hArrow]]
    rw [B.partialTotalSpectralStepToAbutment_comp_iso_hom]
    infer_instance
  let _ : Epi m :=
    (epi_comp_iff_of_isIso m
      (B.partialTotalSpectralAbutmentHomologyIso (k + 1)).hom).1 hmComp
  have hklt : k < s := by omega
  let _ : Mono (HomologicalComplex.homologyMap (B.partialTotalι s) k) :=
    B.mono_homologyMap_partialTotalι_of_lt s k hklt
  have hm'Comp : Mono
      (m' ≫ (B.partialTotalSpectralAbutmentHomologyIso k).hom) := by
    rw [show m' = (Y.H d').map
      (B.partialTotalSpectralStepToAbutmentArrow s) by
        dsimp only [m']
        rw [hArrow]]
    rw [B.partialTotalSpectralStepToAbutment_comp_iso_hom]
    infer_instance
  let _ : Mono m' :=
    (mono_comp_iff_of_mono m'
      (B.partialTotalSpectralAbutmentHomologyIso k).hom).1 hm'Comp
  let _ : Epi (Y.sc₂ f g fg hfg d).f := by
    change Epi m
    infer_instance
  have hz : (Y.H d).map (twoδ₁Toδ₀ f g fg hfg) = 0 :=
    (Y.exact₂ f g fg hfg d).epi_f_iff.mp inferInstance
  have hδMono : Mono (Y.δ f g d d' hdd') :=
    (Y.exact₃ f g fg hfg d d' hdd').mono_g hz
  let _ : Mono (Y.δ f g d d' hdd') := hδMono
  have hδZero : Y.δ f g d d' hdd' = 0 := by
    rw [← cancel_mono m']
    simpa only [zero_comp] using Y.zero₁ f g fg hfg d d' hdd'
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (Y.δ f g d d' hdd'),
    hδZero, Category.id_comp, zero_comp]

/-- Page at total degree plus two as a stable interval object.

For natural `p` and `q`, the spectral-sequence object at `(p, q)` on page `p + q + 2` is
isomorphic to `B.partialTotalStableObj (p + q) p`. First-quadrant vanishing removes the two
outer intervals in this page coordinate. -/
noncomputable def partialTotalStablePageIso (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
        (((p + q + 2 : ℕ) : ℤ))).X (p, q) ≅
      B.partialTotalStableObj (p + q) p := by
  let Y := B.partialTotalSpectralObject
  let n : ℕ := q + p
  let r : ℤ := (((p + q + 2 : ℕ) : ℤ))
  let i₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
  let i₁ : EInt := partialTotalHomologyPreviousIndex p
  let i₂ : EInt := ((p : ℤ) : EInt)
  let i₃ : EInt := (((2 * p + q + 1 : ℕ) : ℤ) : EInt)
  let n₀ : ℤ := -((n + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -(n : ℤ)
  let n₂ : ℤ := -(n : ℤ) + 1
  have hr : (1 : ℤ) ≤ r := by
    dsimp only [r]
    omega
  have h₀ : i₀ = (core).i₀ r (p, q) hr := by
    change i₀ = (((p : ℤ) - r : ℤ) : EInt)
    dsimp only [i₀, r]
    congr 1
    omega
  have h₁ : i₁ = (core).i₁ (p, q) := by
    change i₁ = (((p : ℤ) - 1 : ℤ) : EInt)
    dsimp only [i₁]
    rcases p with _ | p
    · rfl
    · change ((p : ℤ) : EInt) =
        ((((p + 1 : ℕ) : ℤ) - 1 : ℤ) : EInt)
      congr 1
      omega
  have h₂ : i₂ = (core).i₂ (p, q) := rfl
  have h₃ : i₃ = (core).i₃ r (p, q) hr := by
    change i₃ = (((p : ℤ) + r - 1 : ℤ) : EInt)
    dsimp only [i₃, r]
    congr 1
    omega
  have hn : n₁ = (core).deg (p, q) := by
    change n₁ = -(p : ℤ) - (q : ℤ)
    dsimp only [n₁, n]
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
  have hLeft : IsZero ((Y.H n₂).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ i₀ by simp)))) := by
    let h := B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      n₂ (-(q : ℤ) - 2) (by omega)
    exact h
  have hRight : IsZero ((Y.H n₀).obj
      (mk₁ (homOfLE (show i₃ ≤ (⊤ : EInt) by simp)))) := by
    let h := B.isZero_partialTotalSpectralObjectHObj_stage_to_top
      (2 * p + q + 1) n (by omega)
    exact h
  have hiBot₁ : (⊥ : EInt) ≤ i₁ := by simp
  have hi₃Top : i₃ ≤ (⊤ : EInt) := by simp
  let ePage := Y.spectralSequencePageXIso core r hr (p, q)
    i₀ i₁ i₂ i₃ h₀ h₁ h₂ h₃ n₀ n₁ n₂ hn
      (hn₁ := hn₁) (hn₂ := hn₂)
  let eLeft := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) i₀ i₁ i₂ i₃ (by simp) hi₀₁ hi₁₂ hi₂₃
      n₀ n₁ n₂ hLeft (hn₁ := hn₁) (hn₂ := hn₂)
  let eRight := Y.isoMapFourδ₄Toδ₃'
    (⊥ : EInt) i₁ i₂ i₃ ⊤ hiBot₁ hi₁₂ hi₂₃ hi₃Top
      n₀ n₁ n₂ hRight (hn₁ := hn₁) (hn₂ := hn₂)
  let e := ePage ≪≫ eLeft.symm ≪≫ eRight
  have hTarget :
      Y.E (homOfLE hiBot₁) (homOfLE hi₁₂)
          (homOfLE (hi₂₃.trans hi₃Top)) n₀ n₁ n₂ hn₁ hn₂ =
        B.partialTotalStableObj (p + q) p := by
    dsimp only [partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      n₀, n₁, n₂, n]
    congr 1
    all_goals omega
  exact e ≪≫ eqToIso hTarget

/-- Stable page as the adjacent image-filtration quotient.

The object at `(p, q)` on page `p + q + 2` is isomorphic to `B.partialTotalHomologyGradedPiece
(p + q) p`, the quotient of the stage-`p` image in total homology by the preceding image. This
is the stable-interval isomorphism followed by its graded-quotient isomorphism. -/
noncomputable def partialTotalStablePageGradedIso (p q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
        (((p + q + 2 : ℕ) : ℤ))).X (p, q) ≅
      B.partialTotalHomologyGradedPiece (p + q) p :=
  B.partialTotalStablePageIso p q ≪≫
    B.partialTotalStableGradedIso (p + q) p

/-- Filtration-to-stable-page map agrees with the graded quotient.

Map the stage-`p` image in total degree `p + q` to the stable interval, then to page `p + q +
2`, and then through the page grading isomorphism. The composite is
`B.partialTotalHomologyGradedπ (p + q) p`. -/
@[reassoc]
theorem partialTotalHomologyFiltrationToStablePage_comp_gradingIso_hom
    (p q : ℕ) :
    (B.partialTotalHomologyFiltrationToStable (p + q) p ≫
        (B.partialTotalStablePageIso p q).inv) ≫
      (B.partialTotalStablePageGradedIso p q).hom =
    B.partialTotalHomologyGradedπ (p + q) p := by
  simp only [partialTotalStablePageGradedIso, Iso.trans_hom,
    Category.assoc, Iso.inv_hom_id_assoc,
    B.partialTotalHomologyFiltrationToStable_comp_stableGradedIso_hom]

/-- Zero-column stable-page map in total degree q.

For natural `q`, this morphism sends the page-`q + 2` object at `(0, q)` to
`B.partialTotalStableObj q 0`. It uses the stable spectral interval with lower outer cut `-(q
+ 2)`, middle cuts `-1` and `0`, and upper outer cut `q + 1`. -/
noncomputable def partialTotalStablePageZeroColumnHom (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
      (((0 + q + 2 : ℕ) : ℤ))).X (0, q) ⟶
      B.partialTotalStableObj q 0 := by
  let Y := B.partialTotalSpectralObject
  let rD : ℤ := ((2 + q : ℕ) : ℤ)
  let rS : ℤ := ((0 + q + 2 : ℕ) : ℤ)
  have hrS : (1 : ℤ) ≤ rS := by
    dsimp only [rS]
    omega
  let i₀ : EInt := (((0 : ℤ) - rD : ℤ) : EInt)
  let i₁ : EInt := partialTotalHomologyPreviousIndex 0
  let i₂ : EInt := ((0 : ℤ) : EInt)
  let i₃ : EInt := (((0 : ℤ) + rD - 1 : ℤ) : EInt)
  let n₀ : ℤ := -(0 : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(0 : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(0 : ℤ) - (q : ℤ) + 1
  have hn : n₁ = (core).deg (0, q) := by
    exact
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg
        (0, q)).symm
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  have hi₀ : i₀ = (core).i₀ rS (0, q) hrS := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
    dsimp only [i₀, rD, rS]
    congr 1
    omega
  have hi₁ : i₁ = (core).i₁ (0, q) := by
    change i₁ = (((0 : ℤ) - 1 : ℤ) : EInt)
    dsimp only [i₁, partialTotalHomologyPreviousIndex]
    rfl
  have hi₂ : i₂ = (core).i₂ (0, q) := rfl
  have hi₃ : i₃ = (core).i₃ rS (0, q) hrS := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
    dsimp only [i₃, rD, rS]
    congr 1
    omega
  have hi₀neg : i₀ = ((-rD : ℤ) : EInt) := by
    dsimp only [i₀]
    congr 1
    omega
  have hi₀₁ : i₀ ≤ i₁ := by
    dsimp only [i₀, i₁, rD, partialTotalHomologyPreviousIndex]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₁₂ : i₁ ≤ i₂ := partialTotalHomologyPreviousIndex_le 0
  have hi₂₃ : i₂ ≤ i₃ := by
    dsimp only [i₂, i₃, rD]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hiBot₁ : (⊥ : EInt) ≤ i₁ := by simp
  have hi₃Top : i₃ ≤ (⊤ : EInt) := by simp
  have hLeft : IsZero ((Y.H n₂).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ i₀ by simp)))) := by
    let h := B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      n₂ (0 - rD : ℤ) (by
        dsimp only [rD]
        omega)
    exact h
  let ePage := Y.spectralSequencePageXIso core rS hrS (0, q)
    i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn
      (hn₁ := hn₁) (hn₂ := hn₂)
  let eLeft := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) i₀ i₁ i₂ i₃ (by simp) hi₀₁ hi₁₂ hi₂₃
      n₀ n₁ n₂ hLeft (hn₁ := hn₁) (hn₂ := hn₂)
  let rightOuterMap := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) i₁ i₂ i₃ ⊤ hiBot₁ hi₁₂ hi₂₃ hi₃Top
      n₀ n₁ n₂ hn₁ hn₂
  have hTarget :
      Y.E (homOfLE hiBot₁) (homOfLE hi₁₂)
          (homOfLE (hi₂₃.trans hi₃Top)) n₀ n₁ n₂ hn₁ hn₂ =
        B.partialTotalStableObj q 0 := by
    dsimp only [partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      n₀, n₁, n₂]
    congr 1
    all_goals omega
  exact ePage.hom ≫ eLeft.inv ≫ rightOuterMap ≫
    (eqToIso hTarget).hom

private structure StablePageZeroComparisonData (q : ℕ) where
  I : Type
  so : I
  sa : I
  hsa : so = sa
  X₁ : I → C
  X₂ : I → C
  X₃ : I → C
  pageF : ∀ x : I,
    ((B.partialTotalSpectralObject.spectralSequence core).page
      (((0 + q + 2 : ℕ) : ℤ))).X (0, q) ≅ X₁ x
  leftF : ∀ x : I, X₂ x ≅ X₁ x
  rightF : ∀ x : I, X₂ x ⟶ X₃ x
  hoTarget : X₃ so = B.partialTotalStableObj (0 + q) 0
  haTarget : X₃ sa = B.partialTotalStableObj q 0
  hFinal : B.partialTotalStableObj (0 + q) 0 =
    B.partialTotalStableObj q 0

private noncomputable def stablePageZeroComparisonData (q : ℕ) :
    StablePageZeroComparisonData B q := by
  let Y := B.partialTotalSpectralObject
  let rD : ℤ := ((2 + q : ℕ) : ℤ)
  let rS : ℤ := ((0 + q + 2 : ℕ) : ℤ)
  have hrS : (1 : ℤ) ≤ rS := by
    dsimp only [rS]
    omega
  let i₁ : EInt := partialTotalHomologyPreviousIndex 0
  let i₂ : EInt := ((0 : ℤ) : EInt)
  have hi₁ : i₁ = (core).i₁ (0, q) := by
    change i₁ = (((0 : ℤ) - 1 : ℤ) : EInt)
    dsimp only [i₁, partialTotalHomologyPreviousIndex]
    rfl
  have hi₂ : i₂ = (core).i₂ (0, q) := rfl
  have hi₁₂ : i₁ ≤ i₂ := partialTotalHomologyPreviousIndex_le 0
  have hiBot₁ : (⊥ : EInt) ≤ i₁ := by simp
  let oi₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
  let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
  let on : ℕ := q + 0
  let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
  let on₁ : ℤ := -(on : ℤ)
  let on₂ : ℤ := -(on : ℤ) + 1
  let ai₀ : EInt := (((0 : ℤ) - rD : ℤ) : EInt)
  let ai₃ : EInt := (((0 : ℤ) + rD - 1 : ℤ) : EInt)
  let an₀ : ℤ := -(0 : ℤ) - (q : ℤ) - 1
  let an₁ : ℤ := -(0 : ℤ) - (q : ℤ)
  let an₂ : ℤ := -(0 : ℤ) - (q : ℤ) + 1
  let Packet := (EInt × EInt) × (ℤ × ℤ × ℤ)
  let ownerPacket : Packet := ((oi₀, oi₃), (on₀, on₁, on₂))
  let alignedPacket : Packet := ((ai₀, ai₃), (an₀, an₁, an₂))
  have hPacket : ownerPacket = alignedPacket := by
    apply Prod.ext
    · apply Prod.ext
      · dsimp only [ownerPacket, alignedPacket, oi₀, ai₀, rD]
        congr 1
        omega
      · dsimp only [ownerPacket, alignedPacket, oi₃, ai₃, rD]
        congr 1
        omega
    · apply Prod.ext
      · dsimp only [ownerPacket, alignedPacket, on₀, an₀, on]
        omega
      · apply Prod.ext
        · dsimp only [ownerPacket, alignedPacket, on₁, an₁, on]
          omega
        · dsimp only [ownerPacket, alignedPacket, on₂, an₂, on]
          omega
  let I := {x : Packet // x = alignedPacket}
  let so : I := ⟨ownerPacket, hPacket⟩
  let sa : I := ⟨alignedPacket, rfl⟩
  have hsa : so = sa := by
    apply Subtype.ext
    exact hPacket
  let xi₀ (x : I) : EInt := x.1.1.1
  let xi₃ (x : I) : EInt := x.1.1.2
  let xn₀ (x : I) : ℤ := x.1.2.1
  let xn₁ (x : I) : ℤ := x.1.2.2.1
  let xn₂ (x : I) : ℤ := x.1.2.2.2
  have hn (x : I) : xn₁ x = (core).deg (0, q) := by
    dsimp only [xn₁]
    rw [x.2]
    exact
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg
        (0, q)).symm
  have hn₁ (x : I) : xn₀ x + 1 = xn₁ x := by
    dsimp only [xn₀, xn₁]
    rw [x.2]
    dsimp only [alignedPacket, an₀, an₁]
    omega
  have hn₂ (x : I) : xn₁ x + 1 = xn₂ x := by
    dsimp only [xn₁, xn₂]
    rw [x.2]
  have hi₀₁ (x : I) : xi₀ x ≤ i₁ := by
    dsimp only [xi₀]
    rw [x.2]
    dsimp only [alignedPacket, ai₀, i₁, rD,
      partialTotalHomologyPreviousIndex]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₂₃ (x : I) : i₂ ≤ xi₃ x := by
    dsimp only [xi₃]
    rw [x.2]
    dsimp only [alignedPacket, ai₃, i₂, rD]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₃Top (x : I) : xi₃ x ≤ (⊤ : EInt) := by simp
  let X₁ (x : I) := Y.E
    (homOfLE (hi₀₁ x)) (homOfLE hi₁₂) (homOfLE (hi₂₃ x))
    (xn₀ x) (xn₁ x) (xn₂ x) (hn₁ x) (hn₂ x)
  let X₂ (x : I) := Y.E
    (homOfLE hiBot₁) (homOfLE hi₁₂) (homOfLE (hi₂₃ x))
    (xn₀ x) (xn₁ x) (xn₂ x) (hn₁ x) (hn₂ x)
  let X₃ (x : I) := Y.E
    (homOfLE hiBot₁) (homOfLE hi₁₂)
      (homOfLE ((hi₂₃ x).trans (hi₃Top x)))
    (xn₀ x) (xn₁ x) (xn₂ x) (hn₁ x) (hn₂ x)
  let pageF (x : I) :
      ((Y.spectralSequence core).page rS hrS).X (0, q) ≅ X₁ x := by
    have h₀ : xi₀ x = (core).i₀ rS (0, q) hrS := by
      dsimp only [xi₀]
      rw [x.2]
      rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
      dsimp only [alignedPacket, ai₀, rD, rS]
      congr 1
      omega
    have h₃ : xi₃ x = (core).i₃ rS (0, q) hrS := by
      dsimp only [xi₃]
      rw [x.2]
      rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
      dsimp only [alignedPacket, ai₃, rD, rS]
      congr 1
      omega
    exact Y.spectralSequencePageXIso core rS hrS (0, q)
      (xi₀ x) i₁ i₂ (xi₃ x) h₀ hi₁ hi₂ h₃
        (xn₀ x) (xn₁ x) (xn₂ x) (hn x)
        (hn₁ := hn₁ x) (hn₂ := hn₂ x)
  let leftF (x : I) : X₂ x ≅ X₁ x := by
    have hLeft : IsZero ((Y.H (xn₂ x)).obj
        (mk₁ (homOfLE (show (⊥ : EInt) ≤ xi₀ x by simp)))) := by
      have hneg : xi₀ x = ((-rD : ℤ) : EInt) := by
        dsimp only [xi₀]
        rw [x.2]
        dsimp only [alignedPacket, ai₀]
        congr 1
        omega
      rw [hneg]
      exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
        (xn₂ x) (-rD) (by dsimp only [rD]; omega)
    exact Y.isoMapFourδ₁Toδ₀'
      (⊥ : EInt) (xi₀ x) i₁ i₂ (xi₃ x) (by simp)
      (hi₀₁ x) hi₁₂ (hi₂₃ x) (xn₀ x) (xn₁ x) (xn₂ x) hLeft
        (hn₁ := hn₁ x) (hn₂ := hn₂ x)
  let rightF (x : I) : X₂ x ⟶ X₃ x :=
    Y.mapFourδ₄Toδ₃'
      (⊥ : EInt) i₁ i₂ (xi₃ x) ⊤ hiBot₁ hi₁₂ (hi₂₃ x)
      (hi₃Top x) (xn₀ x) (xn₁ x) (xn₂ x) (hn₁ x) (hn₂ x)
  have hoTarget : X₃ so = B.partialTotalStableObj (0 + q) 0 := by
    dsimp only [X₃, so, partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      xi₃, xn₀, xn₁, xn₂, ownerPacket, on₀, on₁, on₂]
    congr 1
    all_goals omega
  have haTarget : X₃ sa = B.partialTotalStableObj q 0 := by
    dsimp only [X₃, sa, partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      xi₃, xn₀, xn₁, xn₂, alignedPacket, an₀, an₁, an₂]
    congr 1
    all_goals omega
  exact
    { I := I
      so := so
      sa := sa
      hsa := hsa
      X₁ := X₁
      X₂ := X₂
      X₃ := X₃
      pageF := pageF
      leftF := leftF
      rightF := rightF
      hoTarget := hoTarget
      haTarget := haTarget
      hFinal := congrArg (fun m => B.partialTotalStableObj m 0)
        (Nat.zero_add q) }

private noncomputable def StablePageZeroComparisonData.ownerHom
    {q : ℕ} (D : StablePageZeroComparisonData B q) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
      (((0 + q + 2 : ℕ) : ℤ))).X (0, q) ⟶
      B.partialTotalStableObj q 0 :=
  (D.pageF D.so).hom ≫ (D.leftF D.so).inv ≫ D.rightF D.so ≫
    eqToHom D.hoTarget ≫ eqToHom D.hFinal

private noncomputable def StablePageZeroComparisonData.alignedHom
    {q : ℕ} (D : StablePageZeroComparisonData B q) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
      (((0 + q + 2 : ℕ) : ℤ))).X (0, q) ⟶
      B.partialTotalStableObj q 0 :=
  (D.pageF D.sa).hom ≫ (D.leftF D.sa).inv ≫ D.rightF D.sa ≫
    eqToHom D.haTarget

private theorem StablePageZeroComparisonData.page_naturality
    {q : ℕ} (D : StablePageZeroComparisonData B q) :
    (D.pageF D.so).hom ≫ eqToHom (congrArg D.X₁ D.hsa) =
      (D.pageF D.sa).hom := by
  have h := CategoryTheory.eqToHom_iso_hom_naturality D.pageF D.hsa
  simpa only [eqToHom_refl, Category.id_comp] using h

private theorem StablePageZeroComparisonData.left_naturality
    {q : ℕ} (D : StablePageZeroComparisonData B q) :
    (D.leftF D.so).inv ≫ eqToHom (congrArg D.X₂ D.hsa) =
      eqToHom (congrArg D.X₁ D.hsa) ≫ (D.leftF D.sa).inv := by
  exact CategoryTheory.eqToHom_iso_inv_naturality D.leftF D.hsa

private theorem StablePageZeroComparisonData.right_naturality
    {q : ℕ} (D : StablePageZeroComparisonData B q) :
    D.rightF D.so ≫ eqToHom (congrArg D.X₃ D.hsa) =
      eqToHom (congrArg D.X₂ D.hsa) ≫ D.rightF D.sa := by
  exact CategoryTheory.eqToHom_naturality D.rightF D.hsa

private theorem StablePageZeroComparisonData.target_naturality
    {q : ℕ} (D : StablePageZeroComparisonData B q) :
    eqToHom D.hoTarget ≫ eqToHom D.hFinal =
      eqToHom (congrArg D.X₃ D.hsa) ≫ eqToHom D.haTarget := by
  simp only [CategoryTheory.eqToHom_trans]

private theorem StablePageZeroComparisonData.ownerHom_eq_alignedHom
    {q : ℕ} (D : StablePageZeroComparisonData B q) :
    D.ownerHom = D.alignedHom := by
  unfold ownerHom alignedHom
  slice_lhs 4 5 => rw [D.target_naturality]
  slice_lhs 3 4 => rw [D.right_naturality]
  slice_lhs 2 3 => rw [D.left_naturality]
  slice_lhs 1 2 => rw [D.page_naturality]
  simp only [Category.assoc]

private noncomputable def stablePageZeroOwnerFactorHom (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
      (((0 + q + 2 : ℕ) : ℤ))).X (0, q) ⟶
      B.partialTotalStableObj q 0 := by
  let Y := B.partialTotalSpectralObject
  let on : ℕ := q + 0
  let or : ℤ := ((0 + q + 2 : ℕ) : ℤ)
  let oi₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
  let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
  let oi₂ : EInt := ((0 : ℤ) : EInt)
  let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
  let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
  let on₁ : ℤ := -(on : ℤ)
  let on₂ : ℤ := -(on : ℤ) + 1
  have ohr : (1 : ℤ) ≤ or := by
    dsimp only [or]
    omega
  have ohi₀ : oi₀ = (core).i₀ or (0, q) ohr := by
    change oi₀ = (((0 : ℤ) - or : ℤ) : EInt)
    dsimp only [oi₀, or]
    congr 1
    omega
  have ohi₁ : oi₁ = (core).i₁ (0, q) := by
    change oi₁ = (((0 : ℤ) - 1 : ℤ) : EInt)
    dsimp only [oi₁, partialTotalHomologyPreviousIndex]
    rfl
  have ohi₂ : oi₂ = (core).i₂ (0, q) := rfl
  have ohi₃ : oi₃ = (core).i₃ or (0, q) ohr := by
    change oi₃ = (((0 : ℤ) + or - 1 : ℤ) : EInt)
    dsimp only [oi₃, or]
    congr 1
    omega
  have ohn : on₁ = (core).deg (0, q) := by
    change on₁ = -(0 : ℤ) - (q : ℤ)
    dsimp only [on₁, on]
    omega
  have ohn₁ : on₀ + 1 = on₁ := by
    dsimp only [on₀, on₁, on]
    omega
  have ohn₂ : on₁ + 1 = on₂ := by
    dsimp only [on₁, on₂]
  have ohi₀₁ : oi₀ ≤ oi₁ := by
    dsimp only [oi₀, oi₁, partialTotalHomologyPreviousIndex]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
  have ohi₂₃ : oi₂ ≤ oi₃ := by
    dsimp only [oi₂, oi₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohiBot₁ : (⊥ : EInt) ≤ oi₁ := by simp
  have ohi₃Top : oi₃ ≤ (⊤ : EInt) := by simp
  have ohLeft : IsZero ((Y.H on₂).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ oi₀ by simp)))) := by
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      on₂ (-(q : ℤ) - 2) (by omega)
  have ohRight : IsZero ((Y.H on₀).obj
      (mk₁ (homOfLE (show oi₃ ≤ (⊤ : EInt) by simp)))) := by
    exact B.isZero_partialTotalSpectralObjectHObj_stage_to_top
      (q + 1) on (by omega)
  let oPage := Y.spectralSequencePageXIso core or ohr (0, q)
    oi₀ oi₁ oi₂ oi₃ ohi₀ ohi₁ ohi₂ ohi₃ on₀ on₁ on₂ ohn
      (hn₁ := ohn₁) (hn₂ := ohn₂)
  let oLeft := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) oi₀ oi₁ oi₂ oi₃ (by simp) ohi₀₁ ohi₁₂ ohi₂₃
      on₀ on₁ on₂ ohLeft (hn₁ := ohn₁) (hn₂ := ohn₂)
  let oRight := Y.isoMapFourδ₄Toδ₃'
    (⊥ : EInt) oi₁ oi₂ oi₃ ⊤ ohiBot₁ ohi₁₂ ohi₂₃ ohi₃Top
      on₀ on₁ on₂ ohRight (hn₁ := ohn₁) (hn₂ := ohn₂)
  let oRightMap := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) oi₁ oi₂ oi₃ ⊤ ohiBot₁ ohi₁₂ ohi₂₃ ohi₃Top
      on₀ on₁ on₂ ohn₁ ohn₂
  have hoRight : oRight.hom = oRightMap := rfl
  have ohTarget :
      Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂)
          (homOfLE (ohi₂₃.trans ohi₃Top)) on₀ on₁ on₂ ohn₁ ohn₂ =
        B.partialTotalStableObj (0 + q) 0 := by
    dsimp only [partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      on₀, on₁, on₂, on]
    congr 1
    all_goals omega
  let oTarget :
      Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂)
          (homOfLE (ohi₂₃.trans ohi₃Top)) on₀ on₁ on₂ ohn₁ ohn₂ ≅
        B.partialTotalStableObj (0 + q) 0 :=
    eqToIso ohTarget
  let finalEq : B.partialTotalStableObj (0 + q) 0 ≅
      B.partialTotalStableObj q 0 :=
    eqToIso (congrArg (fun m => B.partialTotalStableObj m 0)
      (Nat.zero_add q))
  exact oPage.hom ≫ oLeft.inv ≫ oRight.hom ≫
    oTarget.hom ≫ finalEq.hom

private noncomputable def stablePageZeroAlignedFactorHom (q : ℕ) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
      (((0 + q + 2 : ℕ) : ℤ))).X (0, q) ⟶
      B.partialTotalStableObj q 0 := by
  let Y := B.partialTotalSpectralObject
  let rD : ℤ := ((2 + q : ℕ) : ℤ)
  let rS : ℤ := ((0 + q + 2 : ℕ) : ℤ)
  have hrS : (1 : ℤ) ≤ rS := by
    dsimp only [rS]
    omega
  let i₀ : EInt := (((0 : ℤ) - rD : ℤ) : EInt)
  let i₁ : EInt := partialTotalHomologyPreviousIndex 0
  let i₂ : EInt := ((0 : ℤ) : EInt)
  let i₃ : EInt := (((0 : ℤ) + rD - 1 : ℤ) : EInt)
  let n₀ : ℤ := -(0 : ℤ) - (q : ℤ) - 1
  let n₁ : ℤ := -(0 : ℤ) - (q : ℤ)
  let n₂ : ℤ := -(0 : ℤ) - (q : ℤ) + 1
  have hn : n₁ = (core).deg (0, q) := by
    exact
      (CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg
        (0, q)).symm
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  have hi₀ : i₀ = (core).i₀ rS (0, q) hrS := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
    dsimp only [i₀, rD, rS]
    congr 1
    omega
  have hi₁ : i₁ = (core).i₁ (0, q) := by
    change i₁ = (((0 : ℤ) - 1 : ℤ) : EInt)
    dsimp only [i₁, partialTotalHomologyPreviousIndex]
    rfl
  have hi₂ : i₂ = (core).i₂ (0, q) := rfl
  have hi₃ : i₃ = (core).i₃ rS (0, q) hrS := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
    dsimp only [i₃, rD, rS]
    congr 1
    omega
  have hi₀neg : i₀ = ((-rD : ℤ) : EInt) := by
    dsimp only [i₀]
    congr 1
    omega
  have hi₀₁ : i₀ ≤ i₁ := by
    dsimp only [i₀, i₁, rD, partialTotalHomologyPreviousIndex]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₁₂ : i₁ ≤ i₂ := partialTotalHomologyPreviousIndex_le 0
  have hi₂₃ : i₂ ≤ i₃ := by
    dsimp only [i₂, i₃, rD]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hiBot₁ : (⊥ : EInt) ≤ i₁ := by simp
  have hi₃Top : i₃ ≤ (⊤ : EInt) := by simp
  have hLeft : IsZero ((Y.H n₂).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ i₀ by simp)))) := by
    rw [hi₀neg]
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      n₂ (-rD) (by dsimp only [rD]; omega)
  let ePage := Y.spectralSequencePageXIso core rS hrS (0, q)
    i₀ i₁ i₂ i₃ hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn
      (hn₁ := hn₁) (hn₂ := hn₂)
  let eLeft := Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) i₀ i₁ i₂ i₃ (by simp) hi₀₁ hi₁₂ hi₂₃
      n₀ n₁ n₂ hLeft (hn₁ := hn₁) (hn₂ := hn₂)
  let rightOuterMap := Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) i₁ i₂ i₃ ⊤ hiBot₁ hi₁₂ hi₂₃ hi₃Top
      n₀ n₁ n₂ hn₁ hn₂
  have hTarget :
      Y.E (homOfLE hiBot₁) (homOfLE hi₁₂)
          (homOfLE (hi₂₃.trans hi₃Top)) n₀ n₁ n₂ hn₁ hn₂ =
        B.partialTotalStableObj q 0 := by
    dsimp only [partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      n₀, n₁, n₂]
    congr 1
    all_goals omega
  exact ePage.hom ≫ eLeft.inv ≫ rightOuterMap ≫
    (eqToIso hTarget).hom

private noncomputable def PPage (q : ℕ) :
    let Y := B.partialTotalSpectralObject
    let on : ℕ := q + 0
    let or : ℤ := ((0 + q + 2 : ℕ) : ℤ)
    let oi₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
    let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
    let oi₂ : EInt := ((0 : ℤ) : EInt)
    let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
    let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
    let on₁ : ℤ := -(on : ℤ)
    let on₂ : ℤ := -(on : ℤ) + 1
    let ohr : (1 : ℤ) ≤ or := by
      dsimp only [or]
      omega
    let ohi₀₁ : oi₀ ≤ oi₁ := by
      dsimp only [oi₀, oi₁, partialTotalHomologyPreviousIndex]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
    let ohi₂₃ : oi₂ ≤ oi₃ := by
      dsimp only [oi₂, oi₃]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohn₁ : on₀ + 1 = on₁ := by
      dsimp only [on₀, on₁, on]
      omega
    let ohn₂ : on₁ + 1 = on₂ := by
      dsimp only [on₁, on₂]
    ((Y.spectralSequence core).page or ohr).X (0, q) ⟶
      Y.E (homOfLE ohi₀₁) (homOfLE ohi₁₂) (homOfLE ohi₂₃)
        on₀ on₁ on₂ ohn₁ ohn₂ := by
  dsimp only
  let Y := B.partialTotalSpectralObject
  let on : ℕ := q + 0
  let or : ℤ := ((0 + q + 2 : ℕ) : ℤ)
  let oi₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
  let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
  let oi₂ : EInt := ((0 : ℤ) : EInt)
  let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
  let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
  let on₁ : ℤ := -(on : ℤ)
  let on₂ : ℤ := -(on : ℤ) + 1
  have ohr : (1 : ℤ) ≤ or := by
    dsimp only [or]
    omega
  have ohi₀ : oi₀ = (core).i₀ or (0, q) ohr := by
    change oi₀ = (((0 : ℤ) - or : ℤ) : EInt)
    dsimp only [oi₀, or]
    congr 1
    omega
  have ohi₁ : oi₁ = (core).i₁ (0, q) := by
    change oi₁ = (((0 : ℤ) - 1 : ℤ) : EInt)
    dsimp only [oi₁, partialTotalHomologyPreviousIndex]
    rfl
  have ohi₂ : oi₂ = (core).i₂ (0, q) := rfl
  have ohi₃ : oi₃ = (core).i₃ or (0, q) ohr := by
    change oi₃ = (((0 : ℤ) + or - 1 : ℤ) : EInt)
    dsimp only [oi₃, or]
    congr 1
    omega
  have ohn : on₁ = (core).deg (0, q) := by
    change on₁ = -(0 : ℤ) - (q : ℤ)
    dsimp only [on₁, on]
    omega
  have ohn₁ : on₀ + 1 = on₁ := by
    dsimp only [on₀, on₁, on]
    omega
  have ohn₂ : on₁ + 1 = on₂ := by
    dsimp only [on₁, on₂]
  have ohi₀₁ : oi₀ ≤ oi₁ := by
    dsimp only [oi₀, oi₁, partialTotalHomologyPreviousIndex]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
  have ohi₂₃ : oi₂ ≤ oi₃ := by
    dsimp only [oi₂, oi₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  exact (Y.spectralSequencePageXIso core or ohr (0, q)
    oi₀ oi₁ oi₂ oi₃ ohi₀ ohi₁ ohi₂ ohi₃ on₀ on₁ on₂ ohn
      (hn₁ := ohn₁) (hn₂ := ohn₂)).hom

private noncomputable def PLeft (q : ℕ) :
    let Y := B.partialTotalSpectralObject
    let on : ℕ := q + 0
    let oi₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
    let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
    let oi₂ : EInt := ((0 : ℤ) : EInt)
    let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
    let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
    let on₁ : ℤ := -(on : ℤ)
    let on₂ : ℤ := -(on : ℤ) + 1
    let ohi₀₁ : oi₀ ≤ oi₁ := by
      dsimp only [oi₀, oi₁, partialTotalHomologyPreviousIndex]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
    let ohi₂₃ : oi₂ ≤ oi₃ := by
      dsimp only [oi₂, oi₃]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohiBot₁ : (⊥ : EInt) ≤ oi₁ := by simp
    let ohn₁ : on₀ + 1 = on₁ := by
      dsimp only [on₀, on₁, on]
      omega
    let ohn₂ : on₁ + 1 = on₂ := by
      dsimp only [on₁, on₂]
    Y.E (homOfLE ohi₀₁) (homOfLE ohi₁₂) (homOfLE ohi₂₃)
        on₀ on₁ on₂ ohn₁ ohn₂ ⟶
      Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂) (homOfLE ohi₂₃)
        on₀ on₁ on₂ ohn₁ ohn₂ := by
  dsimp only
  let Y := B.partialTotalSpectralObject
  let on : ℕ := q + 0
  let oi₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
  let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
  let oi₂ : EInt := ((0 : ℤ) : EInt)
  let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
  let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
  let on₁ : ℤ := -(on : ℤ)
  let on₂ : ℤ := -(on : ℤ) + 1
  have ohi₀₁ : oi₀ ≤ oi₁ := by
    dsimp only [oi₀, oi₁, partialTotalHomologyPreviousIndex]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
  have ohi₂₃ : oi₂ ≤ oi₃ := by
    dsimp only [oi₂, oi₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohiBot₀ : (⊥ : EInt) ≤ oi₀ := by simp
  have ohn₁ : on₀ + 1 = on₁ := by
    dsimp only [on₀, on₁, on]
    omega
  have ohn₂ : on₁ + 1 = on₂ := by
    dsimp only [on₁, on₂]
  have ohLeft : IsZero ((Y.H on₂).obj
      (mk₁ (homOfLE ohiBot₀))) := by
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      on₂ (-(q : ℤ) - 2) (by omega)
  exact (Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) oi₀ oi₁ oi₂ oi₃ ohiBot₀ ohi₀₁ ohi₁₂ ohi₂₃
      on₀ on₁ on₂ ohLeft (hn₁ := ohn₁) (hn₂ := ohn₂)).inv

private noncomputable def PRight (q : ℕ) :
    let Y := B.partialTotalSpectralObject
    let on : ℕ := q + 0
    let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
    let oi₂ : EInt := ((0 : ℤ) : EInt)
    let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
    let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
    let on₁ : ℤ := -(on : ℤ)
    let on₂ : ℤ := -(on : ℤ) + 1
    let ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
    let ohi₂₃ : oi₂ ≤ oi₃ := by
      dsimp only [oi₂, oi₃]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohiBot₁ : (⊥ : EInt) ≤ oi₁ := by simp
    let ohi₃Top : oi₃ ≤ (⊤ : EInt) := by simp
    let ohn₁ : on₀ + 1 = on₁ := by
      dsimp only [on₀, on₁, on]
      omega
    let ohn₂ : on₁ + 1 = on₂ := by
      dsimp only [on₁, on₂]
    Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂) (homOfLE ohi₂₃)
        on₀ on₁ on₂ ohn₁ ohn₂ ⟶
      Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂)
        (homOfLE (ohi₂₃.trans ohi₃Top))
        on₀ on₁ on₂ ohn₁ ohn₂ := by
  dsimp only
  let Y := B.partialTotalSpectralObject
  let on : ℕ := q + 0
  let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
  let oi₂ : EInt := ((0 : ℤ) : EInt)
  let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
  let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
  let on₁ : ℤ := -(on : ℤ)
  let on₂ : ℤ := -(on : ℤ) + 1
  have ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
  have ohi₂₃ : oi₂ ≤ oi₃ := by
    dsimp only [oi₂, oi₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohiBot₁ : (⊥ : EInt) ≤ oi₁ := by simp
  have ohi₃Top : oi₃ ≤ (⊤ : EInt) := by simp
  have ohn₁ : on₀ + 1 = on₁ := by
    dsimp only [on₀, on₁, on]
    omega
  have ohn₂ : on₁ + 1 = on₂ := by
    dsimp only [on₁, on₂]
  exact Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) oi₁ oi₂ oi₃ ⊤ ohiBot₁ ohi₁₂ ohi₂₃ ohi₃Top
      on₀ on₁ on₂ ohn₁ ohn₂

private noncomputable def PTarget (q : ℕ) :
    let Y := B.partialTotalSpectralObject
    let on : ℕ := q + 0
    let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
    let oi₂ : EInt := ((0 : ℤ) : EInt)
    let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
    let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
    let on₁ : ℤ := -(on : ℤ)
    let on₂ : ℤ := -(on : ℤ) + 1
    let ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
    let ohi₂₃ : oi₂ ≤ oi₃ := by
      dsimp only [oi₂, oi₃]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohiBot₁ : (⊥ : EInt) ≤ oi₁ := by simp
    let ohi₃Top : oi₃ ≤ (⊤ : EInt) := by simp
    let ohn₁ : on₀ + 1 = on₁ := by
      dsimp only [on₀, on₁, on]
      omega
    let ohn₂ : on₁ + 1 = on₂ := by
      dsimp only [on₁, on₂]
    Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂)
        (homOfLE (ohi₂₃.trans ohi₃Top))
        on₀ on₁ on₂ ohn₁ ohn₂ ⟶
      B.partialTotalStableObj q 0 := by
  dsimp only
  let Y := B.partialTotalSpectralObject
  let on : ℕ := q + 0
  let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
  let oi₂ : EInt := ((0 : ℤ) : EInt)
  let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
  let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
  let on₁ : ℤ := -(on : ℤ)
  let on₂ : ℤ := -(on : ℤ) + 1
  have ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
  have ohi₂₃ : oi₂ ≤ oi₃ := by
    dsimp only [oi₂, oi₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohiBot₁ : (⊥ : EInt) ≤ oi₁ := by simp
  have ohi₃Top : oi₃ ≤ (⊤ : EInt) := by simp
  have ohn₁ : on₀ + 1 = on₁ := by
    dsimp only [on₀, on₁, on]
    omega
  have ohn₂ : on₁ + 1 = on₂ := by
    dsimp only [on₁, on₂]
  have ohTarget :
      Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂)
          (homOfLE (ohi₂₃.trans ohi₃Top)) on₀ on₁ on₂ ohn₁ ohn₂ =
        B.partialTotalStableObj (0 + q) 0 := by
    dsimp only [partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      on₀, on₁, on₂, on]
    congr 1
    all_goals omega
  exact (eqToIso ohTarget).hom ≫
    (eqToIso (congrArg (fun m => B.partialTotalStableObj m 0)
      (Nat.zero_add q))).hom

private noncomputable def FPage (q : ℕ) :
    let Y := B.partialTotalSpectralObject
    let on : ℕ := q + 0
    let or : ℤ := ((0 + q + 2 : ℕ) : ℤ)
    let oi₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
    let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
    let oi₂ : EInt := ((0 : ℤ) : EInt)
    let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
    let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
    let on₁ : ℤ := -(on : ℤ)
    let on₂ : ℤ := -(on : ℤ) + 1
    let ohr : (1 : ℤ) ≤ or := by
      dsimp only [or]
      omega
    let ohi₀₁ : oi₀ ≤ oi₁ := by
      dsimp only [oi₀, oi₁, partialTotalHomologyPreviousIndex]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
    let ohi₂₃ : oi₂ ≤ oi₃ := by
      dsimp only [oi₂, oi₃]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohn₁ : on₀ + 1 = on₁ := by
      dsimp only [on₀, on₁, on]
      omega
    let ohn₂ : on₁ + 1 = on₂ := by
      dsimp only [on₁, on₂]
    ((Y.spectralSequence core).page or ohr).X (0, q) ⟶
      Y.E (homOfLE ohi₀₁) (homOfLE ohi₁₂) (homOfLE ohi₂₃)
        on₀ on₁ on₂ ohn₁ ohn₂ := by
  dsimp only
  let Y := B.partialTotalSpectralObject
  let on : ℕ := q + 0
  let or : ℤ := ((0 + q + 2 : ℕ) : ℤ)
  let oi₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
  let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
  let oi₂ : EInt := ((0 : ℤ) : EInt)
  let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
  let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
  let on₁ : ℤ := -(on : ℤ)
  let on₂ : ℤ := -(on : ℤ) + 1
  have ohr : (1 : ℤ) ≤ or := by
    dsimp only [or]
    omega
  have ohi₀ : oi₀ = (core).i₀ or (0, q) ohr := by
    change oi₀ = (((0 : ℤ) - or : ℤ) : EInt)
    dsimp only [oi₀, or]
    congr 1
    omega
  have ohi₁ : oi₁ = (core).i₁ (0, q) := by
    change oi₁ = (((0 : ℤ) - 1 : ℤ) : EInt)
    dsimp only [oi₁, partialTotalHomologyPreviousIndex]
    rfl
  have ohi₂ : oi₂ = (core).i₂ (0, q) := rfl
  have ohi₃ : oi₃ = (core).i₃ or (0, q) ohr := by
    change oi₃ = (((0 : ℤ) + or - 1 : ℤ) : EInt)
    dsimp only [oi₃, or]
    congr 1
    omega
  have ohn : on₁ = (core).deg (0, q) := by
    change on₁ = -(0 : ℤ) - (q : ℤ)
    dsimp only [on₁, on]
    omega
  have ohn₁ : on₀ + 1 = on₁ := by
    dsimp only [on₀, on₁, on]
    omega
  have ohn₂ : on₁ + 1 = on₂ := by
    dsimp only [on₁, on₂]
  have ohi₀₁ : oi₀ ≤ oi₁ := by
    dsimp only [oi₀, oi₁, partialTotalHomologyPreviousIndex]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
  have ohi₂₃ : oi₂ ≤ oi₃ := by
    dsimp only [oi₂, oi₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  exact (Y.spectralSequencePageXIso core or ohr (0, q)
    oi₀ oi₁ oi₂ oi₃ ohi₀ ohi₁ ohi₂ ohi₃ on₀ on₁ on₂ ohn
      (hn₁ := ohn₁) (hn₂ := ohn₂)).hom

private noncomputable def FLeft (q : ℕ) :
    let Y := B.partialTotalSpectralObject
    let on : ℕ := q + 0
    let oi₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
    let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
    let oi₂ : EInt := ((0 : ℤ) : EInt)
    let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
    let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
    let on₁ : ℤ := -(on : ℤ)
    let on₂ : ℤ := -(on : ℤ) + 1
    let ohi₀₁ : oi₀ ≤ oi₁ := by
      dsimp only [oi₀, oi₁, partialTotalHomologyPreviousIndex]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
    let ohi₂₃ : oi₂ ≤ oi₃ := by
      dsimp only [oi₂, oi₃]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohiBot₁ : (⊥ : EInt) ≤ oi₁ := by simp
    let ohn₁ : on₀ + 1 = on₁ := by
      dsimp only [on₀, on₁, on]
      omega
    let ohn₂ : on₁ + 1 = on₂ := by
      dsimp only [on₁, on₂]
    Y.E (homOfLE ohi₀₁) (homOfLE ohi₁₂) (homOfLE ohi₂₃)
        on₀ on₁ on₂ ohn₁ ohn₂ ⟶
      Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂) (homOfLE ohi₂₃)
        on₀ on₁ on₂ ohn₁ ohn₂ := by
  dsimp only
  let Y := B.partialTotalSpectralObject
  let on : ℕ := q + 0
  let oi₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
  let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
  let oi₂ : EInt := ((0 : ℤ) : EInt)
  let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
  let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
  let on₁ : ℤ := -(on : ℤ)
  let on₂ : ℤ := -(on : ℤ) + 1
  have ohi₀₁ : oi₀ ≤ oi₁ := by
    dsimp only [oi₀, oi₁, partialTotalHomologyPreviousIndex]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
  have ohi₂₃ : oi₂ ≤ oi₃ := by
    dsimp only [oi₂, oi₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohiBot₀ : (⊥ : EInt) ≤ oi₀ := by simp
  have ohn₁ : on₀ + 1 = on₁ := by
    dsimp only [on₀, on₁, on]
    omega
  have ohn₂ : on₁ + 1 = on₂ := by
    dsimp only [on₁, on₂]
  have ohLeft : IsZero ((Y.H on₂).obj
      (mk₁ (homOfLE ohiBot₀))) := by
    exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
      on₂ (-(q : ℤ) - 2) (by omega)
  exact (Y.isoMapFourδ₁Toδ₀'
    (⊥ : EInt) oi₀ oi₁ oi₂ oi₃ ohiBot₀ ohi₀₁ ohi₁₂ ohi₂₃
      on₀ on₁ on₂ ohLeft (hn₁ := ohn₁) (hn₂ := ohn₂)).inv

private noncomputable def FRight (q : ℕ) :
    let Y := B.partialTotalSpectralObject
    let on : ℕ := q + 0
    let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
    let oi₂ : EInt := ((0 : ℤ) : EInt)
    let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
    let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
    let on₁ : ℤ := -(on : ℤ)
    let on₂ : ℤ := -(on : ℤ) + 1
    let ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
    let ohi₂₃ : oi₂ ≤ oi₃ := by
      dsimp only [oi₂, oi₃]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohiBot₁ : (⊥ : EInt) ≤ oi₁ := by simp
    let ohi₃Top : oi₃ ≤ (⊤ : EInt) := by simp
    let ohn₁ : on₀ + 1 = on₁ := by
      dsimp only [on₀, on₁, on]
      omega
    let ohn₂ : on₁ + 1 = on₂ := by
      dsimp only [on₁, on₂]
    Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂) (homOfLE ohi₂₃)
        on₀ on₁ on₂ ohn₁ ohn₂ ⟶
      Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂)
        (homOfLE (ohi₂₃.trans ohi₃Top))
        on₀ on₁ on₂ ohn₁ ohn₂ := by
  dsimp only
  let Y := B.partialTotalSpectralObject
  let on : ℕ := q + 0
  let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
  let oi₂ : EInt := ((0 : ℤ) : EInt)
  let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
  let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
  let on₁ : ℤ := -(on : ℤ)
  let on₂ : ℤ := -(on : ℤ) + 1
  have ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
  have ohi₂₃ : oi₂ ≤ oi₃ := by
    dsimp only [oi₂, oi₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohiBot₁ : (⊥ : EInt) ≤ oi₁ := by simp
  have ohi₃Top : oi₃ ≤ (⊤ : EInt) := by simp
  have ohn₁ : on₀ + 1 = on₁ := by
    dsimp only [on₀, on₁, on]
    omega
  have ohn₂ : on₁ + 1 = on₂ := by
    dsimp only [on₁, on₂]
  exact Y.mapFourδ₄Toδ₃'
    (⊥ : EInt) oi₁ oi₂ oi₃ ⊤ ohiBot₁ ohi₁₂ ohi₂₃ ohi₃Top
      on₀ on₁ on₂ ohn₁ ohn₂

private noncomputable def FTarget (q : ℕ) :
    let Y := B.partialTotalSpectralObject
    let on : ℕ := q + 0
    let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
    let oi₂ : EInt := ((0 : ℤ) : EInt)
    let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
    let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
    let on₁ : ℤ := -(on : ℤ)
    let on₂ : ℤ := -(on : ℤ) + 1
    let ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
    let ohi₂₃ : oi₂ ≤ oi₃ := by
      dsimp only [oi₂, oi₃]
      simp only [WithBotTop.coe_le_coe]
      omega
    let ohiBot₁ : (⊥ : EInt) ≤ oi₁ := by simp
    let ohi₃Top : oi₃ ≤ (⊤ : EInt) := by simp
    let ohn₁ : on₀ + 1 = on₁ := by
      dsimp only [on₀, on₁, on]
      omega
    let ohn₂ : on₁ + 1 = on₂ := by
      dsimp only [on₁, on₂]
    Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂)
        (homOfLE (ohi₂₃.trans ohi₃Top))
        on₀ on₁ on₂ ohn₁ ohn₂ ⟶
      B.partialTotalStableObj q 0 := by
  dsimp only
  let Y := B.partialTotalSpectralObject
  let on : ℕ := q + 0
  let oi₁ : EInt := partialTotalHomologyPreviousIndex 0
  let oi₂ : EInt := ((0 : ℤ) : EInt)
  let oi₃ : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
  let on₀ : ℤ := -((on + 1 : ℕ) : ℤ)
  let on₁ : ℤ := -(on : ℤ)
  let on₂ : ℤ := -(on : ℤ) + 1
  have ohi₁₂ : oi₁ ≤ oi₂ := partialTotalHomologyPreviousIndex_le 0
  have ohi₂₃ : oi₂ ≤ oi₃ := by
    dsimp only [oi₂, oi₃]
    simp only [WithBotTop.coe_le_coe]
    omega
  have ohiBot₁ : (⊥ : EInt) ≤ oi₁ := by simp
  have ohi₃Top : oi₃ ≤ (⊤ : EInt) := by simp
  have ohn₁ : on₀ + 1 = on₁ := by
    dsimp only [on₀, on₁, on]
    omega
  have ohn₂ : on₁ + 1 = on₂ := by
    dsimp only [on₁, on₂]
  have ohTarget :
      Y.E (homOfLE ohiBot₁) (homOfLE ohi₁₂)
          (homOfLE (ohi₂₃.trans ohi₃Top)) on₀ on₁ on₂ ohn₁ ohn₂ =
        B.partialTotalStableObj (0 + q) 0 := by
    dsimp only [partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      on₀, on₁, on₂, on]
    congr 1
    all_goals omega
  exact (eqToIso ohTarget).hom ≫
    (eqToIso (congrArg (fun m => B.partialTotalStableObj m 0)
      (Nat.zero_add q))).hom

private structure StablePageZeroPublicCutData (q : ℕ) where
  I : Type
  sp : I
  sn : I
  hpn : sp = sn
  X₁ : I → C
  X₂ : I → C
  X₃ : I → C
  pageF : ∀ x : I,
    ((B.partialTotalSpectralObject.spectralSequence core).page
      (((0 + q + 2 : ℕ) : ℤ))).X (0, q) ≅ X₁ x
  leftF : ∀ x : I, X₂ x ≅ X₁ x
  rightF : ∀ x : I, X₂ x ⟶ X₃ x
  hpTarget : X₃ sp = B.partialTotalStableObj (0 + q) 0
  hnTarget : X₃ sn = B.partialTotalStableObj (0 + q) 0
  hFinal : B.partialTotalStableObj (0 + q) 0 =
    B.partialTotalStableObj q 0

private noncomputable def stablePageZeroPublicCutData (q : ℕ) :
    StablePageZeroPublicCutData B q := by
  let Y := B.partialTotalSpectralObject
  let rS : ℤ := ((0 + q + 2 : ℕ) : ℤ)
  have hrS : (1 : ℤ) ≤ rS := by
    dsimp only [rS]
    omega
  let i₀ : EInt := ((-(q : ℤ) - 2 : ℤ) : EInt)
  let i₁ : EInt := partialTotalHomologyPreviousIndex 0
  let i₂ : EInt := ((0 : ℤ) : EInt)
  let i3pub : EInt := (((0 + q + 1 : ℕ) : ℤ) : EInt)
  let i3P : EInt := (((q + 1 : ℕ) : ℤ) : EInt)
  let n₀ : ℤ := -((q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -(q : ℤ)
  let n₂ : ℤ := -(q : ℤ) + 1
  have hq : 0 + q = q := Nat.zero_add q
  have hCut : i3pub = i3P := by
    dsimp only [i3pub, i3P]
    rw [hq]
  let I := {x : EInt // x = i3P}
  let sp : I := ⟨i3pub, hCut⟩
  let sn : I := ⟨i3P, rfl⟩
  have hpn : sp = sn := by
    apply Subtype.ext
    exact hCut
  have hn : n₁ = (core).deg (0, q) := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_deg]
    dsimp only [n₁]
    omega
  have hn₁ : n₀ + 1 = n₁ := by
    dsimp only [n₀, n₁]
    omega
  have hn₂ : n₁ + 1 = n₂ := by
    dsimp only [n₁, n₂]
  have hi₀ : i₀ = (core).i₀ rS (0, q) hrS := by
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₀]
    dsimp only [i₀, rS]
    congr 1
    omega
  have hi₁ : i₁ = (core).i₁ (0, q) := by
    change i₁ = (((0 : ℤ) - 1 : ℤ) : EInt)
    dsimp only [i₁, partialTotalHomologyPreviousIndex]
    rfl
  have hi₂ : i₂ = (core).i₂ (0, q) := rfl
  have hi₃ (x : I) : x.1 = (core).i₃ rS (0, q) hrS := by
    rw [x.2]
    rw [CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat_i₃]
    dsimp only [i3P, rS]
    congr 1
    omega
  have hi₀₁ : i₀ ≤ i₁ := by
    dsimp only [i₀, i₁, partialTotalHomologyPreviousIndex]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hi₁₂ : i₁ ≤ i₂ := partialTotalHomologyPreviousIndex_le 0
  have hi₂₃ (x : I) : i₂ ≤ x.1 := by
    rw [x.2]
    dsimp only [i₂, i3P]
    simp only [WithBotTop.coe_le_coe]
    omega
  have hiBot₁ : (⊥ : EInt) ≤ i₁ := by simp
  have hi₃Top (x : I) : x.1 ≤ (⊤ : EInt) := by simp
  let X₁ (x : I) := Y.E
    (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE (hi₂₃ x))
    n₀ n₁ n₂ hn₁ hn₂
  let X₂ (x : I) := Y.E
    (homOfLE hiBot₁) (homOfLE hi₁₂) (homOfLE (hi₂₃ x))
    n₀ n₁ n₂ hn₁ hn₂
  let X₃ (x : I) := Y.E
    (homOfLE hiBot₁) (homOfLE hi₁₂)
      (homOfLE ((hi₂₃ x).trans (hi₃Top x)))
    n₀ n₁ n₂ hn₁ hn₂
  let pageF (x : I) :
      ((Y.spectralSequence core).page rS hrS).X (0, q) ≅ X₁ x :=
    Y.spectralSequencePageXIso core rS hrS (0, q)
      i₀ i₁ i₂ x.1 hi₀ hi₁ hi₂ (hi₃ x)
      n₀ n₁ n₂ hn (hn₁ := hn₁) (hn₂ := hn₂)
  let leftF (x : I) : X₂ x ≅ X₁ x := by
    have hLeft : IsZero ((Y.H n₂).obj
        (mk₁ (homOfLE (show (⊥ : EInt) ≤ i₀ by simp)))) := by
      exact B.isZero_partialTotalSpectralObjectHObj_bot_to_neg
        n₂ (-(q : ℤ) - 2) (by omega)
    exact Y.isoMapFourδ₁Toδ₀'
      (⊥ : EInt) i₀ i₁ i₂ x.1 (by simp)
      hi₀₁ hi₁₂ (hi₂₃ x) n₀ n₁ n₂ hLeft
      (hn₁ := hn₁) (hn₂ := hn₂)
  let rightF (x : I) : X₂ x ⟶ X₃ x :=
    Y.mapFourδ₄Toδ₃'
      (⊥ : EInt) i₁ i₂ x.1 ⊤ hiBot₁ hi₁₂ (hi₂₃ x)
      (hi₃Top x) n₀ n₁ n₂ hn₁ hn₂
  have hpTarget : X₃ sp =
      B.partialTotalStableObj (0 + q) 0 := by
    dsimp only [X₃, sp, partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      n₀, n₁, n₂]
    congr 1
    all_goals omega
  have hnTarget : X₃ sn =
      B.partialTotalStableObj (0 + q) 0 := by
    dsimp only [X₃, sn, partialTotalStableObj, stableIntervalObj,
      stableIntervalLeft, stableIntervalMiddle, stableIntervalRight,
      n₀, n₁, n₂]
    congr 1
    all_goals omega
  exact
    { I := I
      sp := sp
      sn := sn
      hpn := hpn
      X₁ := X₁
      X₂ := X₂
      X₃ := X₃
      pageF := pageF
      leftF := leftF
      rightF := rightF
      hpTarget := hpTarget
      hnTarget := hnTarget
      hFinal := congrArg (fun m => B.partialTotalStableObj m 0) hq }

private noncomputable def StablePageZeroPublicCutData.publicHom
    {q : ℕ} (D : StablePageZeroPublicCutData B q) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
      (((0 + q + 2 : ℕ) : ℤ))).X (0, q) ⟶
      B.partialTotalStableObj q 0 :=
  (D.pageF D.sp).hom ≫ (D.leftF D.sp).inv ≫ D.rightF D.sp ≫
    eqToHom D.hpTarget ≫ eqToHom D.hFinal

private noncomputable def StablePageZeroPublicCutData.normalizedHom
    {q : ℕ} (D : StablePageZeroPublicCutData B q) :
    ((B.partialTotalSpectralObject.spectralSequence core).page
      (((0 + q + 2 : ℕ) : ℤ))).X (0, q) ⟶
      B.partialTotalStableObj q 0 :=
  (D.pageF D.sn).hom ≫ (D.leftF D.sn).inv ≫ D.rightF D.sn ≫
    eqToHom D.hnTarget ≫ eqToHom D.hFinal

private theorem StablePageZeroPublicCutData.page_naturality
    {q : ℕ} (D : StablePageZeroPublicCutData B q) :
    (D.pageF D.sp).hom ≫ eqToHom (congrArg D.X₁ D.hpn) =
      (D.pageF D.sn).hom := by
  have h := CategoryTheory.eqToHom_iso_hom_naturality D.pageF D.hpn
  simpa only [eqToHom_refl, Category.id_comp] using h

private theorem StablePageZeroPublicCutData.left_naturality
    {q : ℕ} (D : StablePageZeroPublicCutData B q) :
    (D.leftF D.sp).inv ≫ eqToHom (congrArg D.X₂ D.hpn) =
      eqToHom (congrArg D.X₁ D.hpn) ≫ (D.leftF D.sn).inv := by
  exact CategoryTheory.eqToHom_iso_inv_naturality D.leftF D.hpn

private theorem StablePageZeroPublicCutData.right_naturality
    {q : ℕ} (D : StablePageZeroPublicCutData B q) :
    D.rightF D.sp ≫ eqToHom (congrArg D.X₃ D.hpn) =
      eqToHom (congrArg D.X₂ D.hpn) ≫ D.rightF D.sn := by
  exact CategoryTheory.eqToHom_naturality D.rightF D.hpn

private theorem StablePageZeroPublicCutData.target_naturality
    {q : ℕ} (D : StablePageZeroPublicCutData B q) :
    eqToHom D.hpTarget ≫ eqToHom D.hFinal =
      eqToHom (congrArg D.X₃ D.hpn) ≫
        eqToHom D.hnTarget ≫ eqToHom D.hFinal := by
  simp only [CategoryTheory.eqToHom_trans]

private theorem StablePageZeroPublicCutData.publicHom_eq_normalizedHom
    {q : ℕ} (D : StablePageZeroPublicCutData B q) :
    D.publicHom = D.normalizedHom := by
  unfold publicHom normalizedHom
  slice_lhs 4 5 => rw [D.target_naturality]
  slice_lhs 3 4 => rw [D.right_naturality]
  slice_lhs 2 3 => rw [D.left_naturality]
  slice_lhs 1 2 => rw [D.page_naturality]
  simp only [Category.assoc]

private theorem
    partialTotalStablePageIso_zero_comp_eq_publicCutHom (q : ℕ) :
    (B.partialTotalStablePageIso 0 q).hom ≫ eqToHom
      (congrArg (fun m => B.partialTotalStableObj m 0) (Nat.zero_add q)) =
        (B.stablePageZeroPublicCutData q).publicHom := by
  unfold partialTotalStablePageIso
    StablePageZeroPublicCutData.publicHom
    stablePageZeroPublicCutData
  dsimp only
  simp only [Nat.add_zero, Nat.mul_zero,
    partialTotalHomologyPreviousIndex_zero,
    Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
    CategoryTheory.Abelian.SpectralObject.isoMapFourδ₄Toδ₃'_hom,
    Category.assoc]
  rfl

private theorem stablePageZeroPublicCutData_normalizedHom_eq_PFactors
    (q : ℕ) :
    (B.stablePageZeroPublicCutData q).normalizedHom =
      B.PPage q ≫ B.PLeft q ≫ B.PRight q ≫ B.PTarget q := by
  unfold StablePageZeroPublicCutData.normalizedHom
    stablePageZeroPublicCutData PPage PLeft PRight PTarget
  dsimp only
  simp only [Nat.add_zero, eqToIso.hom, id_eq]

private theorem partialTotalStablePageIso_zero_comp_eq_PFactors (q : ℕ) :
    (B.partialTotalStablePageIso 0 q).hom ≫ eqToHom
      (congrArg (fun m => B.partialTotalStableObj m 0) (Nat.zero_add q)) =
        B.PPage q ≫ B.PLeft q ≫ B.PRight q ≫ B.PTarget q := by
  let D := B.stablePageZeroPublicCutData q
  calc
    _ = D.publicHom :=
      B.partialTotalStablePageIso_zero_comp_eq_publicCutHom q
    _ = D.normalizedHom := D.publicHom_eq_normalizedHom
    _ = _ := B.stablePageZeroPublicCutData_normalizedHom_eq_PFactors q

private theorem stablePageZeroOwnerFactorHom_eq_FFactors (q : ℕ) :
    B.stablePageZeroOwnerFactorHom q =
      B.FPage q ≫ B.FLeft q ≫ B.FRight q ≫ B.FTarget q := by
  unfold stablePageZeroOwnerFactorHom FPage FLeft FRight FTarget
  dsimp only
  simp only [Nat.add_zero, partialTotalHomologyPreviousIndex_zero,
    eqToIso.hom,
    CategoryTheory.Abelian.SpectralObject.isoMapFourδ₄Toδ₃'_hom,
    id_eq]

private theorem PPage_eq_FPage (q : ℕ) :
    B.PPage q = B.FPage q := by
  unfold PPage FPage
  rfl

private theorem PLeft_eq_FLeft (q : ℕ) :
    B.PLeft q = B.FLeft q := by
  unfold PLeft FLeft
  rfl

private theorem PRight_eq_FRight (q : ℕ) :
    B.PRight q = B.FRight q := by
  unfold PRight FRight
  rfl

private theorem PTarget_eq_FTarget (q : ℕ) :
    B.PTarget q = B.FTarget q := by
  unfold PTarget FTarget
  rfl

private theorem PFactors_eq_FFactors (q : ℕ) :
    B.PPage q ≫ B.PLeft q ≫ B.PRight q ≫ B.PTarget q =
      B.FPage q ≫ B.FLeft q ≫ B.FRight q ≫ B.FTarget q := by
  rw [B.PPage_eq_FPage q, B.PLeft_eq_FLeft q,
    B.PRight_eq_FRight q, B.PTarget_eq_FTarget q]

private theorem partialTotalStablePageIso_zero_comp_eq_ownerFactorHom (q : ℕ) :
    (B.partialTotalStablePageIso 0 q).hom ≫ eqToHom
      (congrArg (fun m => B.partialTotalStableObj m 0) (Nat.zero_add q)) =
        B.stablePageZeroOwnerFactorHom q := by
  calc
    _ = B.PPage q ≫ B.PLeft q ≫ B.PRight q ≫ B.PTarget q :=
      B.partialTotalStablePageIso_zero_comp_eq_PFactors q
    _ = B.FPage q ≫ B.FLeft q ≫ B.FRight q ≫ B.FTarget q :=
      B.PFactors_eq_FFactors q
    _ = _ := (B.stablePageZeroOwnerFactorHom_eq_FFactors q).symm

private theorem partialTotalStablePageZeroColumnHom_eq_alignedFactorHom
    (q : ℕ) :
    B.partialTotalStablePageZeroColumnHom q =
      B.stablePageZeroAlignedFactorHom q := by
  unfold partialTotalStablePageZeroColumnHom stablePageZeroAlignedFactorHom
  rfl

private theorem comparisonData_ownerHom_eq_ownerFactorHom (q : ℕ) :
    (B.stablePageZeroComparisonData q).ownerHom =
      B.stablePageZeroOwnerFactorHom q := by
  unfold StablePageZeroComparisonData.ownerHom
    stablePageZeroComparisonData stablePageZeroOwnerFactorHom
  dsimp only
  rfl

private theorem comparisonData_alignedHom_eq_alignedFactorHom (q : ℕ) :
    (B.stablePageZeroComparisonData q).alignedHom =
      B.stablePageZeroAlignedFactorHom q := by
  unfold StablePageZeroComparisonData.alignedHom
    stablePageZeroComparisonData stablePageZeroAlignedFactorHom
  dsimp only
  rfl

private theorem stablePageZeroOwnerFactorHom_eq_alignedFactorHom (q : ℕ) :
    B.stablePageZeroOwnerFactorHom q =
      B.stablePageZeroAlignedFactorHom q := by
  let D := B.stablePageZeroComparisonData q
  calc
    _ = D.ownerHom := (B.comparisonData_ownerHom_eq_ownerFactorHom q).symm
    _ = D.alignedHom := D.ownerHom_eq_alignedHom
    _ = _ := B.comparisonData_alignedHom_eq_alignedFactorHom q

/-- Zero-column stable isomorphism agrees with the degree-q coordinate.

After transporting `B.partialTotalStableObj (0 + q) 0` to `B.partialTotalStableObj q 0` along
`0 + q = q`, the forward map of `B.partialTotalStablePageIso 0 q` equals
`B.partialTotalStablePageZeroColumnHom q`. -/
theorem partialTotalStablePageIso_zero_hom_comp_eqToIso_hom (q : ℕ) :
    (B.partialTotalStablePageIso 0 q).hom ≫
        (eqToIso (congrArg (fun m => B.partialTotalStableObj m 0)
          (Nat.zero_add q))).hom =
      B.partialTotalStablePageZeroColumnHom q := by
  calc
    _ = B.stablePageZeroOwnerFactorHom q :=
      B.partialTotalStablePageIso_zero_comp_eq_ownerFactorHom q
    _ = B.stablePageZeroAlignedFactorHom q :=
      B.stablePageZeroOwnerFactorHom_eq_alignedFactorHom q
    _ = _ := (B.partialTotalStablePageZeroColumnHom_eq_alignedFactorHom q).symm

end HomologicalComplex₂

end
