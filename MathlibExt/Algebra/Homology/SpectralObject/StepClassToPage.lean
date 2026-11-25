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

public import MathlibExt.Algebra.Homology.SpectralObject.FiniteStripSuccessor
public import MathlibExt.Algebra.Homology.SpectralObject.AbutmentFiltration
public import MathlibExt.Algebra.Homology.SpectralSequence.FirstPageRow
public import Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import MathlibExt.Algebra.Homology.SpectralSequence.SingleRow
/-!
# Maps from interval classes to spectral-sequence pages

A spectral object in an abelian category indexed by a bounded preorder
maps bottom-to-cut interval classes to cycles and four-cut `E` objects.
These maps commute with changes of the outer cuts. Under the stated
endpoint vanishing hypotheses, they also commute with padding to stable
intervals and kernel-graded quotients.

For `EInt` indices, the constructions give compatible class maps on skeletal
spectral-sequence pages and lifts to their cycles. First-page row
identifications send these lifts to second-page homology classes. If the
first page is supported in row zero, the class maps are preserved by the
single-row successor and later-page isomorphisms. The zero-row versions
make the total-degree transport explicit.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
  Opposite

universe u v w

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [Preorder ι] [OrderBot ι] [OrderTop ι]
variable (Y : SpectralObject C ι)

/-- Bottom-to-cut interval classes map to cycles in a three-cut window. -/
def stepClassToCycles (n : ℤ) {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c) :
    Y.stableIntervalStep n c ⟶
      Y.cycles (homOfLE hab) (homOfLE hbc) n :=
  Y.toCycles (homOfLE (bot_le : (⊥ : ι) ≤ b)) (homOfLE hbc)
      (homOfLE (bot_le : (⊥ : ι) ≤ c)) (by subsingleton) n ≫
    Y.cyclesMap (homOfLE (bot_le : (⊥ : ι) ≤ b)) (homOfLE hbc)
      (homOfLE hab) (homOfLE hbc)
      (homMk₂ (homOfLE (bot_le : (⊥ : ι) ≤ a)) (𝟙 b) (𝟙 c)
        (by subsingleton) (by subsingleton)) n

/-- Including the cycles recovers restriction to the middle interval. -/
-- Keep the original hypothesis parameters and their order in this compatibility declaration.
@[reassoc, nolint unusedArguments]
theorem stepClassToCycles_i (n : ℤ) {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c) :
    Y.stepClassToCycles n hab hbc ≫
        Y.iCycles (homOfLE hab) (homOfLE hbc) n =
      (Y.H n).map (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : ι) ≤ b)) (homOfLE hbc)
        (homOfLE (bot_le : (⊥ : ι) ≤ c)) (by subsingleton)) := by
  dsimp only [stepClassToCycles]
  erw [Category.assoc, Y.cyclesMap_i _ _ _ _ _ (𝟙 _) n (by ext <;> subsingleton)]
  simp only [Functor.map_id, Category.comp_id]
  exact Y.toCycles_i _ _ _ _ n

/-- Bottom-to-cut interval classes map to the four-cut `E` object via the cycle quotient. -/
def stepClassToE (n : ℤ) {a b c d : ι}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    Y.stableIntervalStep n c ⟶
      Y.E (homOfLE hab) (homOfLE hbc) (homOfLE hcd)
        (n - 1) n (n + 1) (by omega) (by omega) :=
  Y.stepClassToCycles n hab hbc ≫
    Y.πE (homOfLE hab) (homOfLE hbc) (homOfLE hcd)
      (n - 1) n (n + 1) (by omega) (by omega)

/-- Increasing the left cut preserves the restricted cycle under the window map. -/
@[reassoc]
theorem stepClassToCycles_left (n : ℤ) {a' a b c : ι}
    (haa : a' ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    Y.stepClassToCycles n (haa.trans hab) hbc ≫
        Y.cyclesMap (stableIntervalMiddle (haa.trans hab)) (stableIntervalMiddle hbc)
          (stableIntervalMiddle hab) (stableIntervalMiddle hbc)
          (homMk₂ (homOfLE haa) (𝟙 b) (𝟙 c) (by subsingleton) (by subsingleton)) n =
      Y.stepClassToCycles n hab hbc := by
  apply (cancel_mono (Y.iCycles (stableIntervalMiddle hab) (stableIntervalMiddle hbc) n)).mp
  erw [Category.assoc, Y.cyclesMap_i _ _ _ _ _ (𝟙 _) n (by ext <;> subsingleton),
    Functor.map_id, Category.comp_id, stepClassToCycles_i, stepClassToCycles_i]

/-- The left-window map preserves the interval class in `E`. -/
@[reassoc]
theorem stepClassToE_left (n : ℤ) {a' a b c d : ι}
    (haa : a' ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    Y.stepClassToE n (haa.trans hab) hbc hcd ≫
        Y.mapFourδ₁Toδ₀' a' a b c d haa hab hbc hcd
          (n - 1) n (n + 1) (by omega) (by omega) =
      Y.stepClassToE n hab hbc hcd := by
  let β : mk₂ (stableIntervalMiddle (haa.trans hab)) (stableIntervalMiddle hbc) ⟶
      mk₂ (stableIntervalMiddle hab) (stableIntervalMiddle hbc) :=
    homMk₂ (homOfLE haa) (𝟙 b) (𝟙 c) (by subsingleton) (by subsingleton)
  have hπ := Y.πE_map
    (stableIntervalMiddle (haa.trans hab)) (stableIntervalMiddle hbc) (stableIntervalMiddle hcd)
    (stableIntervalMiddle hab) (stableIntervalMiddle hbc) (stableIntervalMiddle hcd)
    (fourδ₁Toδ₀' a' a b c d haa hab hbc hcd) β
    (n - 1) n (n + 1) (by ext <;> subsingleton) (by omega) (by omega)
  dsimp only [stepClassToE]
  erw [Category.assoc, hπ, ← Category.assoc, stepClassToCycles_left]
  rfl

/-- The right-window map preserves the interval class in `E`. -/
-- Keep the original hypothesis parameters and their order in this compatibility declaration.
@[reassoc, nolint unusedArguments]
theorem stepClassToE_right (n : ℤ) {a b c d d' : ι}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hdd : d ≤ d') :
    Y.stepClassToE n hab hbc hcd ≫
        Y.mapFourδ₄Toδ₃' a b c d d' hab hbc hcd hdd
          (n - 1) n (n + 1) (by omega) (by omega) =
      Y.stepClassToE n hab hbc (hcd.trans hdd) := by
  have hπ := Y.πE_map
    (stableIntervalMiddle hab) (stableIntervalMiddle hbc) (stableIntervalMiddle hcd)
    (stableIntervalMiddle hab) (stableIntervalMiddle hbc) (stableIntervalMiddle (hcd.trans hdd))
    (fourδ₄Toδ₃' a b c d d' hab hbc hcd hdd) (𝟙 _)
    (n - 1) n (n + 1) (by ext <;> subsingleton) (by omega) (by omega)
  dsimp only [stepClassToE]
  erw [Category.assoc, hπ, Y.cyclesMap_id, Category.id_comp]
  rfl

/-- With bottom and top outer cuts, the class map is the stable-interval quotient map. -/
theorem stepClassToE_stable (n : ℤ) {b c : ι} (hbc : b ≤ c) :
    Y.stepClassToE n (bot_le : (⊥ : ι) ≤ b) hbc (le_top : c ≤ (⊤ : ι)) =
      Y.stableIntervalStepToStable n hbc := by
  have hId :
      (homMk₂ (homOfLE (bot_le : (⊥ : ι) ≤ (⊥ : ι))) (𝟙 b) (𝟙 c)
        (by subsingleton) (by subsingleton) :
        mk₂ (stableIntervalLeft b) (stableIntervalMiddle hbc) ⟶
          mk₂ (stableIntervalLeft b) (stableIntervalMiddle hbc)) = 𝟙 _ := by
    ext <;> subsingleton
  dsimp only [stepClassToE, stepClassToCycles, stableIntervalStepToStable,
    stableIntervalCokernelSequence, cokernelSequenceE]
  erw [hId, Y.cyclesMap_id, Category.comp_id]
  rfl

/-- Under endpoint vanishing, padding carries an interval class to its stable quotient. -/
@[reassoc]
theorem stepClassToE_padding (n : ℤ) {a b c d : ι}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hleft : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ a)))))
    (hright : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : d ≤ (⊤ : ι)))))) :
    Y.stepClassToE n hab hbc hcd ≫
        (Y.finiteIntervalPaddingIso n hab hbc hcd hleft hright).hom =
      Y.stableIntervalStepToStable n hbc := by
  let L := Y.isoMapFourδ₁Toδ₀' (⊥ : ι) a b c d
    bot_le hab hbc hcd (n - 1) n (n + 1) hleft (by omega) (by omega)
  let R := Y.isoMapFourδ₄Toδ₃' (⊥ : ι) b c d (⊤ : ι)
    bot_le hbc hcd le_top (n - 1) n (n + 1) hright (by omega) (by omega)
  have hL : Y.stepClassToE n (bot_le : (⊥ : ι) ≤ b) hbc hcd ≫ L.hom =
      Y.stepClassToE n hab hbc hcd := by
    change Y.stepClassToE n (bot_le : (⊥ : ι) ≤ b) hbc hcd ≫
        Y.mapFourδ₁Toδ₀' (⊥ : ι) a b c d bot_le hab hbc hcd
          (n - 1) n (n + 1) (by omega) (by omega) = _
    exact Y.stepClassToE_left n bot_le hab hbc hcd
  have hLinv : Y.stepClassToE n hab hbc hcd ≫ L.inv =
      Y.stepClassToE n (bot_le : (⊥ : ι) ≤ b) hbc hcd := by
    erw [← hL, Category.assoc, L.hom_inv_id, Category.comp_id]
  have hR : Y.stepClassToE n (bot_le : (⊥ : ι) ≤ b) hbc hcd ≫ R.hom =
      Y.stepClassToE n (bot_le : (⊥ : ι) ≤ b) hbc (le_top : c ≤ (⊤ : ι)) := by
    change Y.stepClassToE n (bot_le : (⊥ : ι) ≤ b) hbc hcd ≫
        Y.mapFourδ₄Toδ₃' (⊥ : ι) b c d (⊤ : ι) bot_le hbc hcd le_top
          (n - 1) n (n + 1) (by omega) (by omega) = _
    exact Y.stepClassToE_right n bot_le hbc hcd le_top
  change Y.stepClassToE n hab hbc hcd ≫ (L.inv ≫ R.hom) = _
  erw [← Category.assoc, hLinv, hR]
  exact Y.stepClassToE_stable n hbc

/-- Under endpoint vanishing, the class map agrees with the image-to-kernel graded projection. -/
@[reassoc]
theorem stepClassToE_kernelGraded (n : ℤ) {a b c d : ι}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hleft : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ a)))))
    (hright : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : d ≤ (⊤ : ι)))))) :
    Y.stepClassToE n hab hbc hcd ≫
        (Y.finiteIntervalKernelGradedIso n hab hbc hcd hleft hright).hom =
      Y.stableIntervalStepToImage n c ≫ (Y.stableIntervalImageKernelIso n c).hom ≫
        cokernel.π (Subobject.ofLE _ _ (Y.stableIntervalKernelFiltration_monotone n hbc)) := by
  dsimp only [finiteIntervalKernelGradedIso, finiteIntervalImageCokernelIso, Iso.trans_hom]
  simp only [Category.assoc]
  erw [stepClassToE_padding_assoc]
  rw [← Y.stableIntervalStepToImage_comp_imageToStable n hbc]
  simp only [Category.assoc]
  rw [Y.stableIntervalImageToStable_comp_iso_hom_assoc,
    Y.stableIntervalImageKernelGradedIso_π]

/-- For identity outer intervals, `E ≅ H` sends the class map to interval restriction. -/
@[reassoc]
theorem stepClassToE_identity_hom (n : ℤ) {b c : ι} (hbc : b ≤ c) :
    Y.stepClassToE n (le_refl b) hbc (le_refl c) ≫
        (Y.EIsoH (homOfLE hbc) (n - 1) n (n + 1) (by omega) (by omega)).hom =
      (Y.H n).map (twoδ₁Toδ₀ (homOfLE (bot_le : (⊥ : ι) ≤ b)) (homOfLE hbc)
        (homOfLE (bot_le : (⊥ : ι) ≤ c)) (by subsingleton)) := by
  have hc : (Y.cyclesIsoH (homOfLE hbc) n (n + 1) (by omega)).hom =
      Y.iCycles (𝟙 b) (homOfLE hbc) n := by
    apply (cancel_epi (Y.toCycles (𝟙 b) (homOfLE hbc)
      (homOfLE hbc) (by simp) n)).mp
    rw [Y.cyclesIsoH_inv_hom_id (homOfLE hbc) n (n + 1) (by omega),
      Y.toCycles_i]
    have heq : twoδ₁Toδ₀ (𝟙 b) (homOfLE hbc)
        (homOfLE hbc) (by simp) = 𝟙 _ := by subsingleton
    rw [heq, Functor.map_id]
  dsimp only [stepClassToE]
  erw [Category.assoc, ← Y.cyclesIsoH_hom_EIsoH_inv
    (n - 1) n (n + 1) (by omega) (by omega) (homOfLE hbc)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hc]
  exact Y.stepClassToCycles_i n (le_refl b) hbc

end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (Y : SpectralObject C EInt)

/-- The bottom-to-cut interval class maps to a skeletal spectral-sequence page. -/
def skeletalStepClassToPage (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    Y.stableIntervalStep (p + q) ((-p : ℤ) : EInt) ⟶
      ((Y.skeletalSpectralSequence).page r hr).X (p, q) :=
  Y.stepClassToE (p + q)
      (show ((-p - r : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; omega)
      (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
      (show ((-p : ℤ) : EInt) ≤ ((-p + r - 1 : ℤ) : EInt) by simp; omega) ≫
    (Y.skeletalPageWindowIso r hr p q).inv

/-- The intermediate-window class includes as the current skeletal page class. -/
@[reassoc]
theorem skeletalStepClassToPage_successor_i (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    Y.stepClassToE (p + q)
        (show ((-p - (r + 1) : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; omega)
        (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
        (show ((-p : ℤ) : EInt) ≤ ((-p + r - 1 : ℤ) : EInt) by simp; omega) ≫
        (Y.skeletalSuccessorHomologyData r hr p q).left.i =
      Y.skeletalStepClassToPage r hr p q := by
  rw [skeletalSuccessorHomologyData_i]
  erw [← Category.assoc, stepClassToE_left]
  rfl

/-- The successor homology quotient sends the intermediate-window class to the next page. -/
@[reassoc]
theorem skeletalStepClassToPage_successor_π (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    Y.stepClassToE (p + q)
        (show ((-p - (r + 1) : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; omega)
        (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
        (show ((-p : ℤ) : EInt) ≤ ((-p + r - 1 : ℤ) : EInt) by simp; omega) ≫
        (Y.skeletalSuccessorHomologyData r hr p q).left.π ≫
        (Y.skeletalPageWindowIso (r + 1) (by omega) p q).inv =
      Y.skeletalStepClassToPage (r + 1) (by omega) p q := by
  rw [skeletalSuccessorHomologyData_π]
  erw [← Category.assoc, stepClassToE_right]
  rfl

/-- The interval class map is annihilated by every skeletal page differential. -/
@[reassoc]
theorem skeletalStepClassToPage_g (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    Y.skeletalStepClassToPage r hr p q ≫
        (((Y.skeletalSpectralSequence).page r hr).sc (p, q)).g = 0 := by
  rw [← Y.skeletalStepClassToPage_successor_i r hr p q, Category.assoc,
    (Y.skeletalSuccessorHomologyData r hr p q).left.wi, comp_zero]

/-- Equal page indices give compatible transports of the interval class map. -/
@[reassoc]
theorem skeletalStepClassToPage_cast (r r' : ℤ) (h : r = r') (hr : 1 ≤ r) (p q : ℤ) :
    Y.skeletalStepClassToPage r hr p q ≫
        ((Y.skeletalSpectralSequence).pageXIsoOfEq (p, q) r r' h hr).hom =
      Y.skeletalStepClassToPage r' (by omega) p q := by
  subst r'
  simp only [CategoryTheory.SpectralSequence.pageXIsoOfEq, eqToIso_refl,
    Iso.refl_hom, Category.comp_id]

/-- With first-page support in row zero, the single-row successor preserves the interval class map. -/
@[reassoc]
theorem skeletalStepClassToPage_singleRowSuccessor
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero (((Y.skeletalSpectralSequence).page 1).X (p, q)))
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) :
    Y.skeletalStepClassToPage r (by omega) p q ≫
        ((Y.skeletalSpectralSequence).singleRowSuccessorIso hrow r hr (p, q)).hom =
      Y.skeletalStepClassToPage (r + 1) (by omega) p q := by
  let S := Y.skeletalSpectralSequence
  let HD := Y.skeletalSuccessorHomologyData r (by omega) p q
  have hi : HD.left.i ≫ (S.singleRowSuccessorIso hrow r hr (p, q)).hom ≫
      (Y.skeletalPageWindowIso (r + 1) (by omega) p q).hom = HD.left.π := by
    dsimp only [CategoryTheory.SpectralSequence.singleRowSuccessorIso, Iso.trans_hom, Iso.symm_hom]
    rw [Y.skeletalSequence_iso_eq_successorHomologyData]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    exact ShortComplex.LeftHomologyData.i_comp_zeroHomologyIso _ HD.left
      (S.page_d_eq_zero_of_firstPage_off_row hrow r hr _ _)
      (S.page_d_eq_zero_of_firstPage_off_row hrow r hr _ _)
  apply (cancel_mono (Y.skeletalPageWindowIso (r + 1) (by omega) p q).hom).mp
  erw [← Y.skeletalStepClassToPage_successor_i r (by omega) p q]
  simp only [Category.assoc]
  erw [hi, ← Y.skeletalStepClassToPage_successor_π r (by omega) p q]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The interval class map lifts to the cycles of a skeletal page. -/
def skeletalStepClassToPageCycles (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    Y.stableIntervalStep (p + q) ((-p : ℤ) : EInt) ⟶
      ((Y.skeletalSpectralSequence).page r hr).cycles (p, q) :=
  Y.stepClassToE (p + q)
      (show ((-p - (r + 1) : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; omega)
      (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
      (show ((-p : ℤ) : EInt) ≤ ((-p + r - 1 : ℤ) : EInt) by simp; omega) ≫
    (Y.skeletalSuccessorHomologyData r hr p q).left.cyclesIso.inv

/-- Including the cycle lift recovers the skeletal page class map. -/
@[reassoc]
theorem skeletalStepClassToPageCycles_i (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    Y.skeletalStepClassToPageCycles r hr p q ≫
        ((Y.skeletalSpectralSequence).page r hr).iCycles (p, q) =
      Y.skeletalStepClassToPage r hr p q := by
  dsimp only [skeletalStepClassToPageCycles, HomologicalComplex.iCycles]
  erw [Category.assoc,
    (Y.skeletalSuccessorHomologyData r hr p q).left.cyclesIso_inv_comp_iCycles]
  exact Y.skeletalStepClassToPage_successor_i r hr p q

/-- The cycle quotient followed by the successor isomorphism recovers the next-page class map. -/
@[reassoc]
theorem skeletalStepClassToPageCycles_homology (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    Y.skeletalStepClassToPageCycles r hr p q ≫
        ((Y.skeletalSpectralSequence).page r hr).homologyπ (p, q) ≫
        ((Y.skeletalSpectralSequence).iso r (r + 1) (p, q) rfl hr).hom =
      Y.skeletalStepClassToPage (r + 1) (by omega) p q := by
  dsimp only [skeletalStepClassToPageCycles, HomologicalComplex.homologyπ]
  rw [Y.skeletalSequence_iso_eq_successorHomologyData]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [(Y.skeletalSuccessorHomologyData r hr p q).left.homologyπ_comp_homologyIso_hom_assoc]
  simp only [Iso.inv_hom_id_assoc]
  exact Y.skeletalStepClassToPage_successor_π r hr p q

/-- Iterating single-row successors preserves the class map when the first page is supported in row zero. -/
@[reassoc]
theorem skeletalStepClassToPage_singleRowNat
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero (((Y.skeletalSpectralSequence).page 1).X (p, q)))
    (p q : ℤ) (k : ℕ) :
    Y.skeletalStepClassToPage 2 (by omega) p q ≫
        ((Y.skeletalSpectralSequence).singleRowPageIsoNat hrow (p, q) k).hom =
      Y.skeletalStepClassToPage ((k : ℤ) + 2) (by omega) p q := by
  induction k with
  | zero =>
    dsimp only [CategoryTheory.SpectralSequence.singleRowPageIsoNat]
    exact Y.skeletalStepClassToPage_cast 2 (((0 : ℕ) : ℤ) + 2) (by omega) (by omega) p q
  | succ k ih =>
    dsimp only [CategoryTheory.SpectralSequence.singleRowPageIsoNat, Iso.trans_hom]
    rw [← Category.assoc, ih, ← Category.assoc,
      Y.skeletalStepClassToPage_singleRowSuccessor]
    exact Y.skeletalStepClassToPage_cast (((k : ℤ) + 2) + 1)
      (((k + 1 : ℕ) : ℤ) + 2) (by omega) (by omega) p q

/-- The single-row comparison from page two preserves the class map under first-page support in row zero. -/
@[reassoc]
theorem skeletalStepClassToPage_singleRowPage
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero (((Y.skeletalSpectralSequence).page 1).X (p, q)))
    (r : ℤ) (hr : 2 ≤ r) (p q : ℤ) :
    Y.skeletalStepClassToPage 2 (by omega) p q ≫
        ((Y.skeletalSpectralSequence).singleRowPageIso hrow r hr (p, q)).hom =
      Y.skeletalStepClassToPage r (by omega) p q := by
  dsimp only [CategoryTheory.SpectralSequence.singleRowPageIso, Iso.trans_hom]
  rw [← Category.assoc, Y.skeletalStepClassToPage_singleRowNat]
  exact Y.skeletalStepClassToPage_cast (((r - 2).toNat : ℤ) + 2) r (by omega) (by omega) p q

end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : CohomologicalSpectralSequence C 1)

/-- A first-page row short complex identifies with the corresponding short complex of the page. -/
def firstPageRowShortComplexIso (p q : ℤ) :
    (S.firstPageRow q).sc' (p - 1) p (p + 1) ≅
      (S.page 1).sc' (p - 1, q) (p, q) (p + 1, q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- First-page row cycles identify with cycles at the corresponding page position. -/
def firstPageRowCyclesIso (p q : ℤ) :
    (S.firstPageRow q).cycles p ≅ (S.page 1).cycles (p, q) := by
  have hpRow : (ComplexShape.up ℤ).prev p = p - 1 :=
    (ComplexShape.up ℤ).prev_eq' (by change p - 1 + 1 = p; omega)
  have hnRow : (ComplexShape.up ℤ).next p = p + 1 :=
    (ComplexShape.up ℤ).next_eq' rfl
  have hpPage : (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).prev (p, q) = (p - 1, q) :=
    (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).prev_eq' (by
      change (p - 1, q) + (1, 0) = (p, q)
      ext <;> dsimp <;> omega)
  have hnPage : (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).next (p, q) = (p + 1, q) :=
    (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).next_eq' (by
      change (p, q) + (1, 0) = (p + 1, q)
      ext <;> dsimp <;> omega)
  exact (S.firstPageRow q).cyclesIsoSc' (p - 1) p (p + 1) hpRow hnRow ≪≫
    (ShortComplex.cyclesFunctor C).mapIso (S.firstPageRowShortComplexIso p q) ≪≫
      ((S.page 1).cyclesIsoSc' (p - 1, q) (p, q) (p + 1, q) hpPage hnPage).symm

/-- The row cycle comparison preserves the inclusion into the first page. -/
@[reassoc]
theorem firstPageRowCyclesIso_hom_i (p q : ℤ) :
    (S.firstPageRowCyclesIso p q).hom ≫ (S.page 1).iCycles (p, q) =
      (S.firstPageRow q).iCycles p := by
  dsimp only [firstPageRowCyclesIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, ShortComplex.cyclesFunctor]
  simp only [Category.assoc, HomologicalComplex.cyclesIsoSc'_inv_iCycles,
    ShortComplex.cyclesMap_i, firstPageRowShortComplexIso,
    ShortComplex.isoMk_hom_τ₂, Iso.refl_hom, Category.comp_id,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- The row homology comparison preserves the cycle quotient. -/
@[reassoc]
theorem firstPageRowCyclesIso_homologyπ (p q : ℤ) :
    (S.firstPageRow q).homologyπ p ≫ (S.firstPageRowHomologyIso p q).hom =
      (S.firstPageRowCyclesIso p q).hom ≫ (S.page 1).homologyπ (p, q) := by
  dsimp only [firstPageRowHomologyIso, firstPageRow, HomologicalComplex.restrictionHomologyIso,
    firstPageRowCyclesIso, firstPageRowShortComplexIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, ShortComplex.homologyFunctor,
    ShortComplex.cyclesFunctor]
  erw [HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.homologyπ_naturality_assoc,
    HomologicalComplex.π_homologyIsoSc'_inv]
  simp only [Category.assoc]
  dsimp only [HomologicalComplex.restriction.sc'Iso, ComplexShape.embeddingUpIntRow,
    ComplexShape.Embedding.mk', HomologicalComplex.sc', ShortComplex.isoMk]
  rfl

end CategoryTheory.SpectralSequence

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (Y : SpectralObject C EInt)

/-- The interval class maps to cycles of its first-page row. -/
def skeletalStepClassToRowCycles (p q : ℤ) :
    Y.stableIntervalStep (p + q) ((-p : ℤ) : EInt) ⟶
      ((Y.skeletalSpectralSequence).firstPageRow q).cycles p :=
  Y.skeletalStepClassToPageCycles 1 le_rfl p q ≫
    ((Y.skeletalSpectralSequence).firstPageRowCyclesIso p q).inv

/-- Including the row cycle recovers the first-page class map. -/
@[reassoc]
theorem skeletalStepClassToRowCycles_i (p q : ℤ) :
    Y.skeletalStepClassToRowCycles p q ≫
        ((Y.skeletalSpectralSequence).firstPageRow q).iCycles p =
      Y.skeletalStepClassToPage 1 le_rfl p q := by
  have hi : ((Y.skeletalSpectralSequence).firstPageRowCyclesIso p q).inv ≫
      ((Y.skeletalSpectralSequence).firstPageRow q).iCycles p =
      ((Y.skeletalSpectralSequence).page 1).iCycles (p, q) := by
    rw [← (Y.skeletalSpectralSequence).firstPageRowCyclesIso_hom_i]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  dsimp only [skeletalStepClassToRowCycles]
  erw [Category.assoc, hi, skeletalStepClassToPageCycles_i]

/-- The row homology comparison sends the cycle lift to the second-page class map. -/
@[reassoc]
theorem skeletalStepClassToRowCycles_homology (p q : ℤ) :
    Y.skeletalStepClassToRowCycles p q ≫
        ((Y.skeletalSpectralSequence).firstPageRow q).homologyπ p ≫
        ((Y.skeletalSpectralSequence).firstPageRowSecondPageIso p q).hom =
      Y.skeletalStepClassToPage 2 (by omega) p q := by
  dsimp only [skeletalStepClassToRowCycles,
    CategoryTheory.SpectralSequence.firstPageRowSecondPageIso, Iso.trans_hom]
  simp only [Category.assoc]
  rw [(Y.skeletalSpectralSequence).firstPageRowCyclesIso_homologyπ_assoc]
  simp only [Iso.inv_hom_id_assoc]
  exact Y.skeletalStepClassToPageCycles_homology 1 le_rfl p q

unseal spectralSequence in
/-- The first-page interval coordinate sends the class map to restriction to the middle interval. -/
@[reassoc]
theorem skeletalStepClassToPage_firstPage_hom (p q : ℤ) :
    Y.skeletalStepClassToPage 1 le_rfl p q ≫ (Y.skeletalFirstPageXIso (p, q)).hom =
      (Y.H (p + q)).map
        (twoδ₁Toδ₀
          (homOfLE (bot_le : (⊥ : EInt) ≤ ((-p - 1 : ℤ) : EInt)))
          (homOfLE (show ((-p - 1 : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp))
          (homOfLE (bot_le : (⊥ : EInt) ≤ ((-p : ℤ) : EInt))) (by subsingleton)) := by
  have h₀ : ((-p - 1 : ℤ) : EInt) = skeletalPageCore.i₀ 1 (p, q) le_rfl := rfl
  have h₁ : ((-(p + 1) : ℤ) : EInt) = skeletalPageCore.i₁ (p, q) := by
    dsimp only [skeletalPageCore]
    congr 1
    omega
  have h₂ : ((-p : ℤ) : EInt) = skeletalPageCore.i₂ (p, q) := rfl
  have h₃ : ((-p + 1 - 1 : ℤ) : EInt) = skeletalPageCore.i₃ 1 (p, q) le_rfl := rfl
  have h₁' : ((-p - 1 : ℤ) : EInt) = skeletalPageCore.i₁ (p, q) := rfl
  have hn : p + q = skeletalPageCore.deg (p, q) := rfl
  let W := Y.spectralSequencePageXIso skeletalPageCore 1 le_rfl (p, q)
    ((-p - 1 : ℤ) : EInt) ((-(p + 1) : ℤ) : EInt)
    ((-p : ℤ) : EInt) ((-p + 1 - 1 : ℤ) : EInt) h₀ h₁ h₂ h₃
    (p + q - 1) (p + q) (p + q + 1) hn (by omega) (by omega)
  let F := Y.spectralSequenceFirstPageXIso skeletalPageCore (p, q)
    ((-p - 1 : ℤ) : EInt) ((-p : ℤ) : EInt) h₁' h₂ (p + q) hn
  change (Y.stepClassToE (p + q)
      (show ((-p - 1 : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; omega)
      (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
      (show ((-p : ℤ) : EInt) ≤ ((-p + 1 - 1 : ℤ) : EInt) by simp) ≫ W.inv) ≫ F.hom = _
  dsimp only [W, F, spectralSequenceFirstPageXIso, spectralSequencePageXIso,
    CategoryTheory.Abelian.SpectralObject.SpectralSequence.pageXIso, Iso.trans_hom,
    spectralSequence, CategoryTheory.Abelian.SpectralObject.SpectralSequence.page,
    stepClassToE, stepClassToCycles, stableIntervalMiddle, stableIntervalLeft,
    stableIntervalLeftMiddle, stableIntervalRight, stableIntervalStep]
  generalize_proofs edgePf00 edgePf01 edgePf02 edgePf03 edgePf04 edgePf05
    edgePf06 edgePf07 edgePf08 edgePf09 edgePf10 edgePf11 edgePf12 edgePf13
    edgePf14 edgePf15 edgePf16 edgePf17 edgePf18 edgePf19 edgePf20 edgePf21
    edgePf22 edgePf23 edgePf24 edgePf25 edgePf26 edgePf27 edgePf28 edgePf29
    edgePf30 edgePf31 edgePf32 edgePf33 edgePf34 edgePf35
  generalize hb : -(p + 1) = b at *
  have hba : b = -p - 1 := by omega
  subst hba
  generalize hd : -p + 1 - 1 = d at *
  have hdc : d = -p := by omega
  subst hdc
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  let α₀ : mk₂ (homOfLE edgePf09) (homOfLE edgePf05) ⟶
      mk₂ (homOfLE edgePf04) (homOfLE edgePf05) :=
    homMk₂ (homOfLE (bot_le : (⊥ : EInt) ≤ ((-p - 1 : ℤ) : EInt)))
      (𝟙 ((-p - 1 : ℤ) : EInt)) (𝟙 ((-p : ℤ) : EInt))
      (by subsingleton) (by subsingleton)
  have hα :
      (homMk₂ (homOfLE edgePf11) (𝟙 ((-p - 1 : ℤ) : EInt)) (𝟙 ((-p : ℤ) : EInt))
        edgePf15 edgePf17 : mk₂ (homOfLE edgePf09) (homOfLE edgePf05) ⟶
          mk₂ (homOfLE edgePf04) (homOfLE edgePf05)) = α₀ := by subsingleton
  erw [hα]
  simpa only [stepClassToE, stepClassToCycles, stableIntervalStep,
    stableIntervalLeftMiddle, α₀, Category.assoc] using
    Y.stepClassToE_identity_hom (p + q)
      (show ((-p - 1 : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)

end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (Y : SpectralObject C EInt)

/-- The class map to cycles in row zero, with total degree transported along `n + 0 = n`. -/
def skeletalStepClassToZeroRowCycles (n : ℤ) :
    Y.stableIntervalStep n ((-n : ℤ) : EInt) ⟶
      ((Y.skeletalSpectralSequence).firstPageRow 0).cycles n :=
  (eqToIso (congrArg (fun k => (Y.H k).obj
    (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((-n : ℤ) : EInt))))) (add_zero n))).inv ≫
    Y.skeletalStepClassToRowCycles n 0

/-- The interval coordinate for row zero, with total degree transported along `n + 0 = n`. -/
def skeletalFirstPageZeroRowCutIso (n : ℤ) :
    ((Y.skeletalSpectralSequence).firstPageRow 0).X n ≅
      (Y.H n).obj (mk₁
        (homOfLE (show ((-n - 1 : ℤ) : EInt) ≤ ((-n : ℤ) : EInt) by simp))) :=
  Y.skeletalFirstPageXIso (n, 0) ≪≫
    eqToIso (congrArg
      (fun k => (Y.H k).obj (mk₁
        (homOfLE (show ((-n - 1 : ℤ) : EInt) ≤ ((-n : ℤ) : EInt) by simp)))) (add_zero n))

private theorem cohomologyDegreeTransportMap (k n : ℤ) (h : k = n)
    (a b : ComposableArrows EInt 1) (f : a ⟶ b) :
    (eqToIso (congrArg (fun j => (Y.H j).obj a) h)).inv ≫ (Y.H k).map f ≫
        (eqToIso (congrArg (fun j => (Y.H j).obj b) h)).hom = (Y.H n).map f := by
  subst n
  simp only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

/-- The row-zero class map followed by the interval coordinate equals restriction to the middle interval. -/
@[reassoc]
theorem skeletalStepClassToZeroRowCycles_i_cut (n : ℤ) :
    Y.skeletalStepClassToZeroRowCycles n ≫
        ((Y.skeletalSpectralSequence).firstPageRow 0).iCycles n ≫
        (Y.skeletalFirstPageZeroRowCutIso n).hom =
      (Y.H n).map (twoδ₁Toδ₀
        (homOfLE (bot_le : (⊥ : EInt) ≤ ((-n - 1 : ℤ) : EInt)))
        (homOfLE (show ((-n - 1 : ℤ) : EInt) ≤ ((-n : ℤ) : EInt) by simp))
        (homOfLE (bot_le : (⊥ : EInt) ≤ ((-n : ℤ) : EInt))) (by subsingleton)) := by
  dsimp only [skeletalStepClassToZeroRowCycles, skeletalFirstPageZeroRowCutIso, Iso.trans_hom]
  simp only [Category.assoc]
  rw [Y.skeletalStepClassToRowCycles_i_assoc, Y.skeletalStepClassToPage_firstPage_hom_assoc]
  dsimp only [stableIntervalStep, stableIntervalLeftMiddle]
  exact cohomologyDegreeTransportMap Y (n + 0) n (add_zero n) _ _ _

/-- The row-zero cycle inclusion equals interval restriction followed by the inverse coordinate map. -/
@[reassoc]
theorem skeletalStepClassToZeroRowCycles_i (n : ℤ) :
    Y.skeletalStepClassToZeroRowCycles n ≫ ((Y.skeletalSpectralSequence).firstPageRow 0).iCycles n =
      (Y.H n).map (twoδ₁Toδ₀
        (homOfLE (bot_le : (⊥ : EInt) ≤ ((-n - 1 : ℤ) : EInt)))
        (homOfLE (show ((-n - 1 : ℤ) : EInt) ≤ ((-n : ℤ) : EInt) by simp))
        (homOfLE (bot_le : (⊥ : EInt) ≤ ((-n : ℤ) : EInt))) (by subsingleton)) ≫
        (Y.skeletalFirstPageZeroRowCutIso n).inv := by
  apply (cancel_mono (Y.skeletalFirstPageZeroRowCutIso n).hom).mp
  erw [Category.assoc, Y.skeletalStepClassToZeroRowCycles_i_cut]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.Abelian.SpectralObject


end
