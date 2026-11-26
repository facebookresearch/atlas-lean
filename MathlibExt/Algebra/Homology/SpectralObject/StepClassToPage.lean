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
# Interval step classes on spectral pages

For a spectral object over a bounded preorder, bottom-to-cut classes H_n(⊥,c) map to interval
cycles and their four-cut E quotients. These maps commute with outer-cut changes. Under
H_{n+1}(⊥,a)=0 and H_{n−1}(d,⊤)=0, padding identifies their finite representatives with stable
classes and kernel-filtration graded quotients.

For EInt indices, the page map at (p,q) uses total degree p+q and cut −p, with page-r window
cuts −p−r,−p−1,−p,−p+r−1. It lifts to page cycles and is compatible with successor homology,
first-page row homology, and the later single-row collapse comparisons. All integer degrees
and index universe roles are retained.
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

/-- The map from a bottom-to-cut class to interval cycles.

For a≤b≤c, map H_n(⊥,c) to the cycles associated to a→b→c through interval restriction. -/
def stepClassToCycles (n : ℤ) {a b c : ι} (hab : a ≤ b) (hbc : b ≤ c) :
    Y.stableIntervalStep n c ⟶
      Y.cycles (homOfLE hab) (homOfLE hbc) n :=
  Y.toCycles (homOfLE (bot_le : (⊥ : ι) ≤ b)) (homOfLE hbc)
      (homOfLE (bot_le : (⊥ : ι) ≤ c)) (by subsingleton) n ≫
    Y.cyclesMap (homOfLE (bot_le : (⊥ : ι) ≤ b)) (homOfLE hbc)
      (homOfLE hab) (homOfLE hbc)
      (homMk₂ (homOfLE (bot_le : (⊥ : ι) ≤ a)) (𝟙 b) (𝟙 c)
        (by subsingleton) (by subsingleton)) n


-- Keep the original hypothesis parameters and their order in this compatibility declaration.
/-- The step-class lift preserves its interval component.

The cycle lift followed by cycle inclusion equals the H_n map from the bottom-to-cut interval
to b→c. -/
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

/-- The map from step classes to a four-cut quotient.

For a≤b≤c≤d, lift the class to cycles and project to E(a,b,c,d;n). -/
def stepClassToE (n : ℤ) {a b c d : ι}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    Y.stableIntervalStep n c ⟶
      Y.E (homOfLE hab) (homOfLE hbc) (homOfLE hcd)
        (n - 1) n (n + 1) (by omega) (by omega) :=
  Y.stepClassToCycles n hab hbc ≫
    Y.πE (homOfLE hab) (homOfLE hbc) (homOfLE hcd)
      (n - 1) n (n + 1) (by omega) (by omega)

/-- The step-class cycle lift commutes with the left-cut map.

Moving a smaller left cut a′ to a carries its cycle lift to the lift at a. -/
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

/-- The step-class quotient map commutes with the left-cut map.

The four-cut map from a′ to a carries the step-class representative to that with left cut a. -/
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


-- Keep the original hypothesis parameters and their order in this compatibility declaration.
/-- The step-class quotient map commutes with enlarging the right cut.

Moving d to d′ carries the class map to the representative for the enlarged interval. -/
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

/-- The step-class quotient map with extreme outer cuts.

At outer cuts ⊥ and ⊤, the map is the stable interval step-to-stable map. -/
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

/-- The step-class map under endpoint padding.

If H_{n+1}(⊥,a)=0 and H_{n−1}(d,⊤)=0, padding the finite window to the stable interval
preserves the step-class map. -/
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

/-- The step-class map in a kernel-filtration graded quotient.

Under the endpoint vanishing hypotheses, the finite-window comparison gives the step-to-image
map followed by the kernel-image identification and the graded quotient projection. -/
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

/-- The step-class map when both outer arrows are identities.

The E-to-H comparison identifies the map with the corresponding bottom-to-cut H_n interval
map. -/
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

/-- The step-class map to a skeletal spectral page.

At (p,q), map H_{p+q}(⊥,−p) through the cuts −p−r,−p−1,−p,−p+r−1 to E_r^{p,q}. -/
def skeletalStepClassToPage (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    Y.stableIntervalStep (p + q) ((-p : ℤ) : EInt) ⟶
      ((Y.skeletalSpectralSequence).page r hr).X (p, q) :=
  Y.stepClassToE (p + q)
      (show ((-p - r : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; omega)
      (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
      (show ((-p : ℤ) : EInt) ≤ ((-p + r - 1 : ℤ) : EInt) by simp; omega) ≫
    (Y.skeletalPageWindowIso r hr p q).inv

/-- The step-class map through the successor cycle inclusion.

The expanded lower-window representative followed by the successor cycle inclusion is the
page-r class map. -/
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

/-- The step-class map through the successor homology projection.

The expanded representative projected to successor homology and then to page r+1 is the
page-(r+1) class map. -/
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

/-- Step classes are cycles on the skeletal page.

The step-class map to E_r^{p,q} is killed by the outgoing page differential. -/
@[reassoc]
theorem skeletalStepClassToPage_g (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    Y.skeletalStepClassToPage r hr p q ≫
        (((Y.skeletalSpectralSequence).page r hr).sc (p, q)).g = 0 := by
  rw [← Y.skeletalStepClassToPage_successor_i r hr p q, Category.assoc,
    (Y.skeletalSuccessorHomologyData r hr p q).left.wi, comp_zero]

/-- The step-class page map respects equality of page indices.

Transport along r=r′ carries the page-r map to the page-r′ map. -/
@[reassoc]
theorem skeletalStepClassToPage_cast (r r' : ℤ) (h : r = r') (hr : 1 ≤ r) (p q : ℤ) :
    Y.skeletalStepClassToPage r hr p q ≫
        ((Y.skeletalSpectralSequence).pageXIsoOfEq (p, q) r r' h hr).hom =
      Y.skeletalStepClassToPage r' (by omega) p q := by
  subst r'
  simp only [CategoryTheory.SpectralSequence.pageXIsoOfEq, eqToIso_refl,
    Iso.refl_hom, Category.comp_id]

/-- Step-class maps commute with a single-row successor isomorphism.

Under first-page row-zero support and r≥2, the canonical page successor carries the step-class
map to that at r+1. -/
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

/-- The step-class lift into skeletal page cycles.

Use the expanded lower window and successor cycle comparison to lift H_{p+q}(⊥,−p) into page-r
cycles. -/
def skeletalStepClassToPageCycles (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    Y.stableIntervalStep (p + q) ((-p : ℤ) : EInt) ⟶
      ((Y.skeletalSpectralSequence).page r hr).cycles (p, q) :=
  Y.stepClassToE (p + q)
      (show ((-p - (r + 1) : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; omega)
      (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
      (show ((-p : ℤ) : EInt) ≤ ((-p + r - 1 : ℤ) : EInt) by simp; omega) ≫
    (Y.skeletalSuccessorHomologyData r hr p q).left.cyclesIso.inv

/-- The step-class cycle lift recovers the page class map.

Cycle inclusion composed after the lift equals skeletalStepClassToPage. -/
@[reassoc]
theorem skeletalStepClassToPageCycles_i (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    Y.skeletalStepClassToPageCycles r hr p q ≫
        ((Y.skeletalSpectralSequence).page r hr).iCycles (p, q) =
      Y.skeletalStepClassToPage r hr p q := by
  dsimp only [skeletalStepClassToPageCycles, HomologicalComplex.iCycles]
  erw [Category.assoc,
    (Y.skeletalSuccessorHomologyData r hr p q).left.cyclesIso_inv_comp_iCycles]
  exact Y.skeletalStepClassToPage_successor_i r hr p q

/-- The step-class cycle lift gives the next-page class.

The cycle lift followed by homology projection and the successor isomorphism equals the
page-(r+1) class map. -/
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

/-- Step-class maps commute with finite single-row successor composites.

The E₂ class map transported to page k+2 equals the class map defined on that page. -/
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

/-- Step-class maps commute with every later single-row comparison.

Under row-zero support, the E₂-to-E_r isomorphism preserves the class map for r≥2. -/
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

/-- The three-term comparison of a first-page row.

The row complex at p−1,p,p+1 is identified by identity components with the page complex at
(p−1,q),(p,q),(p+1,q). -/
def firstPageRowShortComplexIso (p q : ℤ) :
    (S.firstPageRow q).sc' (p - 1) p (p + 1) ≅
      (S.page 1).sc' (p - 1, q) (p, q) (p + 1, q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- The cycles comparison of a first-page row.

Identify degree-p row cycles with first-page cycles at (p,q) through the three-term
comparison. -/
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

/-- The row-cycle comparison preserves inclusion.

The forward row-cycle comparison followed by page cycle inclusion equals the row cycle
inclusion. -/
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

/-- The row-cycle comparison preserves homology projection.

Row homology projection followed by its comparison equals the row-cycle comparison followed by
page homology projection. -/
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

/-- The step-class map to a first-page row's cycles.

Lift the skeletal first-page class at (p,q) and use the row-cycle comparison to obtain
degree-p row cycles. -/
def skeletalStepClassToRowCycles (p q : ℤ) :
    Y.stableIntervalStep (p + q) ((-p : ℤ) : EInt) ⟶
      ((Y.skeletalSpectralSequence).firstPageRow q).cycles p :=
  Y.skeletalStepClassToPageCycles 1 le_rfl p q ≫
    ((Y.skeletalSpectralSequence).firstPageRowCyclesIso p q).inv

/-- The row-cycle step-class map recovers the first-page map.

Including the row cycles gives the skeletal page-1 class map. -/
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

/-- The row-cycle step-class map gives its second-page class.

The row homology projection and row-to-E₂ comparison carry the lift to the skeletal page-2
class map. -/
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
/-- The first-page class map in its short-interval coordinate.

The first-page chart identifies the class map with H_{p+q}(⊥,−p) → H_{p+q}(−p−1,−p). -/
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

/-- The zero-row step-class lift with explicit total degree.

For n∈ℤ, transport n+0 to n and lift H_n(⊥,−n) into degree-n cycles of row zero. -/
def skeletalStepClassToZeroRowCycles (n : ℤ) :
    Y.stableIntervalStep n ((-n : ℤ) : EInt) ⟶
      ((Y.skeletalSpectralSequence).firstPageRow 0).cycles n :=
  (eqToIso (congrArg (fun k => (Y.H k).obj
    (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ((-n : ℤ) : EInt))))) (add_zero n))).inv ≫
    Y.skeletalStepClassToRowCycles n 0

/-- The zero-row first-page object as a short interval.

Identify its degree-n object with H_n(−n−1,−n), retaining the n+0=n transport. -/
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

/-- The zero-row cycle lift in the short-cut coordinate.

Cycle inclusion followed by the cut isomorphism equals the bottom-to-cut interval map. -/
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

/-- The zero-row cycle lift recovers the cut class representative.

The interval map followed by the inverse cut chart equals the cycle lift followed by
inclusion. -/
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
