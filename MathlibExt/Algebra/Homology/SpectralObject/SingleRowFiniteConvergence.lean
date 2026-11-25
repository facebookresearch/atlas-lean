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

public import MathlibExt.Algebra.Homology.SpectralSequence.SingleRow
public import MathlibExt.CategoryTheory.Subobject.FiniteFiltrationSingleGrade
public import MathlibExt.Algebra.Homology.SpectralObject.FiniteStripSuccessor
public import MathlibExt.Algebra.Homology.GenericSpectralSequenceMapCompatibility

/-!
# Finite convergence for single-row spectral objects

For a spectral object with vanishing endpoint intervals and a first page
supported in row zero, the second page is canonically its full endpoint
object. The comparison uses the original page successors and subobject
filtration, is independent of the finite bound, and is natural for
morphisms of spectral objects.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Abelian.SpectralObject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (Y : SpectralObject C EInt)

/-- Actual finite convergence transports the ordinary row support to the endpoint restriction graded. -/
theorem isZero_skeletalAbutmentGraded_of_singleRow
    (N : ℕ)
    (hfull : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hempty : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((Y.skeletalSpectralSequence.page 1).X (p, q)))
    (n p : ℤ) (hpn : p ≠ n) : IsZero (Y.skeletalAbutmentGraded n p) := by
  let e : ((Y.skeletalSpectralSequence).page ((N : ℤ) + 2) (by omega)).X (p, n - p) ≅
      Y.skeletalAbutmentGraded n p :=
    Y.finiteSkeletalPageGradedIso N hfull hempty ((N : ℤ) + 2) (by omega) p (n - p) ≪≫
      eqToIso (congrArg (fun z => Y.skeletalAbutmentGraded z p) (by omega : p + (n - p) = n))
  exact ((Y.skeletalSpectralSequence).isZero_page_of_firstPage_off_row
    hrow ((N : ℤ) + 2) (by omega) p (n - p) (by omega)).of_iso e.symm

/-- The actual ordinary second page compared to the endpoint graded at an arbitrary later native page. -/
def singleRowFiniteSecondPageGradedIsoAtNatPage
    (N : ℕ)
    (hfull : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hempty : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((Y.skeletalSpectralSequence.page 1).X (p, q)))
    (K : ℕ) (hK : N ≤ K) (p q : ℤ) :
    ((Y.skeletalSpectralSequence).page 2).X (p, q) ≅ Y.skeletalAbutmentGraded (p + q) p :=
  (Y.skeletalSpectralSequence).singleRowPageIsoNat hrow (p, q) K ≪≫
    Y.finiteSkeletalPageGradedIso N hfull hempty ((K : ℤ) + 2) (by omega) p q

private theorem finiteSkeletalPageGradedIso_pageCast
    (N : ℕ)
    (hfull : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hempty : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (r r' : ℤ) (h : r = r') (hr : (N : ℤ) + 1 ≤ r) (p q : ℤ) :
    ((Y.skeletalSpectralSequence).pageXIsoOfEq (p, q) r r' h (by omega)).hom ≫
        (Y.finiteSkeletalPageGradedIso N hfull hempty r' (by omega) p q).hom =
      (Y.finiteSkeletalPageGradedIso N hfull hempty r hr p q).hom := by
  subst r'
  simp only [CategoryTheory.SpectralSequence.pageXIsoOfEq, eqToIso_refl,
    Iso.refl_hom, Category.id_comp]

private theorem singleRowFiniteSecondPageGradedIsoAtNatPage_hom_succ
    (N : ℕ)
    (hfull : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hempty : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((Y.skeletalSpectralSequence.page 1).X (p, q)))
    (K : ℕ) (hK : N ≤ K) (p q : ℤ) :
    (Y.singleRowFiniteSecondPageGradedIsoAtNatPage N hfull hempty hrow K hK p q).hom =
      (Y.singleRowFiniteSecondPageGradedIsoAtNatPage N hfull hempty hrow (K + 1) (by omega) p q).hom := by
  let S := Y.skeletalSpectralSequence
  have hs : S.singleRowSuccessorIso hrow ((K : ℤ) + 2) (by omega) (p, q) =
      Y.finiteSkeletalSuccessorIso N hfull hempty ((K : ℤ) + 2) (by omega) (p, q) := rfl
  change (S.singleRowPageIsoNat hrow (p, q) K).hom ≫
      (Y.finiteSkeletalPageGradedIso N hfull hempty ((K : ℤ) + 2) (by omega) p q).hom =
    ((S.singleRowPageIsoNat hrow (p, q) K).hom ≫
      (S.singleRowSuccessorIso hrow ((K : ℤ) + 2) (by omega) (p, q)).hom ≫
        (S.pageXIsoOfEq (p, q) (((K : ℤ) + 2) + 1) (((K + 1 : ℕ) : ℤ) + 2)
          (by omega) (by omega)).hom) ≫
      (Y.finiteSkeletalPageGradedIso N hfull hempty (((K + 1 : ℕ) : ℤ) + 2) (by omega) p q).hom
  simp only [Category.assoc]
  rw [Y.finiteSkeletalPageGradedIso_pageCast N hfull hempty
      (((K : ℤ) + 2) + 1) (((K + 1 : ℕ) : ℤ) + 2) (by omega) (by omega) p q,
    hs, Y.finiteSkeletalSuccessorIso_comp_graded N hfull hempty ((K : ℤ) + 2) (by omega) p q]

/-- The ordinary graded comparison is unchanged when the actual late native page is increased. -/
theorem singleRowFiniteSecondPageGradedIsoAtNatPage_hom_eq_of_le
    (N : ℕ)
    (hfull : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hempty : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((Y.skeletalSpectralSequence.page 1).X (p, q)))
    (K : ℕ) (hK : N ≤ K) (p q : ℤ) :
    (Y.singleRowFiniteSecondPageGradedIsoAtNatPage N hfull hempty hrow K hK p q).hom =
      (Y.singleRowFiniteSecondPageGradedIsoAtNatPage N hfull hempty hrow N le_rfl p q).hom := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, K = N + d := ⟨K - N, by omega⟩
  subst K
  induction d with
  | zero => rfl
  | succ d ih =>
    have hs := Y.singleRowFiniteSecondPageGradedIsoAtNatPage_hom_succ
      N hfull hempty hrow (N + d) (by omega) p q
    simpa only [Nat.add_assoc] using hs.symm.trans (ih (by omega))

/-- The ordinary second-page graded comparison is independent of the genuine finite dimension bound. -/
theorem singleRowFiniteSecondPageGradedIsoAtNatPage_hom_eq_of_bounds
    (N M : ℕ)
    (hfullN : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hfullM : ∀ n i : ℤ, i ≤ -(M : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hempty : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((Y.skeletalSpectralSequence.page 1).X (p, q)))
    (p q : ℤ) :
    (Y.singleRowFiniteSecondPageGradedIsoAtNatPage N hfullN hempty hrow N le_rfl p q).hom =
      (Y.singleRowFiniteSecondPageGradedIsoAtNatPage M hfullM hempty hrow M le_rfl p q).hom := by
  calc
    _ = (Y.singleRowFiniteSecondPageGradedIsoAtNatPage N hfullN hempty hrow (N + M) (by omega) p q).hom :=
      (Y.singleRowFiniteSecondPageGradedIsoAtNatPage_hom_eq_of_le
        N hfullN hempty hrow (N + M) (by omega) p q).symm
    _ = (Y.singleRowFiniteSecondPageGradedIsoAtNatPage M hfullM hempty hrow (N + M) (by omega) p q).hom := by
      dsimp only [singleRowFiniteSecondPageGradedIsoAtNatPage, Iso.trans_hom]
      rw [Y.finiteSkeletalPageGradedIso_eq_of_bounds N M hfullN hfullM hempty
        (((N + M : ℕ) : ℤ) + 2) (by omega) (by omega) p q]
    _ = _ := Y.singleRowFiniteSecondPageGradedIsoAtNatPage_hom_eq_of_le
      M hfullM hempty hrow (N + M) (by omega) p q

/-- At a specified finite skeletal bound, the ordinary second page is the actual full endpoint object. -/
def singleRowFiniteSecondPageAbutmentIso
    (N : ℕ)
    (hfull : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hempty : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((Y.skeletalSpectralSequence.page 1).X (p, q)))
    (n : ℤ) :
    ((Y.skeletalSpectralSequence).page 2).X (n, 0) ≅ Y.stableIntervalAbutment n := by
  let hz (p : ℤ) (hpn : p ≠ n) : IsZero (Y.skeletalAbutmentGraded n p) :=
    Y.isZero_skeletalAbutmentGraded_of_singleRow N hfull hempty hrow n p hpn
  obtain ⟨h₀, hN⟩ := Y.skeletalAbutmentFiltration_endpoints N hfull hempty n
  exact Y.singleRowFiniteSecondPageGradedIsoAtNatPage N hfull hempty hrow N le_rfl n 0 ≪≫
    eqToIso (congrArg (fun z => Y.skeletalAbutmentGraded z n) (by omega : n + 0 = n)) ≪≫
      Subobject.finiteFiltrationSingleGradeIso (Y.skeletalAbutmentFiltration n)
        (Y.skeletalAbutmentFiltration_antitone n) N h₀ hN n hz

/-- The actual ordinary second-page comparison with the full endpoint is independent of its finite bound. -/
theorem singleRowFiniteSecondPageAbutmentIso_hom_eq_of_bounds
    (N M : ℕ)
    (hfullN : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hfullM : ∀ n i : ℤ, i ≤ -(M : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hempty : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((Y.skeletalSpectralSequence.page 1).X (p, q)))
    (n : ℤ) :
    (Y.singleRowFiniteSecondPageAbutmentIso N hfullN hempty hrow n).hom =
      (Y.singleRowFiniteSecondPageAbutmentIso M hfullM hempty hrow n).hom := by
  have hs := Y.singleRowFiniteSecondPageGradedIsoAtNatPage_hom_eq_of_bounds
    N M hfullN hfullM hempty hrow n 0
  dsimp only [singleRowFiniteSecondPageAbutmentIso, Iso.trans_hom]
  rw [hs]
  rfl

variable {Y}
variable {Z : SpectralObject C EInt}

namespace Hom

private theorem skeletalAbutmentGradedMap_degreeCast (φ : Y ⟶ Z)
    (n n' : ℤ) (h : n = n') (p : ℤ) :
    φ.skeletalAbutmentGradedMap n p ≫
        (eqToIso (congrArg (fun z => Z.skeletalAbutmentGraded z p) h)).hom =
      (eqToIso (congrArg (fun z => Y.skeletalAbutmentGraded z p) h)).hom ≫
        φ.skeletalAbutmentGradedMap n' p := by
  subst n'
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- The actual ordinary second-page graded comparison is natural for native spectral-object maps. -/
@[reassoc]
theorem singleRowFiniteSecondPageGradedIsoAtNatPage_naturality
    (φ : Y ⟶ Z) (N : ℕ)
    (hfullY : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hemptyY : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (hfullZ : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Z.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hemptyZ : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Z.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (hrowY : ∀ p q : ℤ, q ≠ 0 → IsZero ((Y.skeletalSpectralSequence.page 1).X (p, q)))
    (hrowZ : ∀ p q : ℤ, q ≠ 0 → IsZero ((Z.skeletalSpectralSequence.page 1).X (p, q)))
    (K : ℕ) (hK : N ≤ K) (p q : ℤ) :
    ((φ.spectralSequenceMap skeletalPageCore).hom 2).f (p, q) ≫
        (Z.singleRowFiniteSecondPageGradedIsoAtNatPage N hfullZ hemptyZ hrowZ K hK p q).hom =
      (Y.singleRowFiniteSecondPageGradedIsoAtNatPage N hfullY hemptyY hrowY K hK p q).hom ≫
        φ.skeletalAbutmentGradedMap (p + q) p := by
  dsimp only [singleRowFiniteSecondPageGradedIsoAtNatPage, Iso.trans_hom]
  rw [← Category.assoc,
    (φ.spectralSequenceMap skeletalPageCore).singleRowPageIsoNat_naturality hrowY hrowZ,
    Category.assoc, spectralSequenceMap_hom,
    φ.finiteSkeletalPageGradedIso_naturality N hfullY hemptyY hfullZ hemptyZ
      ((K : ℤ) + 2) (by omega) p q,
    ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary second-page comparison is natural for the actual map of full endpoint intervals. -/
@[reassoc]
theorem singleRowFiniteSecondPageAbutmentIso_naturality
    (φ : Y ⟶ Z) (N : ℕ)
    (hfullY : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hemptyY : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Y.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (hfullZ : ∀ n i : ℤ, i ≤ -(N : ℤ) - 1 →
      IsZero ((Z.H n).obj (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hemptyZ : ∀ n i : ℤ, 0 ≤ i →
      IsZero ((Z.H n).obj (ComposableArrows.mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (hrowY : ∀ p q : ℤ, q ≠ 0 → IsZero ((Y.skeletalSpectralSequence.page 1).X (p, q)))
    (hrowZ : ∀ p q : ℤ, q ≠ 0 → IsZero ((Z.skeletalSpectralSequence.page 1).X (p, q)))
    (n : ℤ) :
    ((φ.spectralSequenceMap skeletalPageCore).hom 2).f (n, 0) ≫
        (Z.singleRowFiniteSecondPageAbutmentIso N hfullZ hemptyZ hrowZ n).hom =
      (Y.singleRowFiniteSecondPageAbutmentIso N hfullY hemptyY hrowY n).hom ≫
        (φ.hom n).app (ComposableArrows.mk₁ (stableIntervalFull (ι := EInt))) := by
  let aY : ((Y.skeletalSpectralSequence).page 2).X (n, 0) ≅ Y.skeletalAbutmentGraded n n :=
    Y.singleRowFiniteSecondPageGradedIsoAtNatPage N hfullY hemptyY hrowY N le_rfl n 0 ≪≫
      eqToIso (congrArg (fun z => Y.skeletalAbutmentGraded z n) (by omega : n + 0 = n))
  let aZ : ((Z.skeletalSpectralSequence).page 2).X (n, 0) ≅ Z.skeletalAbutmentGraded n n :=
    Z.singleRowFiniteSecondPageGradedIsoAtNatPage N hfullZ hemptyZ hrowZ N le_rfl n 0 ≪≫
      eqToIso (congrArg (fun z => Z.skeletalAbutmentGraded z n) (by omega : n + 0 = n))
  let cY : Y.skeletalAbutmentGraded n n ≅ Y.stableIntervalAbutment n :=
    Subobject.finiteFiltrationSingleGradeIso (Y.skeletalAbutmentFiltration n)
      (Y.skeletalAbutmentFiltration_antitone n) N
      (Y.skeletalAbutmentFiltration_eq_top hemptyY n 0 (by omega))
      (Y.skeletalAbutmentFiltration_eq_bot N hfullY n ((N : ℤ) + 1) (by omega)) n
      (Y.isZero_skeletalAbutmentGraded_of_singleRow N hfullY hemptyY hrowY n)
  let cZ : Z.skeletalAbutmentGraded n n ≅ Z.stableIntervalAbutment n :=
    Subobject.finiteFiltrationSingleGradeIso (Z.skeletalAbutmentFiltration n)
      (Z.skeletalAbutmentFiltration_antitone n) N
      (Z.skeletalAbutmentFiltration_eq_top hemptyZ n 0 (by omega))
      (Z.skeletalAbutmentFiltration_eq_bot N hfullZ n ((N : ℤ) + 1) (by omega)) n
      (Z.isZero_skeletalAbutmentGraded_of_singleRow N hfullZ hemptyZ hrowZ n)
  have ha : ((φ.spectralSequenceMap skeletalPageCore).hom 2).f (n, 0) ≫ aZ.hom =
      aY.hom ≫ φ.skeletalAbutmentGradedMap n n := by
    dsimp only [aY, aZ, Iso.trans_hom]
    rw [← Category.assoc,
      φ.singleRowFiniteSecondPageGradedIsoAtNatPage_naturality
        N hfullY hemptyY hfullZ hemptyZ hrowY hrowZ N le_rfl n 0,
      Category.assoc, φ.skeletalAbutmentGradedMap_degreeCast (n + 0) n (by omega) n,
      ← Category.assoc]
  let πY : (Y.skeletalAbutmentFiltration n n : C) ⟶ Y.skeletalAbutmentGraded n n :=
    cokernel.π (Subobject.ofLE _ _
      (Y.skeletalAbutmentFiltration_antitone n (show n ≤ n + 1 by omega)))
  let πZ : (Z.skeletalAbutmentFiltration n n : C) ⟶ Z.skeletalAbutmentGraded n n :=
    cokernel.π (Subobject.ofLE _ _
      (Z.skeletalAbutmentFiltration_antitone n (show n ≤ n + 1 by omega)))
  let a : (Y.skeletalAbutmentFiltration n n : C) ⟶ (Z.skeletalAbutmentFiltration n n : C) :=
    φ.skeletalAbutmentFiltrationMap n n
  have hπY : πY ≫ cY.hom =
      (Y.skeletalAbutmentFiltration n n).arrow :=
    Subobject.finiteFiltrationSingleGradeIso_π _ _ _ _ _ _ _
  have hπZ : πZ ≫ cZ.hom =
      (Z.skeletalAbutmentFiltration n n).arrow :=
    Subobject.finiteFiltrationSingleGradeIso_π _ _ _ _ _ _ _
  have hπnat : πY ≫ φ.skeletalAbutmentGradedMap n n = a ≫ πZ := by
    exact φ.stableIntervalKernelGradedMap_π n
      (show ((-(n + 1) : ℤ) : EInt) ≤ ((-n : ℤ) : EInt) by simp)
  have hc : φ.skeletalAbutmentGradedMap n n ≫ cZ.hom = cY.hom ≫
      (φ.hom n).app (ComposableArrows.mk₁ (stableIntervalFull (ι := EInt))) := by
    haveI : Epi πY := by dsimp only [πY]; infer_instance
    apply (cancel_epi πY).1
    rw [← Category.assoc, hπnat, Category.assoc, hπZ, ← Category.assoc, hπY]
    exact φ.stableIntervalKernelMap_arrow n ((-n : ℤ) : EInt)
  have hY : (Y.singleRowFiniteSecondPageAbutmentIso N hfullY hemptyY hrowY n).hom =
      aY.hom ≫ cY.hom := by
    dsimp only [singleRowFiniteSecondPageAbutmentIso, aY, cY, Iso.trans_hom]
    simp only [Category.assoc]
  have hZ : (Z.singleRowFiniteSecondPageAbutmentIso N hfullZ hemptyZ hrowZ n).hom =
      aZ.hom ≫ cZ.hom := by
    dsimp only [singleRowFiniteSecondPageAbutmentIso, aZ, cZ, Iso.trans_hom]
    simp only [Category.assoc]
  rw [hZ, hY, ← Category.assoc, ha, Category.assoc, hc, ← Category.assoc]

end Hom

end CategoryTheory.Abelian.SpectralObject
