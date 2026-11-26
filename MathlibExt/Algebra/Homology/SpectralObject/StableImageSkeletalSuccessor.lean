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

public import MathlibExt.Algebra.Homology.SpectralObject.StableImageNaturality
public import MathlibExt.Algebra.Homology.SpectralObject.FiniteStripSuccessor

/-!
# Skeletal successors and stable-image convergence

For an EInt-indexed abelian-group spectral object S, vanishing of the
incoming and outgoing differentials at a position (p,q) on page r gives
the canonical zero-differential successor E_r^{p,q} ≅ E_{r+1}^{p,q}.
It preserves the cycle inclusion and homology projection of the page's
successor datum.

Fix the skeletal left cuts a_k=−p−1−k. If the full-endpoint cone is
limiting, the restriction-kernel tower is Mittag–Leffler, and its eventual
image is attained at R and R+1, the stable-image comparisons at the two
consecutive pages commute with this successor. The hypotheses also include
the two stated right-interval vanishings and the incoming/outgoing
differential vanishings at the old page position.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows Opposite

universe u

namespace CategoryTheory.Abelian.SpectralObject

variable (S : SpectralObject AddCommGrpCat.{u} EInt)

/-- Let S be an EInt-indexed abelian-group spectral object and r≥1.
If the incoming and outgoing differentials of the page-r short complex
at (p,q) are zero, the canonical isomorphism E_r^{p,q} ≅ E_{r+1}^{p,q}
is the zero-differential homology identification followed by the
spectral-sequence successor. -/
def stableImageSkeletalSuccessorIso (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hf : ((S.skeletalSpectralSequence.page r hr).sc (p, q)).f = 0)
    (hg : ((S.skeletalSpectralSequence.page r hr).sc (p, q)).g = 0) :
    (S.skeletalSpectralSequence.page r hr).X (p, q) ≅
      (S.skeletalSpectralSequence.page (r + 1) (by omega)).X (p, q) :=
  (ShortComplex.HomologyData.ofZeros
    ((S.skeletalSpectralSequence.page r hr).sc (p, q)) hf hg).left.homologyIso.symm ≪≫
      S.skeletalSpectralSequence.iso r (r + 1) (p, q) rfl hr

/-- Let S be an EInt-indexed abelian-group spectral object, r≥1 and
(p,q) a position whose incoming and outgoing page-r differentials
are zero. For the cycle inclusion i_h and homology projection π_h
of its successor datum, the successor followed by the new-page
window comparison sends i_h to π_h. -/
theorem stableImageSkeletalSuccessorIso_i (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hf : ((S.skeletalSpectralSequence.page r hr).sc (p, q)).f = 0)
    (hg : ((S.skeletalSpectralSequence.page r hr).sc (p, q)).g = 0) :
    (S.skeletalSuccessorHomologyData r hr p q).left.i ≫
        (S.stableImageSkeletalSuccessorIso r hr p q hf hg).hom ≫
        (S.skeletalPageWindowIso (r + 1) (by omega) p q).hom =
      (S.skeletalSuccessorHomologyData r hr p q).left.π := by
  dsimp only [stableImageSkeletalSuccessorIso, Iso.trans_hom, Iso.symm_hom]
  rw [S.skeletalSequence_iso_eq_successorHomologyData]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact ShortComplex.LeftHomologyData.i_comp_zeroHomologyIso _
    (S.skeletalSuccessorHomologyData r hr p q).left hf hg

/-- Let S be an EInt-indexed abelian-group spectral object. Fix n, antitone
left cuts a_k and a₀≤c, with limiting full-endpoint cone and
Mittag–Leffler restriction-kernel tower. Suppose R≤M attain the
eventual image, c≤d≤d′, and H_S^{n−1}(d,+∞)=H_S^{n−1}(d′,+∞)=0.
Identifying six alternative cuts with a_M,a_R,a₀,c,d,d′ preserves
the equality of the left-growth and right-growth window maps followed
by their comparisons with F_c/F_{a₀}. -/
private theorem stableImageFiniteWindowKernelGradedIso_indexing_of_eq
    (n : ℤ) (a : ℕ → EInt) (ha : Antitone a) (c : EInt) (hc : a 0 ≤ c)
    (hTotal : IsLimit (stableImageTotalCone S n a ha))
    (hML : (stableImageKernelTower
      (stableImageTowerRestriction S n a ha c hc)).IsSequentialMittagLeffler)
    (R M : ℕ) (hRM : R ≤ M)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le R)).op))
    (hM : ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S n a ha c hc)).map
        (homOfLE (Nat.zero_le M)).op))
    (d d' : EInt) (hcd : c ≤ d) (hdd : d ≤ d')
    (zR : IsZero ((S.H (n - 1)).obj (mk₁ (stableIntervalRight d))))
    (zM : IsZero ((S.H (n - 1)).obj (mk₁ (stableIntervalRight d'))))
    {jM jR j₀ jC jd jd' : EInt}
    (hMR : jM ≤ jR) (hR₀ : jR ≤ j₀) (h₀C : j₀ ≤ jC) (hCd : jC ≤ jd) (hdd' : jd ≤ jd')
    (eM : jM = a M) (eR : jR = a R) (e₀ : j₀ = a 0) (eC : jC = c)
    (ed : jd = d) (ed' : jd' = d') :
    S.mapFourδ₁Toδ₀' jM jR j₀ jC jd hMR hR₀ h₀C hCd (n - 1) n (n + 1) ≫
        (stableImageWindowEqIso S n hR₀ h₀C hCd
          (ha (Nat.zero_le R)) hc hcd eR e₀ eC ed).hom ≫
        (stableImageFiniteWindowKernelGradedIso S n a ha c hc hTotal hML R hR d hcd zR).hom =
      S.mapFourδ₄Toδ₃' jM j₀ jC jd jd' (hMR.trans hR₀) h₀C hCd hdd'
        (n - 1) n (n + 1) ≫
        (stableImageWindowEqIso S n (hMR.trans hR₀) h₀C (hCd.trans hdd')
          (ha (Nat.zero_le M)) hc (hcd.trans hdd) eM e₀ eC ed').hom ≫
        (stableImageFiniteWindowKernelGradedIso S n a ha c hc hTotal hML M hM d'
          (hcd.trans hdd) zM).hom := by
  subst jM jR j₀ jC jd jd'
  simp only [stableImageWindowEqIso, Iso.refl_hom, Category.id_comp]
  exact stableImageFiniteWindowKernelGradedIso_indexing S n a ha c hc hTotal hML R M hRM
    hR hM hcd hdd zR zM

/-- Let S be an EInt-indexed abelian-group spectral object, p,q∈ℤ,
n=p+q and a_k=−p−1−k. Assume the full-endpoint cone over
H_Sⁿ(a_k,+∞) is limiting and the kernels of restriction to
H_Sⁿ(−p,+∞) form a Mittag–Leffler tower.
Suppose R and R+1 attain its eventual image, the right intervals
H_S^{n−1}(−p+R,+∞) and H_S^{n−1}(−p+R+1,+∞) vanish, and both
adjacent differentials at (p,q) on page R+1 are zero.
Then the page-(R+2) graded comparison composed with the successor
from page R+1 equals the page-(R+1) graded comparison. -/
theorem stableImageSkeletalSuccessorIso_comp_graded (p q : ℤ)
    (hTotal : IsLimit (stableImageTotalCone S (p + q) (stableImageSkeletalLeftCuts p)
      (stableImageSkeletalLeftCuts_antitone p)))
    (hML : (stableImageKernelTower (stableImageTowerRestriction S (p + q)
      (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
      ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).IsSequentialMittagLeffler)
    (R : ℕ)
    (hR : ((stableImageKernelTower (stableImageTowerRestriction S (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).map
          (homOfLE (Nat.zero_le R)).op))
    (hM : ((stableImageKernelTower (stableImageTowerRestriction S (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))) ⋙
        forget AddCommGrpCat.{u}).eventualRange (op 0) =
      Set.range ((stableImageKernelTower (stableImageTowerRestriction S (p + q)
        (stableImageSkeletalLeftCuts p) (stableImageSkeletalLeftCuts_antitone p)
        ((-p : ℤ) : EInt) (stableImageSkeletal_middle p))).map
          (homOfLE (Nat.zero_le (R + 1))).op))
    (zR : IsZero ((S.H (p + q - 1)).obj
      (mk₁ (stableIntervalRight (((-p + (R : ℤ) : ℤ) : EInt))))))
    (zM : IsZero ((S.H (p + q - 1)).obj
      (mk₁ (stableIntervalRight (((-p + ((R + 1 : ℕ) : ℤ) : ℤ) : EInt))))))
    (hf : ((S.skeletalSpectralSequence.page ((R : ℤ) + 1) (by omega)).sc (p, q)).f = 0)
    (hg : ((S.skeletalSpectralSequence.page ((R : ℤ) + 1) (by omega)).sc (p, q)).g = 0) :
    (S.stableImageSkeletalSuccessorIso ((R : ℤ) + 1) (by omega) p q hf hg).hom ≫
        (stableImageSkeletalPageGradedIso S p q hTotal hML (R + 1) hM zM).hom =
      (stableImageSkeletalPageGradedIso S p q hTotal hML R hR zR).hom := by
  let r : ℤ := (R : ℤ) + 1
  let a := stableImageSkeletalLeftCuts p
  let ha := stableImageSkeletalLeftCuts_antitone p
  let c : EInt := ((-p : ℤ) : EInt)
  let hc := stableImageSkeletal_middle p
  let d : EInt := ((-p + (R : ℤ) : ℤ) : EInt)
  let d' : EInt := ((-p + ((R + 1 : ℕ) : ℤ) : ℤ) : EInt)
  have hcd : c ≤ d := by simp [c, d]
  have hdd : d ≤ d' := by simp [d, d']
  let HD := S.skeletalSuccessorHomologyData r (by dsimp [r]; omega) p q
  let _ : IsIso HD.left.i := HD.left.isIso_i hg
  apply (cancel_epi HD.left.i).1
  have hi := S.stableImageSkeletalSuccessorIso_i r (by dsimp [r]; omega) p q hf hg
  have hpad := stableImageFiniteWindowKernelGradedIso_indexing_of_eq S (p + q) a ha c hc
    hTotal hML R (R + 1) (Nat.le_succ R) hR hM d d' hcd hdd zR zM
    (jM := ((-p - (r + 1) : ℤ) : EInt)) (jR := ((-p - r : ℤ) : EInt))
    (j₀ := ((-(p + 1) : ℤ) : EInt)) (jC := ((-p : ℤ) : EInt))
    (jd := ((-p + r - 1 : ℤ) : EInt)) (jd' := ((-p + (r + 1) - 1 : ℤ) : EInt))
    (by simp only [WithBotTop.coe_le_coe]; omega)
    (by simp only [WithBotTop.coe_le_coe]; dsimp [r]; omega) (by simp)
    (by simp only [WithBotTop.coe_le_coe]; dsimp [r]; omega)
    (by simp only [WithBotTop.coe_le_coe]; omega)
    (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [a, stableImageSkeletalLeftCuts, r]; omega)
    (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [a, stableImageSkeletalLeftCuts, r]; omega)
    (by simp [a, stableImageSkeletalLeftCuts]) rfl
    (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [d, r]; omega)
    (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [d', r]; omega)
  let wR := S.skeletalPageWindowIso r (by dsimp [r]; omega) p q
  let wM := S.skeletalPageWindowIso (r + 1) (by dsimp [r]; omega) p q
  let heR := stableImageWindowEqIso S (p + q)
    (show ((-p - r : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; dsimp [r]; omega)
    (show ((-(p + 1) : ℤ) : EInt) ≤ c by simp [c])
    (show c ≤ ((-p + r - 1 : ℤ) : EInt) by simp [c]; dsimp [r]; omega)
    (ha (Nat.zero_le R)) hc hcd
    (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [a, stableImageSkeletalLeftCuts, r]; omega)
    (by simp [stableImageSkeletalLeftCuts]) rfl
    (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [d, r]; omega)
  let heM := stableImageWindowEqIso S (p + q)
    (show ((-p - (r + 1) : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; dsimp [r]; omega)
    (show ((-(p + 1) : ℤ) : EInt) ≤ c by simp [c])
    (show c ≤ ((-p + (r + 1) - 1 : ℤ) : EInt) by simp [c]; dsimp [r]; omega)
    (ha (Nat.zero_le (R + 1))) hc (hcd.trans hdd)
    (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [a, stableImageSkeletalLeftCuts, r]; omega)
    (by simp [stableImageSkeletalLeftCuts]) rfl
    (by apply congrArg (fun i : ℤ => (i : EInt)); dsimp [d', r]; omega)
  let FR := stableImageFiniteWindowKernelGradedIso S (p + q) a ha c hc hTotal hML
    R hR d hcd zR
  let FM := stableImageFiniteWindowKernelGradedIso S (p + q) a ha c hc hTotal hML
    (R + 1) hM d' (hcd.trans hdd) zM
  let egrade : S.stableIntervalKernelGraded (p + q) hc ≅ S.skeletalAbutmentGraded (p + q) p :=
    stableImageKernelGradedEqIso S (p + q) hc
      (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
      (by simp [stableImageSkeletalLeftCuts]) rfl
  change HD.left.i ≫ ((S.stableImageSkeletalSuccessorIso r (by dsimp [r]; omega) p q hf hg).hom ≫
      (((wM.hom ≫ heM.hom) ≫ FM.hom) ≫ egrade.hom)) =
    HD.left.i ≫ (((wR.hom ≫ heR.hom) ≫ FR.hom) ≫ egrade.hom)
  simp only [Category.assoc]
  slice_lhs 1 3 => rw [hi]
  slice_rhs 1 2 =>
    rw [S.skeletalSuccessorHomologyData_i]
    dsimp only [wR]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [S.skeletalSuccessorHomologyData_π]
  slice_lhs 1 3 => rw [← hpad]
  simp only [Category.assoc, heR, FR]

end CategoryTheory.Abelian.SpectralObject

end
