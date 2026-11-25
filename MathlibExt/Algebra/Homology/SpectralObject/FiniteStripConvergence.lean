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

public import MathlibExt.Algebra.Homology.SpectralObject.AbutmentFiltration
public import MathlibExt.Algebra.Homology.SpectralObject.PageCore
public import MathlibExt.Algebra.Homology.SpectralObjectPageMapNaturality

/-!
# Finite strip convergence of the actual skeletal pages

The genuine cohomological pages stabilize at page `N + 1` for a spectral
object with constant skeletal ends of dimension `N`. The associated graded
is constructed from the actual restriction kernel filtration of its full
endpoint object. Filtration levels and both page coordinates range over all
integers; the coefficient degree has no lower bound.

The endpoint hypotheses concern only relative interval vanishing. The CW
application must derive them from the actual full and empty skeletal maps.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable {D : Type u} [Category.{v} D] [Abelian D]
variable (Y : SpectralObject D EInt)

/-- The integer decreasing filtration by actual skeletal restriction kernels. -/
def skeletalAbutmentFiltration (n p : ℤ) : Subobject (Y.stableIntervalAbutment n) :=
  Y.stableIntervalKernelFiltration n ((-p : ℤ) : EInt)

theorem skeletalAbutmentFiltration_antitone (n : ℤ) :
    Antitone (Y.skeletalAbutmentFiltration n) := by
  intro p p' h
  exact Y.stableIntervalKernelFiltration_monotone n (by simp; omega)

/-- The actual associated graded `F^p/F^(p+1)`. -/
abbrev skeletalAbutmentGraded (n p : ℤ) : D :=
  cokernel (Subobject.ofLE _ _
    (Y.skeletalAbutmentFiltration_antitone n (show p ≤ p + 1 by omega)))

/-- The actual native page presented as its skeletal `E` interval. -/
def skeletalPageWindowIso (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    ((Y.skeletalSpectralSequence).page r hr).X (p, q) ≅
      Y.E
        (homOfLE (show ((-p - r : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; omega))
        (homOfLE (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp))
        (homOfLE (show ((-p : ℤ) : EInt) ≤ ((-p + r - 1 : ℤ) : EInt) by simp; omega))
        (p + q - 1) (p + q) (p + q + 1) (by omega) (by omega) :=
  Y.spectralSequencePageXIso skeletalPageCore r hr (p, q)
    ((-p - r : ℤ) : EInt) ((-(p + 1) : ℤ) : EInt)
    ((-p : ℤ) : EInt) ((-p + r - 1 : ℤ) : EInt)
    rfl (by simp [skeletalPageCore, sub_eq_add_neg, add_comm]) rfl rfl
    (p + q - 1) (p + q) (p + q + 1) rfl (by omega) (by omega)

section FiniteEnds

variable (N : ℕ)
variable
  (hfull : ∀ (n i : ℤ), i ≤ -(N : ℤ) - 1 →
    IsZero ((Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
  (hempty : ∀ (n i : ℤ), 0 ≤ i →
    IsZero ((Y.H n).obj (mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))

include hempty in
/-- Every nonpositive filtration level is the full endpoint object. -/
theorem skeletalAbutmentFiltration_eq_top (n p : ℤ) (hp : p ≤ 0) :
    Y.skeletalAbutmentFiltration n p = ⊤ :=
  Y.stableIntervalKernelFiltration_eq_top n ((-p : ℤ) : EInt)
    (hempty n (-p) (by omega))

include hfull in
/-- Every level beyond the dimension is zero. -/
theorem skeletalAbutmentFiltration_eq_bot (n p : ℤ) (hp : (N : ℤ) < p) :
    Y.skeletalAbutmentFiltration n p = ⊥ :=
  Y.stableIntervalKernelFiltration_eq_bot n ((-p : ℤ) : EInt)
    (hfull n (-p) (by omega))

include hfull hempty in
/-- The actual filtration has the required bottom and top endpoints. -/
theorem skeletalAbutmentFiltration_endpoints (n : ℤ) :
    Y.skeletalAbutmentFiltration n 0 = ⊤ ∧
      Y.skeletalAbutmentFiltration n ((N : ℤ) + 1) = ⊥ :=
  ⟨Y.skeletalAbutmentFiltration_eq_top hempty n 0 (by omega),
    Y.skeletalAbutmentFiltration_eq_bot N hfull n ((N : ℤ) + 1) (by omega)⟩

include hfull hempty in
/-- The actual middle interval vanishes outside the finite skeletal strip,
by spectral-object exactness and the constant endpoint intervals. -/
theorem isZero_skeletalMiddleInterval (n p : ℤ) (hp : p < 0 ∨ (N : ℤ) < p) :
    IsZero ((Y.H n).obj
      (mk₁ (homOfLE (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)))) := by
  let f := homOfLE
    (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
  rcases hp with hp | hp
  · exact (Y.exact₁ f (stableIntervalRight ((-p : ℤ) : EInt))
      (stableIntervalRight ((-(p + 1) : ℤ) : EInt)) (by subsingleton)
      (n - 1) n (by omega)).isZero_of_both_isZero
        (hempty (n - 1) (-p) (by omega)) (hempty n (-(p + 1)) (by omega))
  · exact (Y.exact₃ (stableIntervalLeftMiddle ((-(p + 1) : ℤ) : EInt)) f
      (stableIntervalLeftMiddle ((-p : ℤ) : EInt)) (by subsingleton)
      n (n + 1) (by omega)).isZero_of_both_isZero
        (hfull n (-p) (by omega)) (hfull (n + 1) (-(p + 1)) (by omega))

include hfull hempty in
/-- Every genuine page object outside the strip is zero, in every coefficient
degree and on every page starting with the actual relative first page. -/
theorem isZero_skeletalPage (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hp : p < 0 ∨ (N : ℤ) < p) :
    IsZero (((Y.skeletalSpectralSequence).page r hr).X (p, q)) :=
  (Iso.isZero_iff (Y.skeletalPageWindowIso r hr p q)).mpr
    (Y.isZero_E_of_isZero_H _ _ _ (p + q - 1) (p + q) (p + q + 1)
      (Y.isZero_skeletalMiddleInterval N hfull hempty (p + q) p hp)
      (by omega) (by omega))

include hfull hempty in
/-- The actual associated graded vanishes outside the same finite strip. -/
theorem isZero_skeletalAbutmentGraded (n p : ℤ) (hp : p < 0 ∨ (N : ℤ) < p) :
    IsZero (Y.skeletalAbutmentGraded n p) := by
  have hEq : Y.skeletalAbutmentFiltration n (p + 1) = Y.skeletalAbutmentFiltration n p := by
    rcases hp with hp | hp
    · rw [Y.skeletalAbutmentFiltration_eq_top hempty n (p + 1) (by omega),
        Y.skeletalAbutmentFiltration_eq_top hempty n p (by omega)]
    · rw [Y.skeletalAbutmentFiltration_eq_bot N hfull n (p + 1) (by omega),
        Y.skeletalAbutmentFiltration_eq_bot N hfull n p (by omega)]
  let e := Subobject.isoOfEq _ _ hEq
  let _ : IsIso (Subobject.ofLE _ _
      (Y.skeletalAbutmentFiltration_antitone n (show p ≤ p + 1 by omega))) := e.isIso_hom
  exact (isZero_zero D).of_iso (cokernel.ofEpi _)

/-- In the finite strip, actual endpoint vanishing derives stabilization at
the uniform page bound `N + 1`. No cohomological degree enters the bound. -/
def finiteSkeletalPageGradedIsoOfMemStrip
    (r : ℤ) (hr : (N : ℤ) + 1 ≤ r) (p q : ℤ) (hp₀ : 0 ≤ p) (hpN : p ≤ (N : ℤ)) :
    ((Y.skeletalSpectralSequence).page r (by omega)).X (p, q) ≅
      Y.skeletalAbutmentGraded (p + q) p :=
  Y.skeletalPageWindowIso r (by omega) p q ≪≫
    Y.finiteIntervalKernelGradedIso (p + q)
      (show ((-p - r : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; omega)
      (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)
      (show ((-p : ℤ) : EInt) ≤ ((-p + r - 1 : ℤ) : EInt) by simp; omega)
      (hfull (p + q + 1) (-p - r) (by omega))
      (hempty (p + q - 1) (-p + r - 1) (by omega))

/-- Every actual page at or beyond `N + 1` is the actual associated graded
of the finite restriction kernel filtration, for all integer positions. -/
def finiteSkeletalPageGradedIso
    (r : ℤ) (hr : (N : ℤ) + 1 ≤ r) (p q : ℤ) :
    ((Y.skeletalSpectralSequence).page r (by omega)).X (p, q) ≅
      Y.skeletalAbutmentGraded (p + q) p :=
  if hp : 0 ≤ p ∧ p ≤ (N : ℤ) then
    Y.finiteSkeletalPageGradedIsoOfMemStrip N hfull hempty r hr p q hp.1 hp.2
  else
    (Y.isZero_skeletalPage N hfull hempty r (by omega) p q (by omega)).isoZero ≪≫
      (Y.isZero_skeletalAbutmentGraded N hfull hempty (p + q) p (by omega)).isoZero.symm

include hfull hempty in
/-- Every actual page differential at or beyond the finite bound is zero.
Only the filtration coordinate is used in the proof. -/
theorem finiteSkeletalPage_d_eq_zero
    (r : ℤ) (hr : (N : ℤ) + 1 ≤ r) (pq pq' : ℤ × ℤ) :
    ((Y.skeletalSpectralSequence).page r (by omega)).d pq pq' = 0 := by
  by_cases hstrip : 0 ≤ pq.1 ∧ pq.1 ≤ (N : ℤ)
  · by_cases hrel : (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel pq pq'
    · have hpq' : (N : ℤ) < pq'.1 := by
        change pq + (r, 1 - r) = pq' at hrel
        have hfst := congrArg (fun z : ℤ × ℤ => z.1) hrel
        dsimp at hfst
        omega
      exact (Y.isZero_skeletalPage N hfull hempty r (by omega)
        pq'.1 pq'.2 (Or.inr hpq')).eq_of_tgt _ _
    · exact ((Y.skeletalSpectralSequence).page r (by omega)).shape pq pq' hrel
  · exact (Y.isZero_skeletalPage N hfull hempty r (by omega)
      pq.1 pq.2 (by omega)).eq_of_src _ _

/-- The actual successor-page isomorphism after the finite bound: identify
zero-differential homology with the page object and use the native spectral
sequence successor isomorphism. -/
def finiteSkeletalSuccessorIso
    (r : ℤ) (hr : (N : ℤ) + 1 ≤ r) (pq : ℤ × ℤ) :
    ((Y.skeletalSpectralSequence).page r (by omega)).X pq ≅
      ((Y.skeletalSpectralSequence).page (r + 1) (by omega)).X pq :=
  (ShortComplex.HomologyData.ofZeros
    (((Y.skeletalSpectralSequence).page r (by omega)).sc pq)
    (Y.finiteSkeletalPage_d_eq_zero N hfull hempty r hr _ _)
    (Y.finiteSkeletalPage_d_eq_zero N hfull hempty r hr _ _)).left.homologyIso.symm ≪≫
      (Y.skeletalSpectralSequence).iso r (r + 1) pq rfl (by omega)

/-- The stable page is an actual native page at the derived finite bound. -/
abbrev finiteSkeletalStablePage (p q : ℤ) : D :=
  ((Y.skeletalSpectralSequence).page ((N : ℤ) + 1) (by omega)).X (p, q)

/-- The actual stable page is the associated graded of the original endpoint
abutment restriction filtration. -/
def finiteSkeletalStablePageGradedIso (p q : ℤ) :
    Y.finiteSkeletalStablePage N p q ≅ Y.skeletalAbutmentGraded (p + q) p :=
  Y.finiteSkeletalPageGradedIso N hfull hempty ((N : ℤ) + 1) le_rfl p q

end FiniteEnds

variable {Y Z : SpectralObject D EInt}

namespace Hom

/-- The actual map on each integer restriction-kernel filtration step. -/
def skeletalAbutmentFiltrationMap (φ : Y ⟶ Z) (n p : ℤ) :
    (Y.skeletalAbutmentFiltration n p : D) ⟶ (Z.skeletalAbutmentFiltration n p : D) :=
  φ.stableIntervalKernelMap n ((-p : ℤ) : EInt)

/-- The actual associated-graded map induced by the filtration maps. -/
def skeletalAbutmentGradedMap (φ : Y ⟶ Z) (n p : ℤ) :
    Y.skeletalAbutmentGraded n p ⟶ Z.skeletalAbutmentGraded n p :=
  φ.stableIntervalKernelGradedMap n
    (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)

unseal spectralSequence in
/-- The actual native fixed-page map commutes with the skeletal interval
presentation, including its integer index equality casts. -/
@[reassoc]
theorem skeletalPageWindowIso_naturality (φ : Y ⟶ Z)
    (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    (φ.spectralSequencePageMap skeletalPageCore r hr).f (p, q) ≫
        (Z.skeletalPageWindowIso r hr p q).hom =
      (Y.skeletalPageWindowIso r hr p q).hom ≫
        φ.EMap
          (homOfLE (show ((-p - r : ℤ) : EInt) ≤ ((-(p + 1) : ℤ) : EInt) by simp; omega))
          (homOfLE (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp))
          (homOfLE (show ((-p : ℤ) : EInt) ≤ ((-p + r - 1 : ℤ) : EInt) by simp; omega))
          (p + q - 1) (p + q) (p + q + 1) (by omega) (by omega) := by
  simpa only [spectralSequencePageMap, pageMap, skeletalPageWindowIso,
    spectralSequencePageXIso] using
    φ.pageMapComponent_pageXIso_hom skeletalPageCore r hr (p, q)
      ((-p - r : ℤ) : EInt) ((-(p + 1) : ℤ) : EInt)
      ((-p : ℤ) : EInt) ((-p + r - 1 : ℤ) : EInt)
      rfl (by simp [skeletalPageCore, sub_eq_add_neg, add_comm]) rfl rfl
      (p + q - 1) (p + q) (p + q + 1) rfl (by omega) (by omega)

section FiniteNaturality

variable (φ : Y ⟶ Z) (N : ℕ)
variable
  (hfullY : ∀ (n i : ℤ), i ≤ -(N : ℤ) - 1 →
    IsZero ((Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
  (hemptyY : ∀ (n i : ℤ), 0 ≤ i →
    IsZero ((Y.H n).obj (mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
  (hfullZ : ∀ (n i : ℤ), i ≤ -(N : ℤ) - 1 →
    IsZero ((Z.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
  (hemptyZ : ∀ (n i : ℤ), 0 ≤ i →
    IsZero ((Z.H n).obj (mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))

/-- In-strip convergence is natural for actual native page and filtration maps. -/
@[reassoc]
theorem finiteSkeletalPageGradedIsoOfMemStrip_naturality
    (r : ℤ) (hr : (N : ℤ) + 1 ≤ r) (p q : ℤ) (hp₀ : 0 ≤ p) (hpN : p ≤ (N : ℤ)) :
    (φ.spectralSequencePageMap skeletalPageCore r (by omega)).f (p, q) ≫
        (Z.finiteSkeletalPageGradedIsoOfMemStrip N hfullZ hemptyZ r hr p q hp₀ hpN).hom =
      (Y.finiteSkeletalPageGradedIsoOfMemStrip N hfullY hemptyY r hr p q hp₀ hpN).hom ≫
        φ.skeletalAbutmentGradedMap (p + q) p := by
  dsimp only [finiteSkeletalPageGradedIsoOfMemStrip, Iso.trans_hom,
    skeletalAbutmentGradedMap]
  rw [← Category.assoc, φ.skeletalPageWindowIso_naturality,
    Category.assoc, φ.finiteIntervalKernelGradedIso_naturality, ← Category.assoc]

/-- Convergence at every integer position is natural, including the zero
page objects outside the finite skeletal strip. -/
@[reassoc]
theorem finiteSkeletalPageGradedIso_naturality
    (r : ℤ) (hr : (N : ℤ) + 1 ≤ r) (p q : ℤ) :
    (φ.spectralSequencePageMap skeletalPageCore r (by omega)).f (p, q) ≫
        (Z.finiteSkeletalPageGradedIso N hfullZ hemptyZ r hr p q).hom =
      (Y.finiteSkeletalPageGradedIso N hfullY hemptyY r hr p q).hom ≫
        φ.skeletalAbutmentGradedMap (p + q) p := by
  dsimp only [finiteSkeletalPageGradedIso]
  split_ifs with hp
  · exact φ.finiteSkeletalPageGradedIsoOfMemStrip_naturality
      N hfullY hemptyY hfullZ hemptyZ r hr p q hp.1 hp.2
  · exact (Y.isZero_skeletalPage N hfullY hemptyY r (by omega) p q (by omega)).eq_of_src _ _

end FiniteNaturality

end Hom

end CategoryTheory.Abelian.SpectralObject

end
