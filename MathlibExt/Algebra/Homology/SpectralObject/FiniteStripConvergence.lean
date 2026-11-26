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
# Finite-strip convergence of integer-indexed skeletal pages

Let Y be an EInt-indexed spectral object in an abelian category D.
For N∈ℕ, suppose in every integer cohomological degree m that
H_Yᵐ(−∞,i)=0 for i≤−N−1 and H_Yᵐ(i,+∞)=0 for i≥0.
The decreasing filtration of A_n=H_Yⁿ(−∞,+∞) is
FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞)).
It is full for p≤0 and zero for p>N.

For r≥N+1 and all p,q∈ℤ the page object is canonically
E_r^{p,q} ≅ FᵖA_{p+q}/Fᵖ⁺¹A_{p+q}.
Page objects and graded pieces vanish for p<0 or p>N, and every differential
on these late pages is zero. The comparisons, filtration maps and graded
maps are natural in spectral-object morphisms with the same endpoint
vanishings.
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

/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n.

The decreasing integer filtration p↦FᵖA_n given by kernels of restriction at the cut −p. -/
def skeletalAbutmentFiltration (n p : ℤ) : Subobject (Y.stableIntervalAbutment n) :=
  Y.stableIntervalKernelFiltration n ((-p : ℤ) : EInt)

theorem skeletalAbutmentFiltration_antitone (n : ℤ) :
    Antitone (Y.skeletalAbutmentFiltration n) := by
  intro p p' h
  exact Y.stableIntervalKernelFiltration_monotone n (by simp; omega)

/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n.

The associated-graded object GrᵖA_n=Coker(Fᵖ⁺¹A_n ↪ FᵖA_n). -/
abbrev skeletalAbutmentGraded (n p : ℤ) : D :=
  cokernel (Subobject.ofLE _ _
    (Y.skeletalAbutmentFiltration_antitone n (show p ≤ p + 1 by omega)))

/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n.

For r≥1 and p,q∈ℤ, the page object E_r^{p,q} is canonically the window E_Y^{p+q}(−p−r≤−p−1≤−p≤−p+r−1). -/
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
/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n.

Assume H_Yᵐ(i,+∞)=0 for all integers m and i≥0. If p≤0, the filtration step FᵖA_n is the full subobject of A_n. -/
theorem skeletalAbutmentFiltration_eq_top (n p : ℤ) (hp : p ≤ 0) :
    Y.skeletalAbutmentFiltration n p = ⊤ :=
  Y.stableIntervalKernelFiltration_eq_top n ((-p : ℤ) : EInt)
    (hempty n (-p) (by omega))

include hfull in
/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n.

Fix N∈ℕ and assume H_Yᵐ(−∞,i)=0 for all integers m and i≤−N−1. If p>N, the filtration step FᵖA_n is zero. -/
theorem skeletalAbutmentFiltration_eq_bot (n p : ℤ) (hp : (N : ℤ) < p) :
    Y.skeletalAbutmentFiltration n p = ⊥ :=
  Y.stableIntervalKernelFiltration_eq_bot n ((-p : ℤ) : EInt)
    (hfull n (-p) (by omega))

include hfull hempty in
/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n. Fix N∈ℕ and assume, for every integer m,
H_Yᵐ(−∞,i)=0 for i≤−N−1 and H_Yᵐ(i,+∞)=0 for i≥0.

The filtration endpoints are F⁰A_n=A_n and F^{N+1}A_n=0. -/
theorem skeletalAbutmentFiltration_endpoints (n : ℤ) :
    Y.skeletalAbutmentFiltration n 0 = ⊤ ∧
      Y.skeletalAbutmentFiltration n ((N : ℤ) + 1) = ⊥ :=
  ⟨Y.skeletalAbutmentFiltration_eq_top hempty n 0 (by omega),
    Y.skeletalAbutmentFiltration_eq_bot N hfull n ((N : ℤ) + 1) (by omega)⟩

include hfull hempty in
/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n. Fix N∈ℕ and assume, for every integer m,
H_Yᵐ(−∞,i)=0 for i≤−N−1 and H_Yᵐ(i,+∞)=0 for i≥0.

If p<0 or p>N, the middle-interval object H_Yⁿ(−p−1,−p) is zero. -/
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
/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n. Fix N∈ℕ and assume, for every integer m,
H_Yᵐ(−∞,i)=0 for i≤−N−1 and H_Yᵐ(i,+∞)=0 for i≥0.

For every r≥1 and p,q∈ℤ with p<0 or p>N, the page object E_r^{p,q} is zero. -/
theorem isZero_skeletalPage (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
    (hp : p < 0 ∨ (N : ℤ) < p) :
    IsZero (((Y.skeletalSpectralSequence).page r hr).X (p, q)) :=
  (Iso.isZero_iff (Y.skeletalPageWindowIso r hr p q)).mpr
    (Y.isZero_E_of_isZero_H _ _ _ (p + q - 1) (p + q) (p + q + 1)
      (Y.isZero_skeletalMiddleInterval N hfull hempty (p + q) p hp)
      (by omega) (by omega))

include hfull hempty in
/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n. Fix N∈ℕ and assume, for every integer m,
H_Yᵐ(−∞,i)=0 for i≤−N−1 and H_Yᵐ(i,+∞)=0 for i≥0.

For p<0 or p>N, the graded object GrᵖA_n is zero. -/
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

/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n. Fix N∈ℕ and assume, for every integer m,
H_Yᵐ(−∞,i)=0 for i≤−N−1 and H_Yᵐ(i,+∞)=0 for i≥0.

For r≥N+1, 0≤p≤N and any q∈ℤ, the canonical comparison E_r^{p,q} ≅ GrᵖA_{p+q}. -/
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

/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n. Fix N∈ℕ and assume, for every integer m,
H_Yᵐ(−∞,i)=0 for i≤−N−1 and H_Yᵐ(i,+∞)=0 for i≥0.

For r≥N+1 and arbitrary p,q∈ℤ, the canonical comparison E_r^{p,q} ≅ GrᵖA_{p+q}, including the zero objects outside the strip. -/
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
/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n. Fix N∈ℕ and assume, for every integer m,
H_Yᵐ(−∞,i)=0 for i≤−N−1 and H_Yᵐ(i,+∞)=0 for i≥0.

Every page differential d:E_r^{p,q} → E_r^{p′,q′} is zero when r≥N+1. -/
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

/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n. Fix N∈ℕ and assume, for every integer m,
H_Yᵐ(−∞,i)=0 for i≤−N−1 and H_Yᵐ(i,+∞)=0 for i≥0.

For r≥N+1, the canonical successor isomorphism E_r^{p,q} ≅ E_{r+1}^{p,q}, formed from the zero-differential homology identification and the spectral-sequence successor. -/
def finiteSkeletalSuccessorIso
    (r : ℤ) (hr : (N : ℤ) + 1 ≤ r) (pq : ℤ × ℤ) :
    ((Y.skeletalSpectralSequence).page r (by omega)).X pq ≅
      ((Y.skeletalSpectralSequence).page (r + 1) (by omega)).X pq :=
  (ShortComplex.HomologyData.ofZeros
    (((Y.skeletalSpectralSequence).page r (by omega)).sc pq)
    (Y.finiteSkeletalPage_d_eq_zero N hfull hempty r hr _ _)
    (Y.finiteSkeletalPage_d_eq_zero N hfull hempty r hr _ _)).left.homologyIso.symm ≪≫
      (Y.skeletalSpectralSequence).iso r (r + 1) pq rfl (by omega)

/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n.

For N∈ℕ, the selected stable-page object is E_{N+1}^{p,q}. -/
abbrev finiteSkeletalStablePage (p q : ℤ) : D :=
  ((Y.skeletalSpectralSequence).page ((N : ℤ) + 1) (by omega)).X (p, q)

/-- Let D be abelian and Y a spectral object indexed by EInt.
Set A_n=H_Yⁿ(−∞,+∞), FᵖA_n=Ker(A_n → H_Yⁿ(−p,+∞))
and GrᵖA_n=FᵖA_n/Fᵖ⁺¹A_n. Fix N∈ℕ and assume, for every integer m,
H_Yᵐ(−∞,i)=0 for i≤−N−1 and H_Yᵐ(i,+∞)=0 for i≥0.

The selected page E_{N+1}^{p,q} is canonically isomorphic to GrᵖA_{p+q}. -/
def finiteSkeletalStablePageGradedIso (p q : ℤ) :
    Y.finiteSkeletalStablePage N p q ≅ Y.skeletalAbutmentGraded (p + q) p :=
  Y.finiteSkeletalPageGradedIso N hfull hempty ((N : ℤ) + 1) le_rfl p q

end FiniteEnds

variable {Y Z : SpectralObject D EInt}

namespace Hom

/-- For a spectral-object morphism φ:Y → Z in an abelian category, indexed
by EInt, the induced map FᵖA_n(Y) → FᵖA_n(Z) between kernels of
restriction from Hⁿ(−∞,+∞) to Hⁿ(−p,+∞). -/
def skeletalAbutmentFiltrationMap (φ : Y ⟶ Z) (n p : ℤ) :
    (Y.skeletalAbutmentFiltration n p : D) ⟶ (Z.skeletalAbutmentFiltration n p : D) :=
  φ.stableIntervalKernelMap n ((-p : ℤ) : EInt)

/-- For a spectral-object morphism φ:Y → Z in an abelian category, indexed
by EInt, the quotient map GrᵖA_n(Y) → GrᵖA_n(Z) induced by the maps
of the decreasing restriction-kernel filtration. -/
def skeletalAbutmentGradedMap (φ : Y ⟶ Z) (n p : ℤ) :
    Y.skeletalAbutmentGraded n p ⟶ Z.skeletalAbutmentGraded n p :=
  φ.stableIntervalKernelGradedMap n
    (show ((-(p + 1) : ℤ) : EInt) ≤ ((-p : ℤ) : EInt) by simp)

unseal spectralSequence in
/-- For φ:Y → Z between EInt-indexed spectral objects in an abelian
category and r≥1, the page-window comparisons commute with the page
map and the E-window map on
−p−r≤−p−1≤−p≤−p+r−1 in degree p+q. -/
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

/-- Let D be abelian, φ:Y → Z a morphism of EInt-indexed spectral objects,
and N∈ℕ. For both W=Y,Z and every integer m assume
H_Wᵐ(−∞,i)=0 for i≤−N−1 and H_Wᵐ(i,+∞)=0 for i≥0.
Put FᵖA_n(W)=Ker(H_Wⁿ(−∞,+∞) → H_Wⁿ(−p,+∞)).

For r≥N+1, 0≤p≤N and any integer q, the comparisons E_r^{p,q}(W) ≅ GrᵖA_{p+q}(W) commute with the page map of φ and its associated-graded map. -/
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

/-- Let D be abelian, φ:Y → Z a morphism of EInt-indexed spectral objects,
and N∈ℕ. For both W=Y,Z and every integer m assume
H_Wᵐ(−∞,i)=0 for i≤−N−1 and H_Wᵐ(i,+∞)=0 for i≥0.
Put FᵖA_n(W)=Ker(H_Wⁿ(−∞,+∞) → H_Wⁿ(−p,+∞)).

For r≥N+1 and all integers p,q, the comparisons E_r^{p,q}(W) ≅ GrᵖA_{p+q}(W) commute with the page map of φ and its associated-graded map. -/
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
