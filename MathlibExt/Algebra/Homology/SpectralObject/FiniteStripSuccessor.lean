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

public import MathlibExt.Algebra.Homology.SpectralObject.FiniteStripConvergence

import all Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# Compatibility of finite convergence with native successors

The endpoint comparison commutes with the genuine interval indexing maps.
Together with the original page homology data, this makes the finite
associated-graded comparison compatible with native successor isomorphisms.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace CategoryTheory.ShortComplex

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- For a short complex with zero differentials, the canonical identification
with zero-differential homology retains every actual homology datum's `i` and `π`. -/
theorem LeftHomologyData.i_comp_zeroHomologyIso
    (S : ShortComplex D) (h : S.LeftHomologyData) (hf : S.f = 0) (hg : S.g = 0) :
    h.i ≫ (HomologyData.ofZeros S hf hg).left.homologyIso.inv ≫ h.homologyIso.hom = h.π := by
  let h0 := (HomologyData.ofZeros S hf hg).left
  have hi0 : h0.cyclesIso.hom = S.iCycles := by
    have hi := h0.cyclesIso_hom_comp_i
    change h0.cyclesIso.hom ≫ 𝟙 _ = S.iCycles at hi
    simpa only [Category.comp_id] using hi
  have hπ0 : h0.homologyIso.inv = h0.cyclesIso.inv ≫ S.homologyπ := by
    have hπ := h0.π_comp_homologyIso_inv
    change 𝟙 _ ≫ h0.homologyIso.inv = h0.cyclesIso.inv ≫ S.homologyπ at hπ
    simpa only [Category.id_comp] using hπ
  change h.i ≫ h0.homologyIso.inv ≫ h.homologyIso.hom = h.π
  rw [hπ0, ← h.cyclesIso_inv_comp_iCycles]
  simp only [Category.assoc, ← hi0, Iso.hom_inv_id_assoc,
    h.homologyπ_comp_homologyIso_hom, Iso.inv_hom_id_assoc]

end CategoryTheory.ShortComplex

namespace CategoryTheory.Abelian.SpectralObject

variable {D : Type u} [Category.{v} D] [Abelian D]

section Padding

variable {ι : Type w} [Preorder ι] [OrderBot ι] [OrderTop ι]
variable (Y : SpectralObject D ι)

/-- The two actual indexing maps around a growing window give the same
endpoint comparison. All isomorphisms are the native indexing isomorphisms. -/
theorem finiteIntervalPaddingIso_indexing
    (n : ℤ) {a' a b c d d' : ι}
    (haa : a' ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hdd : d ≤ d')
    (hleft : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ a)))))
    (hleft' : IsZero ((Y.H (n + 1)).obj (mk₁ (homOfLE (bot_le : (⊥ : ι) ≤ a')))))
    (hright : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : d ≤ (⊤ : ι))))))
    (hright' : IsZero ((Y.H (n - 1)).obj (mk₁ (homOfLE (le_top : d' ≤ (⊤ : ι)))))) :
    Y.mapFourδ₁Toδ₀' a' a b c d haa hab hbc hcd (n - 1) n (n + 1) ≫
        (Y.finiteIntervalPaddingIso n hab hbc hcd hleft hright).hom =
      Y.mapFourδ₄Toδ₃' a' b c d d' (haa.trans hab) hbc hcd hdd (n - 1) n (n + 1) ≫
        (Y.finiteIntervalPaddingIso n (haa.trans hab) hbc (hcd.trans hdd) hleft' hright').hom := by
  let L := Y.isoMapFourδ₁Toδ₀' (⊥ : ι) a b c d
    bot_le hab hbc hcd (n - 1) n (n + 1) hleft
  let L' := Y.isoMapFourδ₁Toδ₀' (⊥ : ι) a' b c d
    bot_le (haa.trans hab) hbc hcd (n - 1) n (n + 1) hleft'
  let L'' := Y.isoMapFourδ₁Toδ₀' (⊥ : ι) a' b c d'
    bot_le (haa.trans hab) hbc (hcd.trans hdd) (n - 1) n (n + 1) hleft'
  let R := Y.isoMapFourδ₄Toδ₃' (⊥ : ι) b c d (⊤ : ι)
    bot_le hbc hcd le_top (n - 1) n (n + 1) hright
  let R' := Y.isoMapFourδ₄Toδ₃' (⊥ : ι) b c d' (⊤ : ι)
    bot_le hbc (hcd.trans hdd) le_top (n - 1) n (n + 1) hright'
  have hL : L'.hom ≫
      Y.mapFourδ₁Toδ₀' a' a b c d haa hab hbc hcd (n - 1) n (n + 1) = L.hom :=
    Y.mapFourδ₁Toδ₀'_comp (⊥ : ι) a' a b c d
      bot_le haa hab hbc hcd (n - 1) n (n + 1)
  have hSquare : L'.hom ≫
      Y.mapFourδ₄Toδ₃' a' b c d d' (haa.trans hab) hbc hcd hdd (n - 1) n (n + 1) =
    Y.mapFourδ₄Toδ₃' (⊥ : ι) b c d d' bot_le hbc hcd hdd (n - 1) n (n + 1) ≫ L''.hom :=
    Y.mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' (⊥ : ι) a' b c d d'
      bot_le (haa.trans hab) hbc hcd hdd (n - 1) n (n + 1)
  have hR :
      Y.mapFourδ₄Toδ₃' (⊥ : ι) b c d d' bot_le hbc hcd hdd (n - 1) n (n + 1) ≫ R'.hom =
    R.hom :=
    Y.mapFourδ₄Toδ₃'_comp (⊥ : ι) b c d d' (⊤ : ι)
      bot_le hbc hcd hdd le_top (n - 1) n (n + 1)
  apply (cancel_epi L'.hom).1
  change L'.hom ≫
      (Y.mapFourδ₁Toδ₀' a' a b c d haa hab hbc hcd (n - 1) n (n + 1) ≫
        (L.inv ≫ R.hom)) =
    L'.hom ≫
      (Y.mapFourδ₄Toδ₃' a' b c d d' (haa.trans hab) hbc hcd hdd (n - 1) n (n + 1) ≫
        (L''.inv ≫ R'.hom))
  rw [← Category.assoc, hL, L.hom_inv_id_assoc,
    ← Category.assoc, hSquare, Category.assoc, L''.hom_inv_id_assoc, hR]

end Padding

section NativeSuccessor

variable (Y : SpectralObject D EInt)

/-- The original native homology data at the three canonical neighboring
positions, presented at the integer skeletal window cuts. -/
def skeletalSuccessorHomologyData (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    (((Y.skeletalSpectralSequence).page r hr).sc (p, q)).HomologyData :=
  Y.spectralSequenceHomologyData skeletalPageCore r (r + 1) rfl hr
    ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (p, q)) (p, q)
    ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (p, q)) rfl rfl
    ((-p - (r + 1) : ℤ) : EInt) ((-p - r : ℤ) : EInt)
    ((-(p + 1) : ℤ) : EInt) ((-p : ℤ) : EInt)
    ((-p + r - 1 : ℤ) : EInt) ((-p + (r + 1) - 1 : ℤ) : EInt)
    rfl rfl (by simp [skeletalPageCore, sub_eq_add_neg, add_comm]) rfl rfl rfl
    (p + q - 1) (p + q) (p + q + 1) rfl (by omega) (by omega)

/-- The cycles inclusion of the original native datum is the original left
window indexing map transported to the old page. -/
theorem skeletalSuccessorHomologyData_i (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    (Y.skeletalSuccessorHomologyData r hr p q).left.i =
      Y.mapFourδ₁Toδ₀'
        ((-p - (r + 1) : ℤ) : EInt) ((-p - r : ℤ) : EInt)
        ((-(p + 1) : ℤ) : EInt) ((-p : ℤ) : EInt) ((-p + r - 1 : ℤ) : EInt)
        (by simp; omega) (by simp; omega) (by simp) (by simp; omega)
        (p + q - 1) (p + q) (p + q + 1) ≫
        (Y.skeletalPageWindowIso r hr p q).inv := by
  have h := Y.spectralSequenceHomologyData_left_i skeletalPageCore r (r + 1) rfl hr
    ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (p, q)) (p, q)
    ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (p, q)) rfl rfl
    ((-p - (r + 1) : ℤ) : EInt) ((-p - r : ℤ) : EInt)
    ((-(p + 1) : ℤ) : EInt) ((-p : ℤ) : EInt)
    ((-p + r - 1 : ℤ) : EInt) ((-p + (r + 1) - 1 : ℤ) : EInt)
    rfl rfl (by simp [skeletalPageCore, sub_eq_add_neg, add_comm]) rfl rfl rfl
    (p + q - 1) (p + q) (p + q + 1) rfl (by omega) (by omega)
  simpa only [skeletalSuccessorHomologyData, skeletalPageWindowIso] using h

/-- The quotient of the original native datum is the original right window
indexing map, before transport to the new page. -/
theorem skeletalSuccessorHomologyData_π (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    (Y.skeletalSuccessorHomologyData r hr p q).left.π =
      Y.mapFourδ₄Toδ₃'
        ((-p - (r + 1) : ℤ) : EInt) ((-(p + 1) : ℤ) : EInt) ((-p : ℤ) : EInt)
        ((-p + r - 1 : ℤ) : EInt) ((-p + (r + 1) - 1 : ℤ) : EInt)
        (by simp; omega) (by simp) (by simp; omega) (by simp)
        (p + q - 1) (p + q) (p + q + 1) := rfl

/-- The native sequence successor is the homology isomorphism of its
original datum, followed by transport from the actual new window. -/
theorem skeletalSequence_iso_eq_successorHomologyData
    (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) :
    (Y.skeletalSpectralSequence).iso r (r + 1) (p, q) rfl hr =
      (Y.skeletalSuccessorHomologyData r hr p q).left.homologyIso ≪≫
        (Y.skeletalPageWindowIso (r + 1) (by omega) p q).symm := by
  have h := Y.spectralSequence_iso skeletalPageCore r (r + 1) rfl hr
    ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).prev (p, q)) (p, q)
    ((ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).next (p, q)) rfl rfl
    ((-p - (r + 1) : ℤ) : EInt) ((-p - r : ℤ) : EInt)
    ((-(p + 1) : ℤ) : EInt) ((-p : ℤ) : EInt)
    ((-p + r - 1 : ℤ) : EInt) ((-p + (r + 1) - 1 : ℤ) : EInt)
    rfl rfl (by simp [skeletalPageCore, sub_eq_add_neg, add_comm]) rfl rfl rfl
    (p + q - 1) (p + q) (p + q + 1) rfl (by omega) (by omega)
  simpa only [HomologicalComplex.homologyIsoSc'_eq_refl, Iso.refl_trans,
    skeletalSuccessorHomologyData, skeletalPageWindowIso] using h

variable (N : ℕ)
variable
  (hfull : ∀ (n i : ℤ), i ≤ -(N : ℤ) - 1 →
    IsZero ((Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
  (hempty : ∀ (n i : ℤ), 0 ≤ i →
    IsZero ((Y.H n).obj (mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))

include hfull hempty in
/-- The actual native stabilized successor carries the original cycles
inclusion to the original quotient, at the actual new-page presentation. -/
theorem finiteSkeletalSuccessorIso_i
    (r : ℤ) (hr : (N : ℤ) + 1 ≤ r) (p q : ℤ) :
    (Y.skeletalSuccessorHomologyData r (by omega) p q).left.i ≫
        (Y.finiteSkeletalSuccessorIso N hfull hempty r hr (p, q)).hom ≫
        (Y.skeletalPageWindowIso (r + 1) (by omega) p q).hom =
      (Y.skeletalSuccessorHomologyData r (by omega) p q).left.π := by
  dsimp only [finiteSkeletalSuccessorIso, Iso.trans_hom, Iso.symm_hom]
  rw [Y.skeletalSequence_iso_eq_successorHomologyData]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  exact ShortComplex.LeftHomologyData.i_comp_zeroHomologyIso _
    (Y.skeletalSuccessorHomologyData r (by omega) p q).left _ _

include hfull hempty in
/-- Inside the finite strip, the associated-graded comparison commutes with
the actual native successor isomorphism. -/
theorem finiteSkeletalSuccessorIso_comp_gradedOfMemStrip
    (r : ℤ) (hr : (N : ℤ) + 1 ≤ r) (p q : ℤ) (hp₀ : 0 ≤ p) (hpN : p ≤ (N : ℤ)) :
    (Y.finiteSkeletalSuccessorIso N hfull hempty r hr (p, q)).hom ≫
        (Y.finiteSkeletalPageGradedIsoOfMemStrip N hfull hempty (r + 1) (by omega)
          p q hp₀ hpN).hom =
      (Y.finiteSkeletalPageGradedIsoOfMemStrip N hfull hempty r hr p q hp₀ hpN).hom := by
  let HD := Y.skeletalSuccessorHomologyData r (by omega) p q
  let _ : IsIso HD.left.i :=
    HD.left.isIso_i (Y.finiteSkeletalPage_d_eq_zero N hfull hempty r hr _ _)
  apply (cancel_epi HD.left.i).1
  have hi := Y.finiteSkeletalSuccessorIso_i N hfull hempty r hr p q
  have hpad := Y.finiteIntervalPaddingIso_indexing (p + q)
    (a' := ((-p - (r + 1) : ℤ) : EInt)) (a := ((-p - r : ℤ) : EInt))
    (b := ((-(p + 1) : ℤ) : EInt)) (c := ((-p : ℤ) : EInt))
    (d := ((-p + r - 1 : ℤ) : EInt)) (d' := ((-p + (r + 1) - 1 : ℤ) : EInt))
    (by simp; omega) (by simp; omega) (by simp) (by simp; omega) (by simp)
    (hfull (p + q + 1) (-p - r) (by omega))
    (hfull (p + q + 1) (-p - (r + 1)) (by omega))
    (hempty (p + q - 1) (-p + r - 1) (by omega))
    (hempty (p + q - 1) (-p + (r + 1) - 1) (by omega))
  dsimp only [finiteSkeletalPageGradedIsoOfMemStrip, finiteIntervalKernelGradedIso,
    finiteIntervalImageCokernelIso, Iso.trans_hom]
  simp only [Category.assoc]
  slice_lhs 1 3 => rw [hi]
  slice_rhs 1 2 =>
    rw [Y.skeletalSuccessorHomologyData_i]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Y.skeletalSuccessorHomologyData_π]
  slice_lhs 1 2 => rw [← hpad]

include hfull hempty in
/-- At every integer position, the finite associated-graded comparison is
compatible with the native successor, including the zero objects outside the strip. -/
theorem finiteSkeletalSuccessorIso_comp_graded
    (r : ℤ) (hr : (N : ℤ) + 1 ≤ r) (p q : ℤ) :
    (Y.finiteSkeletalSuccessorIso N hfull hempty r hr (p, q)).hom ≫
        (Y.finiteSkeletalPageGradedIso N hfull hempty (r + 1) (by omega) p q).hom =
      (Y.finiteSkeletalPageGradedIso N hfull hempty r hr p q).hom := by
  by_cases hp : 0 ≤ p ∧ p ≤ (N : ℤ)
  · simpa only [finiteSkeletalPageGradedIso, dite_eq_left hp] using
      Y.finiteSkeletalSuccessorIso_comp_gradedOfMemStrip N hfull hempty r hr p q hp.1 hp.2
  · exact (Y.isZero_skeletalPage N hfull hempty r (by omega) p q (by omega)).eq_of_src _ _

end NativeSuccessor

/-- At a common late native page, enlarging the finite strip bound does not
change the associated-graded comparison. The zero branches are forced by
actual interval exactness, and the nonzero branch uses the same indexing maps. -/
theorem finiteSkeletalPageGradedIso_eq_of_bounds
    (Y : SpectralObject D EInt) (N N' : ℕ)
    (hfull : ∀ (n i : ℤ), i ≤ -(N : ℤ) - 1 →
      IsZero ((Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hfull' : ∀ (n i : ℤ), i ≤ -(N' : ℤ) - 1 →
      IsZero ((Y.H n).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ (i : EInt))))))
    (hempty : ∀ (n i : ℤ), 0 ≤ i →
      IsZero ((Y.H n).obj (mk₁ (homOfLE (le_top : (i : EInt) ≤ (⊤ : EInt))))))
    (r : ℤ) (hr : (N : ℤ) + 1 ≤ r) (hr' : (N' : ℤ) + 1 ≤ r) (p q : ℤ) :
    (Y.finiteSkeletalPageGradedIso N hfull hempty r hr p q).hom =
      (Y.finiteSkeletalPageGradedIso N' hfull' hempty r hr' p q).hom := by
  by_cases hp : 0 ≤ p ∧ p ≤ (N : ℤ)
  · by_cases hp' : 0 ≤ p ∧ p ≤ (N' : ℤ)
    · dsimp only [finiteSkeletalPageGradedIso]
      rw [dite_eq_left hp, dite_eq_left hp']
      rfl
    · exact (Y.isZero_skeletalPage N' hfull' hempty r (by omega) p q (by omega)).eq_of_src _ _
  · exact (Y.isZero_skeletalPage N hfull hempty r (by omega) p q (by omega)).eq_of_src _ _

end CategoryTheory.Abelian.SpectralObject

end
