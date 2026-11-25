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

public import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-!
# The skeletal cohomological page recipe

The first page has relative terms in total degree `p + q`, and its
differential has degree `(1, 0)`. On page `r`, the differential has degree
`(r, 1 - r)`. Both coordinates range over all integers.

The spectral-object index is opposite to the increasing skeletal index:
the middle interval `-p-1 ⟶ -p` represents the pair `(X^p, X^(p-1))`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

/-- The E₁ page recipe for the opposite inclusion index of an increasing filtration. -/
@[simps!]
def skeletalPageCore :
    SpectralSequenceDataCore EInt
      (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1 where
  deg pq := pq.1 + pq.2
  i₀ r pq _ := (-pq.1 - r : ℤ)
  i₁ pq := (-pq.1 - 1 : ℤ)
  i₂ pq := (-pq.1 : ℤ)
  i₃ r pq _ := (-pq.1 + r - 1 : ℤ)
  le₀₁ r pq hr := by simp; omega
  le₁₂ pq := by simp
  le₂₃ r pq hr := by simp; omega
  hc := by rintro r pq _ rfl _; dsimp; omega
  hc₀₂ := by rintro r pq _ rfl _; congr 1; dsimp; omega
  hc₁₃ := by rintro r pq _ rfl _; congr 1; dsimp; omega
  antitone_i₀ r r' pq hr hrr' := by simp; omega
  monotone_i₃ r r' pq hr hrr' := by simp; omega
  i₀_prev := by rintro r r' pq _ rfl hrr' _; congr 1; dsimp; omega
  i₃_next := by rintro r r' pq _ rfl hrr' _; congr 1; dsimp; omega

instance : skeletalPageCore.HasFirstPageComputation where
  hi₀₁ pq := by simp [skeletalPageCore]
  hi₂₃ pq := by simp [skeletalPageCore]

variable {C : Type*} [Category* C] [Abelian C]

/-- The full integer shape has both predecessor and successor at every position. -/
instance (X : SpectralObject C EInt) : X.HasSpectralSequence skeletalPageCore where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq _ rfl
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq (pq - (r, 1 - r)) (by simp)

/-- The actual spectral sequence starting with the relative E₁ page. -/
abbrev skeletalSpectralSequence (X : SpectralObject C EInt) :=
  X.spectralSequence skeletalPageCore

/-- The first page is the middle relative interval in total degree `p + q`. -/
def skeletalFirstPageXIso (X : SpectralObject C EInt) (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page 1).X pq ≅
      (X.H (pq.1 + pq.2)).obj
        (mk₁ (homOfLE (show ((-pq.1 - 1 : ℤ) : EInt) ≤ ((-pq.1 : ℤ) : EInt) by simp))) :=
  X.spectralSequenceFirstPageXIso skeletalPageCore pq _ _ rfl rfl _ rfl

/-- E₂ is the homology of the actual first-page differential. -/
def skeletalSecondPageXIso (X : SpectralObject C EInt) (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page 1).homology pq ≅
      ((X.skeletalSpectralSequence).page 2).X pq :=
  (X.skeletalSpectralSequence).iso 1 2 pq rfl (by omega)

end CategoryTheory.Abelian.SpectralObject

end
