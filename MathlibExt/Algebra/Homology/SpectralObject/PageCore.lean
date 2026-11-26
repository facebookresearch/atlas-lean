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
# Skeletal cohomological pages on the integer grid

The page prescription indexed by EInt begins at E₁. At (p,q) its total
cohomological degree is p+q, with cuts
−p−r≤−p−1≤−p≤−p+r−1 on page r.
The differential sends (p,q) to (p+r,q+1−r), so d₁ has bidegree (1,0).

For a spectral object in an abelian category, the full integer grid
satisfies the required boundary conditions. Its first page is the relative
interval H^{p+q}(−p−1,−p), and the second page is the homology of that
first-page differential. Both page coordinates range over all integers.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

/-- The EInt-indexed spectral-sequence prescription starting at page 1,
with degree p+q, cuts i₀=−p−r, i₁=−p−1, i₂=−p, i₃=−p+r−1,
and page-r differential bidegree (r,1−r) on ℤ×ℤ. -/
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

/-- For a spectral object X in an abelian category, indexed by EInt, the
integer-grid page prescription satisfies the spectral-sequence boundary
condition: every page position has both a predecessor and a successor
for the differential bidegree (r,1−r). -/
instance (X : SpectralObject C EInt) : X.HasSpectralSequence skeletalPageCore where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq _ rfl
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq (pq - (r, 1 - r)) (by simp)

/-- For an EInt-indexed spectral object X in an abelian category, the
spectral sequence beginning at E₁ with cuts
−p−r≤−p−1≤−p≤−p+r−1, total degree p+q and differential
bidegree (r,1−r). -/
abbrev skeletalSpectralSequence (X : SpectralObject C EInt) :=
  X.spectralSequence skeletalPageCore

/-- For an EInt-indexed spectral object X in an abelian category, the
canonical first-page isomorphism
E₁^{p,q} ≅ H_X^{p+q}(−p−1,−p) at every integer pair (p,q). -/
def skeletalFirstPageXIso (X : SpectralObject C EInt) (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page 1).X pq ≅
      (X.H (pq.1 + pq.2)).obj
        (mk₁ (homOfLE (show ((-pq.1 - 1 : ℤ) : EInt) ≤ ((-pq.1 : ℤ) : EInt) by simp))) :=
  X.spectralSequenceFirstPageXIso skeletalPageCore pq _ _ rfl rfl _ rfl

/-- For an EInt-indexed spectral object X in an abelian category, the
canonical isomorphism from the homology of its first-page complex at
(p,q) to E₂^{p,q}. The first-page differential has bidegree (1,0). -/
def skeletalSecondPageXIso (X : SpectralObject C EInt) (pq : ℤ × ℤ) :
    ((X.skeletalSpectralSequence).page 1).homology pq ≅
      ((X.skeletalSpectralSequence).page 2).X pq :=
  (X.skeletalSpectralSequence).iso 1 2 pq rfl (by omega)

end CategoryTheory.Abelian.SpectralObject

end
