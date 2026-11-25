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

public import MathlibExt.Algebra.Homology.SpectralSequence.IncreasingHomologicalCore

/-!
# Two-column increasing homological spectral sequences

For an increasing homological spectral sequence whose page-two objects
vanish in columns at least two, those columns vanish on every later finite
page.  In columns zero and one the outgoing differential is excluded by the
shape `(-r,r-1)`, while every incoming differential has a zero high-column
source.  The public cycles and homology coordinates therefore give canonical
isomorphisms between all finite pages in the two surviving columns.

This file is page-only.  It chooses no stable page or filtration and makes no
edge, convergence, splitting, or Künneth claim.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.SpectralSequence.IncreasingHomological

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (E : SpectralSequence C
  (fun r : ℤ => ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩) 1)

/-- An increasing homological spectral sequence is concentrated in columns
zero and one on page two.  This is a predicate rather than an instance. -/
def IsTwoColumnAtTwo : Prop :=
  ∀ (p q : ℕ), 2 ≤ p → IsZero ((E.page (2 : ℤ)).X (p, q))

namespace IsTwoColumnAtTwo

variable {E}

/-- Page-two vanishing above column one propagates to every finite page. -/
theorem isZero_page_two_add_X (h : IsTwoColumnAtTwo E)
    (k p q : ℕ) (hp : 2 ≤ p) :
    IsZero ((E.page (((2 + k : ℕ) : ℤ))).X (p, q)) := by
  induction k with
  | zero =>
      simpa only [Nat.add_zero, Nat.cast_ofNat] using h p q hp
  | succ k ih =>
      have hHomology : IsZero
          ((E.page (((2 + k : ℕ) : ℤ))).homology (p, q)) :=
        ShortComplex.isZero_homology_of_isZero_X₂
          (S := (E.page (((2 + k : ℕ) : ℤ))).sc (p, q)) ih
      exact IsZero.of_iso hHomology
        (E.iso (((2 + k : ℕ) : ℤ))
          (((2 + k.succ : ℕ) : ℤ)) (p, q)
          (hrr' := by omega) (hr := by omega)).symm

/-- Every page differential out of a surviving column is shape-zero. -/
theorem page_d_from_survivor_eq_zero (_h : IsTwoColumnAtTwo E)
    (k p q : ℕ) (hp : p ≤ 1) (pq' : ℕ × ℕ) :
    (E.page (((2 + k : ℕ) : ℤ))).d (p, q) pq' = 0 := by
  apply (E.page (((2 + k : ℕ) : ℤ))).shape
  intro hrel
  simp only [ComplexShape.spectralSequenceNat_rel_iff] at hrel
  omega

/-- Every page differential into a surviving column has zero high-column
source. -/
theorem page_d_to_survivor_eq_zero (h : IsTwoColumnAtTwo E)
    (k p q : ℕ) (hp : p ≤ 1) (pq' : ℕ × ℕ) :
    (E.page (((2 + k : ℕ) : ℤ))).d pq' (p, q) = 0 := by
  by_cases hrel :
      (ComplexShape.spectralSequenceNat
        ⟨-(((2 + k : ℕ) : ℤ)), ((2 + k : ℕ) : ℤ) - 1⟩).Rel pq' (p, q)
  · have hpq' : 2 ≤ pq'.1 := by
      simp only [ComplexShape.spectralSequenceNat_rel_iff] at hrel
      omega
    exact (h.isZero_page_two_add_X k pq'.1 pq'.2 hpq').eq_of_src _ _
  · exact (E.page (((2 + k : ℕ) : ℤ))).shape pq' (p, q) hrel

/-- The canonical isomorphism from one surviving-column page object to the
same object on the next page. -/
noncomputable def pageSuccIso (h : IsTwoColumnAtTwo E)
    (k p q : ℕ) (hp : p ≤ 1) :
    (E.page (((2 + k : ℕ) : ℤ))).X (p, q) ≅
      (E.page (((2 + k.succ : ℕ) : ℤ))).X (p, q) :=
  let r : ℤ := ((2 + k : ℕ) : ℤ)
  let K := E.page r
  (K.iCyclesIso (p, q)
      ((ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).next (p, q)) rfl
      (h.page_d_from_survivor_eq_zero k p q hp _)).symm ≪≫
    K.isoHomologyπ
      ((ComplexShape.spectralSequenceNat ⟨-r, r - 1⟩).prev (p, q))
      (p, q) rfl (h.page_d_to_survivor_eq_zero k p q hp _) ≪≫
    E.iso r (((2 + k.succ : ℕ) : ℤ)) (p, q)
      (hrr' := by omega) (hr := by omega)

/-- The canonical finite composite from page two to page `2+k` in a
surviving column. -/
noncomputable def pageTwoToPageIso (h : IsTwoColumnAtTwo E)
    (k p q : ℕ) (hp : p ≤ 1) :
    (E.page (2 : ℤ)).X (p, q) ≅
      (E.page (((2 + k : ℕ) : ℤ))).X (p, q) :=
  Nat.rec
    (E.pageXIsoOfEq (p, q) (2 : ℤ) (((2 + 0 : ℕ) : ℤ)) (by omega))
    (fun k e => e ≪≫ h.pageSuccIso k p q hp) k

end IsTwoColumnAtTwo

end CategoryTheory.SpectralSequence.IncreasingHomological

end
