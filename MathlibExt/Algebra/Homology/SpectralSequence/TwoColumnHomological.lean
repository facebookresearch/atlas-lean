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
# Finite survivor isomorphisms for two-column homological spectral sequences

Let E be a spectral sequence in an abelian category whose page-r differential has bidegree
(-r,r−1) on ℕ². Assume E^2_{p,q}=0 for all p≥2. These high-column terms remain zero on every
page 2+k. For p≤1 and r≥2, outgoing differentials are excluded by the nonnegative horizontal
index, and every incoming differential has a zero high-column source.

Hence cycles and homology projection identify E^r_{p,q} canonically with its homology and then
with E^{r+1}_{p,q}. Their finite composites give E^2_{p,q}≅E^{2+k}_{p,q} for k∈ℕ in columns zero
and one. The result concerns these specified page coordinates; it does not require a
filtered-complex realization. The category's object and morphism universes are arbitrary.
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

/-- Let C be abelian and E a spectral sequence on ℕ² starting at page one, with page-r differential
of bidegree (-r,r−1). This condition is E^2_{p,q}=0 for every p,q∈ℕ with p≥2. It permits
arbitrary second-page objects in columns p=0 and p=1. -/
def IsTwoColumnAtTwo : Prop :=
  ∀ (p q : ℕ), 2 ≤ p → IsZero ((E.page (2 : ℤ)).X (p, q))

namespace IsTwoColumnAtTwo

variable {E}

/-- Let C be abelian and E an increasing homological spectral sequence indexed by (p,q)∈ℕ², starting
at page one and with page-r differential of bidegree (-r,r−1). Assume E^2_{p,q}=0 whenever p≥2.
For k,p,q∈ℕ with p≥2, the object E^{2+k}_{p,q} is zero. Vanishing propagates because the next
page is the homology of the preceding page at the same bidegree. -/
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

/-- Let C be abelian and E an increasing homological spectral sequence indexed by (p,q)∈ℕ², starting
at page one and with page-r differential of bidegree (-r,r−1). Assume E^2_{p,q}=0 whenever p≥2.
For k,p,q∈ℕ with p≤1 and any (a,b)∈ℕ², the differential d_{2+k}:E^{2+k}_{p,q}→E^{2+k}_{a,b} is
zero. Its allowed target would have horizontal index p−(2+k)<0, outside the nonnegative indexing
set. -/
theorem page_d_from_survivor_eq_zero (_h : IsTwoColumnAtTwo E)
    (k p q : ℕ) (hp : p ≤ 1) (pq' : ℕ × ℕ) :
    (E.page (((2 + k : ℕ) : ℤ))).d (p, q) pq' = 0 := by
  apply (E.page (((2 + k : ℕ) : ℤ))).shape
  intro hrel
  simp only [ComplexShape.spectralSequenceNat_rel_iff] at hrel
  omega

/-- Let C be abelian and E an increasing homological spectral sequence indexed by (p,q)∈ℕ², starting
at page one and with page-r differential of bidegree (-r,r−1). Assume E^2_{p,q}=0 whenever p≥2.
For k,p,q∈ℕ with p≤1 and any (a,b)∈ℕ², the differential d_{2+k}:E^{2+k}_{a,b}→E^{2+k}_{p,q} is
zero. If the shape allows the arrow then a=p+2+k≥2, so its source vanishes on that page; all
other arrows are shape-zero. -/
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

/-- Let C be abelian and E an increasing homological spectral sequence indexed by (p,q)∈ℕ², starting
at page one and with page-r differential of bidegree (-r,r−1). Assume E^2_{p,q}=0 whenever p≥2.
For k,p,q∈ℕ with p≤1 and r=2+k, this isomorphism E^r_{p,q}≅E^{r+1}_{p,q} is the inverse
cycles-inclusion isomorphism followed by the homology projection and the spectral successor-page
isomorphism. Outgoing and incoming differential vanishing make the first two arrows invertible. -/
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

/-- Let C be abelian and E an increasing homological spectral sequence indexed by (p,q)∈ℕ², starting
at page one and with page-r differential of bidegree (-r,r−1). Assume E^2_{p,q}=0 whenever p≥2.
For k,p,q∈ℕ with p≤1, this is the canonical composite E^2_{p,q}≅E^{2+k}_{p,q}. At k=0 it is the
identity page coordinate, and each successor appends the cycles-and-homology successor
isomorphism in the same bidegree. -/
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
