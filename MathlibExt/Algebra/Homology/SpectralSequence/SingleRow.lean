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

public import Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Single-row cohomological spectral sequences

If the first page of a cohomological spectral sequence is supported in row
zero, every later page has the same support and all differentials from page
two onward vanish. The resulting page isomorphisms are the composites of
the original successor homology comparisons and are natural in morphisms
of spectral sequences.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : CohomologicalSpectralSequence C 1)

/-- A zero row on the actual first page stays zero on every later page. -/
theorem isZero_page_of_firstPage_off_row
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((S.page 1).X (p, q)))
    (r : ℤ) (hr : 1 ≤ r) (p q : ℤ) (hq : q ≠ 0) :
    IsZero ((S.page r hr).X (p, q)) := by
  have h : ∀ k : ℕ, IsZero ((S.page ((k : ℤ) + 1) (by omega)).X (p, q)) := by
    intro k
    induction k with
    | zero =>
      exact (hrow p q hq).of_iso
        (S.pageXIsoOfEq (p, q) (((0 : ℕ) : ℤ) + 1) 1 (by omega) (by omega))
    | succ k ih =>
      have hz : IsZero ((S.page ((k : ℤ) + 1) (by omega)).homology (p, q)) :=
        ShortComplex.isZero_homology_of_isZero_X₂ _ ih
      exact hz.of_iso (S.iso ((k : ℤ) + 1) (((k + 1 : ℕ) : ℤ) + 1)
        (p, q) (by omega) (by omega)).symm
  have heq : (((r - 1).toNat : ℤ) + 1) = r := by omega
  exact (h (r - 1).toNat).of_iso
    (S.pageXIsoOfEq (p, q) r (((r - 1).toNat : ℤ) + 1) heq.symm hr)

/-- The ordinary coefficient row forces every actual differential from page two onward to vanish. -/
theorem page_d_eq_zero_of_firstPage_off_row
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((S.page 1).X (p, q)))
    (r : ℤ) (hr : 2 ≤ r) (pq pq' : ℤ × ℤ) :
    (S.page r (by omega)).d pq pq' = 0 := by
  by_cases hq : pq.2 = 0
  · by_cases hrel : (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel pq pq'
    · have hq' : pq'.2 ≠ 0 := by
        change pq + (r, 1 - r) = pq' at hrel
        have h := congrArg (fun x : ℤ × ℤ => x.2) hrel
        dsimp at h
        omega
      exact (S.isZero_page_of_firstPage_off_row hrow r (by omega)
        pq'.1 pq'.2 hq').eq_of_tgt _ _
    · exact (S.page r (by omega)).shape pq pq' hrel
  · exact (S.isZero_page_of_firstPage_off_row hrow r (by omega)
      pq.1 pq.2 hq).eq_of_src _ _

/-- The canonical successor comparison for an actual ordinary row collapse. -/
def singleRowSuccessorIso
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((S.page 1).X (p, q)))
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (S.page r (by omega)).X pq ≅ (S.page (r + 1) (by omega)).X pq :=
  (ShortComplex.HomologyData.ofZeros ((S.page r (by omega)).sc pq)
    (S.page_d_eq_zero_of_firstPage_off_row hrow r hr _ _)
    (S.page_d_eq_zero_of_firstPage_off_row hrow r hr _ _)).left.homologyIso.symm ≪≫
      S.iso r (r + 1) pq rfl (by omega)

/-- A finite composite of the actual canonical ordinary successor comparisons. -/
def singleRowPageIsoNat
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((S.page 1).X (p, q)))
    (pq : ℤ × ℤ) : ∀ k : ℕ, (S.page 2).X pq ≅ (S.page ((k : ℤ) + 2) (by omega)).X pq
  | 0 => S.pageXIsoOfEq pq 2 (((0 : ℕ) : ℤ) + 2) (by omega) (by omega)
  | k + 1 => singleRowPageIsoNat hrow pq k ≪≫
      S.singleRowSuccessorIso hrow ((k : ℤ) + 2) (by omega) pq ≪≫
        S.pageXIsoOfEq pq (((k : ℤ) + 2) + 1) (((k + 1 : ℕ) : ℤ) + 2)
          (by omega) (by omega)

/-- The actual second page identifies canonically with every later page under the ordinary row axiom. -/
def singleRowPageIso
    (hrow : ∀ p q : ℤ, q ≠ 0 → IsZero ((S.page 1).X (p, q)))
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (S.page 2).X pq ≅ (S.page r (by omega)).X pq :=
  S.singleRowPageIsoNat hrow pq (r - 2).toNat ≪≫
    S.pageXIsoOfEq pq (((r - 2).toNat : ℤ) + 2) r (by omega) (by omega)

variable {S}
variable {T : CohomologicalSpectralSequence C 1}

namespace Hom

private theorem pageXIsoOfEq_naturality (f : S ⟶ T) (pq : ℤ × ℤ)
    (r r' : ℤ) (h : r = r') (hr : 1 ≤ r) :
    (f.hom r hr).f pq ≫ (T.pageXIsoOfEq pq r r' h hr).hom =
      (S.pageXIsoOfEq pq r r' h hr).hom ≫ (f.hom r' (by omega)).f pq := by
  subst r'
  simp only [pageXIsoOfEq, eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- Canonical ordinary successor collapse is natural for actual morphisms of spectral sequences. -/
@[reassoc]
theorem singleRowSuccessorIso_naturality (f : S ⟶ T)
    (hS : ∀ p q : ℤ, q ≠ 0 → IsZero ((S.page 1).X (p, q)))
    (hT : ∀ p q : ℤ, q ≠ 0 → IsZero ((T.page 1).X (p, q)))
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (f.hom r (by omega)).f pq ≫ (T.singleRowSuccessorIso hT r hr pq).hom =
      (S.singleRowSuccessorIso hS r hr pq).hom ≫ (f.hom (r + 1) (by omega)).f pq := by
  let a : (S.page r (by omega)).homology pq ≅ (S.page r (by omega)).X pq :=
    (ShortComplex.HomologyData.ofZeros ((S.page r (by omega)).sc pq)
      (S.page_d_eq_zero_of_firstPage_off_row hS r hr _ _)
      (S.page_d_eq_zero_of_firstPage_off_row hS r hr _ _)).left.homologyIso
  let b : (T.page r (by omega)).homology pq ≅ (T.page r (by omega)).X pq :=
    (ShortComplex.HomologyData.ofZeros ((T.page r (by omega)).sc pq)
      (T.page_d_eq_zero_of_firstPage_off_row hT r hr _ _)
      (T.page_d_eq_zero_of_firstPage_off_row hT r hr _ _)).left.homologyIso
  let γ := ShortComplex.LeftHomologyMapData.ofZeros
    ((HomologicalComplex.shortComplexFunctor C
      (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) pq).map (f.hom r (by omega)))
    (S.page_d_eq_zero_of_firstPage_off_row hS r hr _ _)
    (S.page_d_eq_zero_of_firstPage_off_row hS r hr _ _)
    (T.page_d_eq_zero_of_firstPage_off_row hT r hr _ _)
    (T.page_d_eq_zero_of_firstPage_off_row hT r hr _ _)
  have hc : a.inv ≫ HomologicalComplex.homologyMap (f.hom r (by omega)) pq =
      (f.hom r (by omega)).f pq ≫ b.inv := by
    rw [show HomologicalComplex.homologyMap (f.hom r (by omega)) pq =
      a.hom ≫ (f.hom r (by omega)).f pq ≫ b.inv from
        γ.homologyMap_eq]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change (f.hom r (by omega)).f pq ≫ (b.inv ≫ (T.iso r (r + 1) pq).hom) =
    (a.inv ≫ (S.iso r (r + 1) pq).hom) ≫ (f.hom (r + 1) (by omega)).f pq
  rw [← Category.assoc, ← hc, Category.assoc,
    f.comm r (r + 1) pq rfl (by omega), ← Category.assoc]

/-- Every finite canonical ordinary page comparison is natural in spectral sequences. -/
@[reassoc]
theorem singleRowPageIsoNat_naturality (f : S ⟶ T)
    (hS : ∀ p q : ℤ, q ≠ 0 → IsZero ((S.page 1).X (p, q)))
    (hT : ∀ p q : ℤ, q ≠ 0 → IsZero ((T.page 1).X (p, q)))
    (pq : ℤ × ℤ) (k : ℕ) :
    (f.hom 2).f pq ≫ (T.singleRowPageIsoNat hT pq k).hom =
      (S.singleRowPageIsoNat hS pq k).hom ≫ (f.hom ((k : ℤ) + 2) (by omega)).f pq := by
  induction k with
  | zero => exact f.pageXIsoOfEq_naturality pq 2 (((0 : ℕ) : ℤ) + 2) (by omega) (by omega)
  | succ k ih =>
    change (f.hom 2).f pq ≫
        ((T.singleRowPageIsoNat hT pq k).hom ≫
          (T.singleRowSuccessorIso hT ((k : ℤ) + 2) (by omega) pq).hom ≫
            (T.pageXIsoOfEq pq (((k : ℤ) + 2) + 1) (((k + 1 : ℕ) : ℤ) + 2)
              (by omega) (by omega)).hom) =
      ((S.singleRowPageIsoNat hS pq k).hom ≫
        (S.singleRowSuccessorIso hS ((k : ℤ) + 2) (by omega) pq).hom ≫
          (S.pageXIsoOfEq pq (((k : ℤ) + 2) + 1) (((k + 1 : ℕ) : ℤ) + 2)
            (by omega) (by omega)).hom) ≫ (f.hom (((k + 1 : ℕ) : ℤ) + 2) (by omega)).f pq
    rw [← Category.assoc, ih]
    simp only [Category.assoc]
    rw [f.singleRowSuccessorIso_naturality_assoc hS hT,
      f.pageXIsoOfEq_naturality]

/-- Ordinary row collapse from page two to any later integer page is natural. -/
@[reassoc]
theorem singleRowPageIso_naturality (f : S ⟶ T)
    (hS : ∀ p q : ℤ, q ≠ 0 → IsZero ((S.page 1).X (p, q)))
    (hT : ∀ p q : ℤ, q ≠ 0 → IsZero ((T.page 1).X (p, q)))
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    (f.hom 2).f pq ≫ (T.singleRowPageIso hT r hr pq).hom =
      (S.singleRowPageIso hS r hr pq).hom ≫ (f.hom r (by omega)).f pq := by
  dsimp only [singleRowPageIso, Iso.trans_hom]
  rw [← Category.assoc, f.singleRowPageIsoNat_naturality hS hT, Category.assoc,
    f.pageXIsoOfEq_naturality, ← Category.assoc]

end Hom

end CategoryTheory.SpectralSequence
