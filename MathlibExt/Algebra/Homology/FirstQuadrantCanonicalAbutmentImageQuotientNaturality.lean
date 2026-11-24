/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentCokernelNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentCurrentImageNaturality

/-!
# Naturality of the canonical-abutment nested-image quotient

A bicomplex map induces a canonical map between the nested-image quotient
presentations of the canonical abutment.  The comparison from the canonical
fixed `E` object to that quotient is natural: first transport through the
inverse canonical cokernel comparison, then use generic naturality of the
biproduct-to-image-quotient comparison.

This file does not construct the graded cokernel bridge or the final graded
naturality theorem.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Map between the canonical-abutment nested-image quotients induced by a
bicomplex morphism. -/
noncomputable def horizontalCanonicalAbutmentImageQuotientMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentImageQuotient K p q ⟶
      horizontalCanonicalAbutmentImageQuotient L p q := by
  let φ := horizontalCompleteFiltrationSpectralObjectMap f
  let n : ℤ := -((p + q : ℕ) : ℤ)
  let α := (φ.hom n).app
    (mk₁ (horizontalCanonicalAbutmentLowerMap p))
  let β := (φ.hom n).app
    (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p))
  let τ := (φ.hom n).app
    (mk₁ (horizontalCanonicalAbutmentTotalMap p q))
  have ha : horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫ β =
      α ≫ horizontalCanonicalAbutmentPreviousHomologyMap L p q := by
    simp [φ, n, α, β,
      horizontalCanonicalAbutmentPreviousHomologyMap]
  have hb : horizontalCanonicalAbutmentToUpperHomologyMap K p q ≫ τ =
      β ≫ horizontalCanonicalAbutmentToUpperHomologyMap L p q := by
    simp [φ, n, β, τ,
      horizontalCanonicalAbutmentToUpperHomologyMap]
  exact CategoryTheory.imageQuotientMap
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
    (horizontalCanonicalAbutmentToUpperHomologyMap K p q)
    (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
    (horizontalCanonicalAbutmentToUpperHomologyMap L p q)
    α β τ ha hb

/-- The canonical nested-image quotient map computes on the cokernel
projection, with right leg the landed current-image map. -/
@[reassoc]
theorem horizontalCanonicalAbutmentImageQuotientMapOfBicomplex_π
    (f : K ⟶ L) (p q : ℕ) :
    cokernel.π (CategoryTheory.imageCompMap
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentToUpperHomologyMap K p q)) ≫
        horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q =
      horizontalCanonicalAbutmentCurrentImageMapOfBicomplex f p q ≫
        cokernel.π (CategoryTheory.imageCompMap
          (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
          (horizontalCanonicalAbutmentToUpperHomologyMap L p q)) := by
  simp [horizontalCanonicalAbutmentImageQuotientMapOfBicomplex,
    horizontalCanonicalAbutmentCurrentImageMapOfBicomplex,
    horizontalCanonicalAbutmentCurrentHomologySquareOfBicomplex,
    CategoryTheory.cokernel_π_imageQuotientMap]
  congr 2

/-- The comparison from the canonical fixed `E` object to the nested-image
quotient is natural under bicomplex morphisms. -/
theorem horizontalCanonicalAbutmentImageQuotientIso_naturality
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentImageQuotientIso L p q).hom =
      (horizontalCanonicalAbutmentImageQuotientIso K p q).hom ≫
        horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q := by
  let φ := horizontalCompleteFiltrationSpectralObjectMap f
  let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -((p + q : ℕ) : ℤ)
  let α := (φ.hom n₁).app
    (mk₁ (horizontalCanonicalAbutmentLowerMap p))
  let χ := (φ.hom n₀).app
    (mk₁ (horizontalCanonicalAbutmentUpperMap p q))
  let β := (φ.hom n₁).app
    (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p))
  let τ := (φ.hom n₁).app
    (mk₁ (horizontalCanonicalAbutmentTotalMap p q))
  have ha : horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫ β =
      α ≫ horizontalCanonicalAbutmentPreviousHomologyMap L p q := by
    simp [φ, n₁, α, β,
      horizontalCanonicalAbutmentPreviousHomologyMap]
  have hx : horizontalCanonicalAbutmentBoundaryMap K p q ≫ β =
      χ ≫ horizontalCanonicalAbutmentBoundaryMap L p q := by
    simp [φ, n₀, n₁, χ, β,
      horizontalCanonicalAbutmentBoundaryMap]
  have hb : horizontalCanonicalAbutmentToUpperHomologyMap K p q ≫ τ =
      β ≫ horizontalCanonicalAbutmentToUpperHomologyMap L p q := by
    simp [φ, n₁, β, τ,
      horizontalCanonicalAbutmentToUpperHomologyMap]
  let eK := horizontalCanonicalAbutmentCokernelIso K p q
  let eL := horizontalCanonicalAbutmentCokernelIso L p q
  let bq := horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex f p q
  let iqK := CategoryTheory.imageQuotientBiprodIso
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
    (horizontalCanonicalAbutmentBoundaryMap K p q)
    (horizontalCanonicalAbutmentToUpperHomologyMap K p q)
    (horizontalCanonicalAbutmentBoundary_comp_toUpper K p q)
    (horizontalCanonicalAbutmentBoundaryToUpper_exact K p q)
  let iqL := CategoryTheory.imageQuotientBiprodIso
    (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
    (horizontalCanonicalAbutmentBoundaryMap L p q)
    (horizontalCanonicalAbutmentToUpperHomologyMap L p q)
    (horizontalCanonicalAbutmentBoundary_comp_toUpper L p q)
    (horizontalCanonicalAbutmentBoundaryToUpper_exact L p q)
  let iqMap := horizontalCanonicalAbutmentImageQuotientMapOfBicomplex f p q
  have hCok := horizontalCanonicalAbutmentCokernelIso_naturality f p q
  have hCokInv :
      horizontalCanonicalAbutmentMapOfBicomplex f p q ≫ eL.inv =
        eK.inv ≫ bq := by
    apply (cancel_epi eK.hom).1
    simp only [eK.hom_inv_id_assoc]
    rw [← Category.assoc, ← hCok]
    simp [eL, bq, Category.assoc]
  have hIQ : bq ≫ iqL.hom = iqK.hom ≫ iqMap := by
    simpa [φ, n₀, n₁, α, χ, β, τ, eK, eL, bq, iqK, iqL, iqMap,
      horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex,
      horizontalCanonicalAbutmentImageQuotientMapOfBicomplex] using
      CategoryTheory.imageQuotientBiprodIso_naturality
        (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
        (horizontalCanonicalAbutmentBoundaryMap K p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap K p q)
        (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
        (horizontalCanonicalAbutmentBoundaryMap L p q)
        (horizontalCanonicalAbutmentToUpperHomologyMap L p q)
        α χ β τ ha hx hb
        (horizontalCanonicalAbutmentBoundary_comp_toUpper K p q)
        (horizontalCanonicalAbutmentBoundary_comp_toUpper L p q)
        (horizontalCanonicalAbutmentBoundaryToUpper_exact K p q)
        (horizontalCanonicalAbutmentBoundaryToUpper_exact L p q)
  dsimp only [horizontalCanonicalAbutmentImageQuotientIso, Iso.trans_hom,
    Iso.symm_hom]
  calc
    horizontalCanonicalAbutmentMapOfBicomplex f p q ≫
          (eL.inv ≫ iqL.hom) =
        (horizontalCanonicalAbutmentMapOfBicomplex f p q ≫ eL.inv) ≫
          iqL.hom := (Category.assoc _ _ _).symm
    _ = (eK.inv ≫ bq) ≫ iqL.hom := by rw [hCokInv]
    _ = eK.inv ≫ (bq ≫ iqL.hom) := Category.assoc _ _ _
    _ = eK.inv ≫ (iqK.hom ≫ iqMap) := by rw [hIQ]
    _ = (eK.inv ≫ iqK.hom) ≫ iqMap := (Category.assoc _ _ _).symm

end HomologicalComplex₂

end
