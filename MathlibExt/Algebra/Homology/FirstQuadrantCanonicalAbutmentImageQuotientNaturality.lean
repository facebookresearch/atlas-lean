/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentCokernelNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantCanonicalAbutmentCurrentImageNaturality

/-!
# Naturality of the canonical abutment nested-image quotient

For a first-quadrant bicomplex K in an abelian category and p,q∈ℕ, set m=p+q, ℓ=(p:ℤ)−1 and
u=m+1. Let a_K:H^{-m}_K(⊥,ℓ)→H^{-m}_K(⊥,p) and b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u) be the relative
cochain homology maps of the complete horizontal filtration. Their nested-image quotient is
Q_K=coker(image(a_K≫b_K)→image b_K).

A bicomplex morphism f:K→L induces compatible maps on the three relative homology objects and
therefore on Q_K. The quotient map commutes with the projection from image b_K. The canonical
abutment term E_K at cuts ⊥≤ℓ≤p≤u and degree -m is isomorphic to Q_K, and this isomorphism
commutes with the spectral E-map and the quotient map. The construction uses the exact
connecting sequence with incoming arrow δ:H^{-m-1}_K(p,u)→H^{-m}_K(⊥,p).
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

/-- Let C be an abelian category, f:K→L a morphism of bicomplexes of shape (down ℕ,down ℕ), and
p,q∈ℕ. Set m=p+q, ℓ=(p:ℤ)−1 and u=m+1. For relative cochain homology of the complete horizontal
filtration, write a_K:H^{-m}_K(⊥,ℓ)→H^{-m}_K(⊥,p), b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u), and
Q_K=coker(image(a_K≫b_K)→image b_K). The spectral morphism of f gives maps α,β,τ on these three
homology objects with a_K≫β=α≫a_L and b_K≫τ=β≫b_L. They induce this quotient morphism Q_K→Q_L. -/
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

/-- For a morphism f:K→L of first-quadrant bicomplexes in an abelian category and p,q∈ℕ, put m=p+q,
ℓ=(p:ℤ)−1 and u=m+1. Let a:H^{-m}(⊥,ℓ)→H^{-m}(⊥,p), b:H^{-m}(⊥,p)→H^{-m}(⊥,u), and
Q=coker(image(a≫b)→image b). If Q_f:Q_K→Q_L is the induced quotient map, I_f:image b_K→image b_L
the current image map, and π_K,π_L the cokernel projections, then π_K≫Q_f=I_f≫π_L. -/
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

/-- Let f:K→L be a first-quadrant bicomplex morphism in an abelian category and p,q∈ℕ. Put m=p+q,
ℓ=(p:ℤ)−1 and u=m+1. Let E_K be the canonical spectral abutment term at cuts ⊥≤ℓ≤p≤u and degree
-m. For a_K:H^{-m}_K(⊥,ℓ)→H^{-m}_K(⊥,p) and b_K:H^{-m}_K(⊥,p)→H^{-m}_K(⊥,u), set
Q_K=coker(image(a_K≫b_K)→image b_K). The canonical isomorphism e_K:E_K≅Q_K is natural:
E_f≫e_L.hom=e_K.hom≫Q_f, where E_f is the spectral E-map and Q_f the induced nested-image
quotient map. -/
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
