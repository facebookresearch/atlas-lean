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

public import MathlibExt.Algebra.Homology.SpectralSequence.FirstPageRow
public import MathlibExt.Algebra.Homology.GenericSpectralSequenceMapCompatibility
/-!
# Naturality of row and second-page homology comparisons

The three-term complex of the row at (p−1,p,p+1) is identified with the first-page complex at
(p−1,q),(p,q),(p+1,q) by identity components. These comparisons commute with first-page maps.

The resulting homology comparison is natural for every first-page morphism. For a morphism of
spectral sequences, its successor compatibility gives naturality of the row-homology
isomorphism with E₂.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v uι

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type uι} {c : ComplexShape ι} {K L : HomologicalComplex C c}

/-- Naturality of homology comparison at specified neighboring indices.

For prev(j)=i and next(j)=k, the homology comparison with the three-term complex commutes with
a complex morphism. -/
@[reassoc]
theorem homologyIsoSc'_map_naturality (φ : K ⟶ L) (i j k : ι)
    (hi : c.prev j = i) (hk : c.next j = k) :
    homologyMap φ j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        (ShortComplex.homologyFunctor C).map ((shortComplexFunctor' C c i j k).map φ) := by
  dsimp only [homologyMap, homology, homologyIsoSc', isoSc',
    Iso.app, ShortComplex.homologyMapIso, ShortComplex.homologyFunctor]
  have h := congrArg (fun ψ : K.sc j ⟶ L.sc' i j k => ShortComplex.homologyMap ψ)
    ((natIsoSc' C c i j k hi hk).hom.naturality φ)
  simpa only [ShortComplex.homologyMap_comp, natIsoSc', NatIso.ofComponents] using h

end HomologicalComplex

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S T : SpectralSequence C (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1}

/-- The identity three-term comparison of a first-page row.

Identify the row complex at p−1,p,p+1 with the first-page complex at the corresponding
bidegrees, using identity maps on all three objects. -/
def firstPageRowScIso (S : SpectralSequence C
    (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1) (p q : ℤ) :
    (S.firstPageRow q).sc' (p - 1) p (p + 1) ≅
      (S.page 1).sc' (p - 1, q) (p, q) (p + 1, q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- The row three-term comparison commutes with page maps.

A first-page map and its row restriction form a commuting square with the identity three-term
comparisons. -/
theorem firstPageRowScIso_naturality (φ : S.page 1 ⟶ T.page 1) (p q : ℤ) :
    (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ) (p - 1) p (p + 1)).map
        (firstPageRowMap φ q) ≫ (T.firstPageRowScIso p q).hom =
      (S.firstPageRowScIso p q).hom ≫
        (HomologicalComplex.shortComplexFunctor' C
          (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)) (p - 1, q) (p, q) (p + 1, q)).map φ := by
  apply ShortComplex.Hom.ext <;>
    simp [firstPageRowScIso, firstPageRowMap, ComplexShape.embeddingUpIntRow,
      ComplexShape.Embedding.mk']

/-- Naturality of the first-page row homology isomorphism.

For a first-page morphism φ, its row homology map followed by the target comparison equals the
source comparison followed by H(φ) at (p,q). -/
@[reassoc]
theorem firstPageRowHomologyIso_naturality (φ : S.page 1 ⟶ T.page 1) (p q : ℤ) :
    HomologicalComplex.homologyMap (firstPageRowMap φ q) p ≫
        (T.firstPageRowHomologyIso p q).hom =
      (S.firstPageRowHomologyIso p q).hom ≫ HomologicalComplex.homologyMap φ (p, q) := by
  have hpRow : (ComplexShape.up ℤ).prev p = p - 1 :=
    (ComplexShape.up ℤ).prev_eq' (by change p - 1 + 1 = p; omega)
  have hnRow : (ComplexShape.up ℤ).next p = p + 1 :=
    (ComplexShape.up ℤ).next_eq' rfl
  have hpPage : (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).prev (p, q) = (p - 1, q) :=
    (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).prev_eq' (by
      change (p - 1, q) + (1, 0) = (p, q)
      ext <;> dsimp <;> omega)
  have hnPage : (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).next (p, q) = (p + 1, q) :=
    (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)).next_eq' (by
      change (p, q) + (1, 0) = (p + 1, q)
      ext <;> dsimp; omega)
  let eRowS := (S.firstPageRow q).homologyIsoSc' (p - 1) p (p + 1) hpRow hnRow
  let eRowT := (T.firstPageRow q).homologyIsoSc' (p - 1) p (p + 1) hpRow hnRow
  let ePageS := (S.page 1).homologyIsoSc' (p - 1, q) (p, q) (p + 1, q) hpPage hnPage
  let ePageT := (T.page 1).homologyIsoSc' (p - 1, q) (p, q) (p + 1, q) hpPage hnPage
  let hRow := (ShortComplex.homologyFunctor C).map
    ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ) (p - 1) p (p + 1)).map
      (firstPageRowMap φ q))
  let hPage := (ShortComplex.homologyFunctor C).map
    ((HomologicalComplex.shortComplexFunctor' C
      (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)) (p - 1, q) (p, q) (p + 1, q)).map φ)
  have hRowNat : HomologicalComplex.homologyMap (firstPageRowMap φ q) p ≫ eRowT.hom =
      eRowS.hom ≫ hRow :=
    HomologicalComplex.homologyIsoSc'_map_naturality
      (firstPageRowMap φ q) (p - 1) p (p + 1) hpRow hnRow
  have hPageNat : HomologicalComplex.homologyMap φ (p, q) ≫ ePageT.hom =
      ePageS.hom ≫ hPage :=
    HomologicalComplex.homologyIsoSc'_map_naturality
      φ (p - 1, q) (p, q) (p + 1, q) hpPage hnPage
  have hMiddle : hRow ≫ (ShortComplex.homologyFunctor C).map (T.firstPageRowScIso p q).hom =
      (ShortComplex.homologyFunctor C).map (S.firstPageRowScIso p q).hom ≫ hPage := by
    have h := congrArg (ShortComplex.homologyFunctor C).map
      (firstPageRowScIso_naturality φ p q)
    simpa only [Functor.map_comp] using h
  apply (cancel_mono ePageT.hom).mp
  simp only [firstPageRowHomologyIso, HomologicalComplex.restrictionHomologyIso,
    Iso.trans_hom, Iso.symm_hom, ShortComplex.homologyMapIso_hom, Category.assoc]
  change HomologicalComplex.homologyMap (firstPageRowMap φ q) p ≫
      eRowT.hom ≫ (ShortComplex.homologyFunctor C).map (T.firstPageRowScIso p q).hom ≫
        ePageT.inv ≫ ePageT.hom =
    eRowS.hom ≫ (ShortComplex.homologyFunctor C).map (S.firstPageRowScIso p q).hom ≫
      ePageS.inv ≫ HomologicalComplex.homologyMap φ (p, q) ≫ ePageT.hom
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hRowNat, Category.assoc, hMiddle]
  rw [hPageNat]
  simp only [Iso.inv_hom_id_assoc]

/-- Naturality of the row comparison with the second page.

For a spectral-sequence morphism, the first-row homology map commutes with the canonical E₂
comparison and the second-page component map. -/
@[reassoc]
theorem firstPageRowSecondPageIso_naturality (φ : S ⟶ T) (p q : ℤ) :
    HomologicalComplex.homologyMap (firstPageRowMap (φ.hom 1 le_rfl) q) p ≫
        (T.firstPageRowSecondPageIso p q).hom =
      (S.firstPageRowSecondPageIso p q).hom ≫ (φ.hom 2 (by omega)).f (p, q) := by
  simp only [firstPageRowSecondPageIso, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, firstPageRowHomologyIso_naturality, Category.assoc,
    φ.comm 1 2 (p, q) rfl le_rfl]

end CategoryTheory.SpectralSequence


end
