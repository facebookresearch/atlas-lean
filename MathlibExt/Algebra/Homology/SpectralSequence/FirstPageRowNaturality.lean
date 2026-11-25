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
# Naturality of the actual first-page row homology

The row extraction uses the original native differential. Its chosen
short complex is compared with the native bidegree short complex by the
identity on all three original objects. Naturality of the actual homology
functor and of the native spectral-sequence successor gives the canonical
row homology comparison with the actual second page.
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

/-- The actual homology comparison with specified neighboring indices is
natural for the original complex map, by the native short-complex natural isomorphism. -/
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

/-- The row and native first-page short complexes use identical original
objects at the chosen neighboring indices. -/
def firstPageRowScIso (S : SpectralSequence C
    (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1) (p q : ℤ) :
    (S.firstPageRow q).sc' (p - 1) p (p + 1) ≅
      (S.page 1).sc' (p - 1, q) (p, q) (p + 1, q) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl)

/-- The identity short-complex comparison commutes with the actual first-page map. -/
theorem firstPageRowScIso_naturality (φ : S.page 1 ⟶ T.page 1) (p q : ℤ) :
    (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℤ) (p - 1) p (p + 1)).map
        (firstPageRowMap φ q) ≫ (T.firstPageRowScIso p q).hom =
      (S.firstPageRowScIso p q).hom ≫
        (HomologicalComplex.shortComplexFunctor' C
          (ComplexShape.up' (⟨1, 0⟩ : ℤ × ℤ)) (p - 1, q) (p, q) (p + 1, q)).map φ := by
  apply ShortComplex.Hom.ext <;>
    simp [firstPageRowScIso, firstPageRowMap, ComplexShape.embeddingUpIntRow,
      ComplexShape.Embedding.mk']

/-- The canonical actual row homology comparison is natural for each
original first-page map. -/
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

/-- A genuine native spectral-sequence morphism preserves the canonical
actual row homology identification with the actual native second page. -/
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
