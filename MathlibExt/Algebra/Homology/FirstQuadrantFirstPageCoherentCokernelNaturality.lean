/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageColumnNaturality
public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageDifferential
public import
  MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFiniteComparison

/-!
# Naturality of the coherent first-page cokernel

A bicomplex map commutes with projection from a horizontal filtration stage
to its top column.  Transporting this square to the complete filtration gives
a map between the cokernels of coherent first-page windows, and the chosen
coherent cokernel isomorphisms identify that map with the direct-column map.

This file does not construct a mapping-cone, homology, or spectral-page
naturality comparison.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

section Projection

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

omit [HasZeroObject C] in
/-- A finite-stage bicomplex map commutes with projection onto the top
horizontal-column summand. -/
@[reassoc]
theorem horizontalFilteredTotalMapOfBicomplex_topProjection
    (f : K ⟶ L) (p q : ℕ) :
    horizontalFilteredTotalMapOfBicomplex f p (p + q) ≫
        horizontalFilteredTopProjection L p q =
      horizontalFilteredTopProjection K p q ≫ (f.f p).f q := by
  apply Sigma.hom_ext
  intro idx
  change horizontalFilteredTotalι K p (p + q) idx ≫
      (horizontalFilteredTotalMapOfBicomplex f p (p + q) ≫
        horizontalFilteredTopProjection L p q) =
    horizontalFilteredTotalι K p (p + q) idx ≫
      (horizontalFilteredTopProjection K p q ≫ (f.f p).f q)
  simp only [← Category.assoc,
    horizontalFilteredTotalι_mapOfBicomplex,
    horizontalFilteredTotalι_topProjection]
  split_ifs with h
  · subst idx
    rw [Category.assoc, horizontalFilteredTopι_topProjection,
      Category.comp_id]
    dsimp [horizontalFilteredTopIndex]
    simp
  · rw [Category.assoc,
      horizontalFilteredTotalι_topProjection,
      dite_eq_right h, comp_zero, zero_comp]

/-- Supported-degree naturality of the extended finite-stage direct-column
projection. -/
@[reassoc]
theorem horizontalNaturalDirectColumnProjectionComponent_naturality
    (f : K ⟶ L) (p q : ℕ) :
    (HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat).f (-(p : ℤ) - q) ≫
        horizontalNaturalDirectColumnProjectionComponent L p q =
      horizontalNaturalDirectColumnProjectionComponent K p q ≫
        (horizontalDirectColumnCochainMap f p).f (-(p : ℤ) - q) := by
  dsimp [horizontalNaturalDirectColumnProjectionComponent]
  rw [HomologicalComplex.extendMap_f
    (K := horizontalFilteredTotalComplex K p)
    (L := horizontalFilteredTotalComplex L p)
    (φ := horizontalFilteredTotalComplexMapOfBicomplex f p)
    (e := ComplexShape.embeddingDownNat)
    (i := p + q) (i' := -(p : ℤ) - q)
    (by rw [ComplexShape.embeddingDownNat_f]; push_cast; omega)]
  rw [horizontalDirectColumnCochainMap_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  dsimp only [horizontalFilteredTotalComplexMapOfBicomplex]
  change _ ≫ horizontalFilteredTotalMapOfBicomplex f p (p + q) ≫
      horizontalFilteredTopProjection L p q ≫ _ =
    _ ≫ horizontalFilteredTopProjection K p q ≫
      (f.f p).f q ≫ _
  slice_lhs 2 3 =>
    rw [horizontalFilteredTotalMapOfBicomplex_topProjection]
  simp only [Category.assoc]

/-- The extended finite-stage direct-column projection is natural under
bicomplex maps. -/
@[reassoc]
theorem horizontalNaturalDirectColumnProjectionMap_naturality
    (f : K ⟶ L) (p : ℕ) :
    HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat ≫
        horizontalNaturalDirectColumnProjectionMap L p =
      horizontalNaturalDirectColumnProjectionMap K p ≫
        horizontalDirectColumnCochainMap f p := by
  apply HomologicalComplex.Hom.ext
  funext i
  change
    (HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat).f i ≫
        horizontalNaturalDirectColumnProjection L p i =
      horizontalNaturalDirectColumnProjection K p i ≫
        (horizontalDirectColumnCochainMap f p).f i
  by_cases hi : -(p : ℤ) < i
  · rw [horizontalNaturalDirectColumnProjection_eq_zero_of_lt L p i hi,
      horizontalNaturalDirectColumnProjection_eq_zero_of_lt K p i hi,
      comp_zero, zero_comp]
  · have hile : i ≤ -(p : ℤ) := by lia
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = -(p : ℤ) - q :=
      ⟨horizontalColumnDegree p i,
        horizontalColumnDegree_spec p i hile⟩
    rw [horizontalNaturalDirectColumnProjection_eq_component,
      horizontalNaturalDirectColumnProjection_eq_component]
    exact horizontalNaturalDirectColumnProjectionComponent_naturality
      f p q

set_option linter.flexible false in
/-- The existing upper-stage comparison is the cochain extension of the
complete-to-finite comparison. -/
theorem horizontalCompleteFiltrationCochainUpperIso_hom_eq_finite
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    (horizontalCompleteFiltrationCochainUpperIso K p).hom =
      HomologicalComplex.extendMap
        (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
          (by omega)).hom ComplexShape.embeddingDownNat := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp [horizontalCompleteFiltrationCochainUpperIso,
    horizontalCompleteFiltrationCochainMonoUpperIso,
    horizontalCompleteFilteredTotalMonoOverUpperIso,
    horizontalCompleteFilteredTotalComplexFiniteIso]
  exact HomologicalComplex.extendMap_id_f
    ((horizontalCompleteFilteredTotalMonoOver K
      (horizontalFirstPageUpperIndex p)).obj.left)
    ComplexShape.embeddingDownNat i

/-- The complete-stage projection is the finite-stage projection transported
through the complete-to-finite comparison. -/
theorem horizontalCompleteDirectColumnProjectionMap_eq_finite
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    horizontalCompleteDirectColumnProjectionMap K p =
      HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat ≫
        horizontalNaturalDirectColumnProjectionMap K p := by
  rw [← horizontalCompleteFiltrationCochainUpperIso_hom_eq_finite]
  cases p with
  | zero =>
      apply HomologicalComplex.Hom.ext
      funext i
      change horizontalDirectColumnProjection K 0 i =
        (horizontalCompleteFiltrationCochainUpperIso K 0).hom.f i ≫
          horizontalNaturalDirectColumnProjection K 0 i
      by_cases hi : (0 : ℤ) < i
      · rw [horizontalDirectColumnProjection_eq_zero_of_lt K 0 i hi,
          horizontalNaturalDirectColumnProjection_eq_zero_of_lt K 0 i hi,
          comp_zero]
      · have hile : i ≤ (0 : ℤ) := by lia
        obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = -(0 : ℤ) - q :=
          ⟨horizontalColumnDegree 0 i,
            horizontalColumnDegree_spec 0 i hile⟩
        have hile' : -(0 : ℤ) - q ≤ -((0 : ℕ) : ℤ) := by omega
        unfold horizontalDirectColumnProjection
        rw [dite_eq_left hile']
        unfold horizontalNaturalDirectColumnProjection
        rw [dite_eq_left hile']
        simp [horizontalColumnDegree,
          horizontalDirectColumnProjectionComponent,
          horizontalNaturalDirectColumnProjectionComponent,
          Category.assoc]
  | succ p =>
      simp [horizontalCompleteDirectColumnProjectionMap,
        horizontalCompleteSuccDirectColumnProjectionMap,
        horizontalMonoStageDirectColumnProjectionMap,
        horizontalNaturalStageCochainIso,
        horizontalCompleteFiltrationCochainUpperIso,
        horizontalCompleteFiltrationCochainMonoUpperIso,
        horizontalCompleteFiltrationCochainMonoUpperSuccIso,
        horizontalCompleteFilteredTotalMonoOverUpperIso,
        horizontalCompleteFilteredTotalMonoOverUpperSuccIso]

/-- The complete upper-stage projection is natural under bicomplex maps. -/
@[reassoc]
theorem horizontalCompleteDirectColumnProjectionMap_naturality
    (f : K ⟶ L) (p : ℕ) :
    HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
            (horizontalFirstPageUpperIndex p))
          ComplexShape.embeddingDownNat ≫
        horizontalCompleteDirectColumnProjectionMap L p =
      horizontalCompleteDirectColumnProjectionMap K p ≫
        horizontalDirectColumnCochainMap f p := by
  rw [horizontalCompleteDirectColumnProjectionMap_eq_finite,
    horizontalCompleteDirectColumnProjectionMap_eq_finite]
  have hFinite :=
    horizontalCompleteFilteredTotalComplexFiniteIso_naturality f
      (p : ℤ) (by omega)
  have hFiniteExt := congrArg
    (fun k ↦ HomologicalComplex.extendMap k
      ComplexShape.embeddingDownNat) hFinite
  simp only [HomologicalComplex.extendMap_comp] at hFiniteExt
  have hFiniteExt' :
      HomologicalComplex.extendMap
            (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
              (by omega)).hom ComplexShape.embeddingDownNat ≫
          HomologicalComplex.extendMap
            (horizontalFilteredTotalComplexMapOfBicomplex f p)
            ComplexShape.embeddingDownNat =
        HomologicalComplex.extendMap
            (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
              ((p : ℤ) : EInt)) ComplexShape.embeddingDownNat ≫
          HomologicalComplex.extendMap
            (horizontalCompleteFilteredTotalComplexFiniteIso L (p : ℤ)
              (by omega)).hom ComplexShape.embeddingDownNat := by
    simpa using hFiniteExt
  unfold horizontalFirstPageUpperIndex
  calc
    _ = (HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
            ((p : ℤ) : EInt)) ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso L (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat) ≫
        horizontalNaturalDirectColumnProjectionMap L p :=
      (Category.assoc _ _ _).symm
    _ = (HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat ≫
        HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat) ≫
        horizontalNaturalDirectColumnProjectionMap L p := by
      rw [hFiniteExt']
    _ = HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat ≫
        (HomologicalComplex.extendMap
          (horizontalFilteredTotalComplexMapOfBicomplex f p)
          ComplexShape.embeddingDownNat ≫
        horizontalNaturalDirectColumnProjectionMap L p) :=
      Category.assoc _ _ _
    _ = HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat ≫
        (horizontalNaturalDirectColumnProjectionMap K p ≫
          horizontalDirectColumnCochainMap f p) := by
      rw [horizontalNaturalDirectColumnProjectionMap_naturality]
    _ = (HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalComplexFiniteIso K (p : ℤ)
            (by omega)).hom ComplexShape.embeddingDownNat ≫
        horizontalNaturalDirectColumnProjectionMap K p) ≫
        horizontalDirectColumnCochainMap f p :=
      (Category.assoc _ _ _).symm

end Projection

section Coherent

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The map on the lower endpoint of a coherent first-page window induced by
a bicomplex map. -/
noncomputable abbrev horizontalFirstPageCoherentLowerCochainMapOfBicomplex
    (f : K ⟶ L) (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageCoherentLowerIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram L).obj
        (horizontalFirstPageCoherentLowerIndex p) :=
  HomologicalComplex.extendMap
    (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
      (horizontalFirstPageCoherentLowerIndex p))
    ComplexShape.embeddingDownNat

/-- The map on the upper endpoint of a coherent first-page window induced by
a bicomplex map. -/
noncomputable abbrev horizontalFirstPageCoherentUpperCochainMapOfBicomplex
    (f : K ⟶ L) (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram L).obj
        (horizontalFirstPageUpperIndex p) :=
  HomologicalComplex.extendMap
    (horizontalCompleteFilteredTotalComplexMapOfBicomplex f
      (horizontalFirstPageUpperIndex p))
    ComplexShape.embeddingDownNat

/-- Bicomplex maps commute with the filtration map spanning a coherent
first-page window. -/
theorem horizontalFirstPageCoherentMap_naturality_of_bicomplex
    (f : K ⟶ L) (p : ℕ) :
    horizontalFirstPageCoherentMap K p ≫
        horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p =
      horizontalFirstPageCoherentLowerCochainMapOfBicomplex f p ≫
        horizontalFirstPageCoherentMap L p := by
  have h :=
    horizontalCompleteFilteredTotalComplexMapOfBicomplex_naturality f
      (horizontalFirstPageCoherentIndex_le p)
  have hExt := congrArg
    (fun k ↦ HomologicalComplex.extendMap k
      ComplexShape.embeddingDownNat) h.symm
  simp only [HomologicalComplex.extendMap_comp] at hExt
  change
    HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalMap K
            (horizontalFirstPageCoherentIndex_le p))
          ComplexShape.embeddingDownNat ≫
        horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p =
      horizontalFirstPageCoherentLowerCochainMapOfBicomplex f p ≫
        HomologicalComplex.extendMap
          (horizontalCompleteFilteredTotalMap L
            (horizontalFirstPageCoherentIndex_le p))
          ComplexShape.embeddingDownNat
  exact hExt

/-- Map between the cokernels of coherent first-page windows induced by a
bicomplex map. -/
noncomputable def horizontalFirstPageCoherentCokernelMapOfBicomplex
    (f : K ⟶ L) (p : ℕ) :
    cokernel (horizontalFirstPageCoherentMap K p) ⟶
      cokernel (horizontalFirstPageCoherentMap L p) :=
  cokernel.map
    (horizontalFirstPageCoherentMap K p)
    (horizontalFirstPageCoherentMap L p)
    (horizontalFirstPageCoherentLowerCochainMapOfBicomplex f p)
    (horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p)
    (horizontalFirstPageCoherentMap_naturality_of_bicomplex f p)

/-- The coherent cokernel map has the expected formula on the cokernel
projection. -/
@[reassoc]
theorem horizontalFirstPageCoherentCokernelMapOfBicomplex_π
    (f : K ⟶ L) (p : ℕ) :
    cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        horizontalFirstPageCoherentCokernelMapOfBicomplex f p =
      horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p ≫
        cokernel.π (horizontalFirstPageCoherentMap L p) := by
  exact cokernel.π_desc _ _ _

/-- The coherent cokernel isomorphism sends the abstract cokernel projection
to the complete-stage direct-column projection. -/
@[reassoc]
theorem horizontalFirstPageCoherentCokernelIso_π_hom
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        (horizontalFirstPageCoherentCokernelIso K p).hom =
      horizontalCompleteDirectColumnProjectionMap K p := by
  cases p with
  | zero =>
      change cokernel.π (horizontalFirstPageFiltrationMap K 0) ≫
          (horizontalFirstPageCokernelIso K 0).hom =
        horizontalCompleteDirectColumnProjectionMap K 0
      unfold horizontalFirstPageCokernelIso
        horizontalFirstPageCokernelToDirectColumn
      rw [cokernel.π_desc]
  | succ p =>
      change cokernel.π (horizontalFirstPageNextFiltrationMap K p) ≫
          (horizontalFirstPageAdjacentRightIso K p).hom =
        horizontalCompleteDirectColumnProjectionMap K (p + 1)
      dsimp [horizontalFirstPageAdjacentRightIso,
        horizontalFirstPageNextCokernelIso,
        horizontalFirstPageCokernelIso]
      rw [cokernel.mapIso_hom]
      rw [cokernel.π_desc_assoc]
      simp only [Iso.refl_hom, Category.id_comp]
      unfold horizontalFirstPageCokernelToDirectColumn
      rw [cokernel.π_desc]

/-- The coherent cokernel identification with the direct column is natural
under bicomplex maps. -/
@[reassoc]
theorem horizontalFirstPageCoherentCokernelIso_hom_naturality_of_bicomplex
    (f : K ⟶ L) (p : ℕ) :
    horizontalFirstPageCoherentCokernelMapOfBicomplex f p ≫
        (horizontalFirstPageCoherentCokernelIso L p).hom =
      (horizontalFirstPageCoherentCokernelIso K p).hom ≫
        horizontalDirectColumnCochainMap f p := by
  apply (cancel_epi
    (cokernel.π (horizontalFirstPageCoherentMap K p))).1
  calc
    cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        (horizontalFirstPageCoherentCokernelMapOfBicomplex f p ≫
          (horizontalFirstPageCoherentCokernelIso L p).hom) =
      (cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        horizontalFirstPageCoherentCokernelMapOfBicomplex f p) ≫
          (horizontalFirstPageCoherentCokernelIso L p).hom :=
      (Category.assoc _ _ _).symm
    _ = (horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p ≫
          cokernel.π (horizontalFirstPageCoherentMap L p)) ≫
        (horizontalFirstPageCoherentCokernelIso L p).hom := by
      rw [horizontalFirstPageCoherentCokernelMapOfBicomplex_π]
    _ = horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p ≫
        (cokernel.π (horizontalFirstPageCoherentMap L p) ≫
          (horizontalFirstPageCoherentCokernelIso L p).hom) :=
      Category.assoc _ _ _
    _ = horizontalFirstPageCoherentUpperCochainMapOfBicomplex f p ≫
        horizontalCompleteDirectColumnProjectionMap L p := by
      rw [horizontalFirstPageCoherentCokernelIso_π_hom]
    _ = horizontalCompleteDirectColumnProjectionMap K p ≫
        horizontalDirectColumnCochainMap f p :=
      horizontalCompleteDirectColumnProjectionMap_naturality f p
    _ = (cokernel.π (horizontalFirstPageCoherentMap K p) ≫
          (horizontalFirstPageCoherentCokernelIso K p).hom) ≫
        horizontalDirectColumnCochainMap f p := by
      rw [horizontalFirstPageCoherentCokernelIso_π_hom]
    _ = cokernel.π (horizontalFirstPageCoherentMap K p) ≫
        ((horizontalFirstPageCoherentCokernelIso K p).hom ≫
          horizontalDirectColumnCochainMap f p) :=
      Category.assoc _ _ _

end Coherent

end HomologicalComplex₂

end
