/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageBoundaryComparison
public import MathlibExt.Algebra.Homology.MappingConeCokernelConnecting

/-!
# The first-page differential of the horizontal-filtration spectral sequence

The first page is compared coherently with the homology of the direct columns.
The filtration connecting morphism defining the spectral-sequence differential
is identified with the adjacent-column connecting morphism, including the edge
from column one to column zero.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ComposableArrows
open CategoryTheory.Pretriangulated

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The upper filtration index for column `p` is the first-page lower index
for column `p+1`. -/
theorem horizontalFirstPageUpperIndex_eq_i₁_succ (p q : ℕ) :
    horizontalFirstPageUpperIndex p =
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₁
        (p + 1, q) := by
  change horizontalFirstPageUpperIndex p = horizontalFirstPageLowerIndex (p + 1)
  exact horizontalFirstPageUpperIndex_eq_lowerIndex_succ p

/-- The upper filtration index is the first-page upper endpoint. -/
theorem horizontalFirstPageUpperIndex_eq_i₂ (p q : ℕ) :
    horizontalFirstPageUpperIndex p =
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₂
        (p, q) := by
  rfl

/-- The total-complex degree used at bidegree `(p,q)` is the degree selected
by the first-quadrant first-page data. -/
theorem horizontalFirstPageDegree_eq (p q : ℕ) :
    -(p : ℤ) - q =
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.deg
        (p, q) := by
  rfl

/-- Coherent lower endpoints for consecutive first-page filtration windows.
The positive-column lower endpoint is literally the previous upper endpoint. -/
abbrev horizontalFirstPageCoherentLowerIndex : ℕ → EInt
  | 0 => horizontalFirstPageLowerIndex 0
  | p + 1 => horizontalFirstPageUpperIndex p

/-- The coherent lower endpoint is the lower endpoint chosen by the
first-page spectral-sequence data. -/
theorem horizontalFirstPageCoherentLowerIndex_eq_i₁ (p q : ℕ) :
    horizontalFirstPageCoherentLowerIndex p =
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₁
        (p, q) := by
  cases p with
  | zero => rfl
  | succ p => exact horizontalFirstPageUpperIndex_eq_i₁_succ p q

/-- Each coherent lower endpoint lies below its corresponding upper endpoint. -/
theorem horizontalFirstPageCoherentIndex_le :
    (p : ℕ) → horizontalFirstPageCoherentLowerIndex p ≤
      horizontalFirstPageUpperIndex p
  | 0 => horizontalFirstPageIndex_le 0
  | p + 1 => horizontalFirstPageUpperIndex_le_succ p

/-- The filtration map spanning the coherent window for column `p`. -/
noncomputable abbrev horizontalFirstPageCoherentMap (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageCoherentLowerIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) :=
  (horizontalCompleteFiltrationCochainDiagram K).map
    (homOfLE (horizontalFirstPageCoherentIndex_le p))

/-- At column zero, the coherent filtration map is the original first-page
filtration map. -/
theorem horizontalFirstPageCoherentMap_zero :
    horizontalFirstPageCoherentMap K 0 =
      horizontalFirstPageFiltrationMap K 0 := by
  rfl

/-- At a positive column, the coherent filtration map is the canonical map
between the preceding and current upper stages. -/
theorem horizontalFirstPageCoherentMap_succ (p : ℕ) :
    horizontalFirstPageCoherentMap K (p + 1) =
      horizontalFirstPageNextFiltrationMap K p := by
  rfl

/-- The canonical map from the upper stage for column `p` to that for
column `p+1`. -/
noncomputable def horizontalFirstPageCoherentSuccessorMap (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1)) :=
  (horizontalCompleteFiltrationCochainDiagram K).map
    (homOfLE (horizontalFirstPageUpperIndex_le_succ p))

/-- The coherent successor map is the coherent filtration map for the next
column. -/
theorem horizontalFirstPageCoherentSuccessorMap_eq_map_succ (p : ℕ) :
    horizontalFirstPageCoherentSuccessorMap K p =
      horizontalFirstPageCoherentMap K (p + 1) := by
  rfl

/-- The coherent successor map agrees with the previously constructed
next-stage filtration map. -/
theorem horizontalFirstPageCoherentSuccessorMap_eq_next (p : ℕ) :
    horizontalFirstPageCoherentSuccessorMap K p =
      horizontalFirstPageNextFiltrationMap K p :=
  (horizontalFirstPageCoherentSuccessorMap_eq_map_succ K p).trans
    (horizontalFirstPageCoherentMap_succ K p)

/-- Relative homology of the coherent filtration window for `(p,q)`. -/
noncomputable abbrev horizontalFirstPageCoherentRelativeHomology (p q : ℕ) : C :=
  ((horizontalCompleteFiltrationSpectralObject K).H (-(p : ℤ) - q)).obj
    (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le p)))

/-- The spectral-sequence first-page object identified with the relative
homology of its coherent filtration window. -/
noncomputable def horizontalFirstPageCoherentXIso (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      horizontalFirstPageCoherentRelativeHomology K p q :=
  (horizontalCompleteFiltrationSpectralObject K).spectralSequenceFirstPageXIso
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
    (p, q) (horizontalFirstPageCoherentLowerIndex p)
    (horizontalFirstPageUpperIndex p)
    (horizontalFirstPageCoherentLowerIndex_eq_i₁ p q)
    (horizontalFirstPageUpperIndex_eq_i₂ p q)
    (-(p : ℤ) - q) (horizontalFirstPageDegree_eq p q)

/-- The cokernel of the coherent filtration map is the corresponding direct
column complex. -/
noncomputable def horizontalFirstPageCoherentCokernelIso :
    (p : ℕ) →
      cokernel (horizontalFirstPageCoherentMap K p) ≅
        horizontalDirectColumnCochain K p
  | 0 => by
      rw [horizontalFirstPageCoherentMap_zero]
      exact horizontalFirstPageCokernelIso K 0
  | p + 1 => by
      rw [horizontalFirstPageCoherentMap_succ]
      exact horizontalFirstPageAdjacentRightIso K p

/-- The mapping cone of a coherent filtration map maps to the corresponding
direct column through its cokernel sequence. -/
noncomputable def horizontalFirstPageCoherentMappingConeToDirectColumn
    (p : ℕ) :
    CochainComplex.mappingCone (horizontalFirstPageCoherentMap K p) ⟶
      horizontalDirectColumnCochain K p :=
  CochainComplex.mappingCone.descShortComplex
      (ShortComplex.cokernelSequence (horizontalFirstPageCoherentMap K p)) ≫
    (horizontalFirstPageCoherentCokernelIso K p).hom

/-- The mapping-cone-to-column comparison is a quasi-isomorphism. -/
theorem horizontalFirstPageCoherentMappingConeToDirectColumn_quasiIso
    (p : ℕ) :
    QuasiIso (horizontalFirstPageCoherentMappingConeToDirectColumn K p) := by
  have hm : Mono (horizontalFirstPageCoherentMap K p) := by
    cases p <;> unfold horizontalFirstPageCoherentMap <;> infer_instance
  let _ := hm
  let _ : Mono (ShortComplex.cokernelSequence
      (horizontalFirstPageCoherentMap K p)).f := by
    dsimp [ShortComplex.cokernelSequence]
    exact hm
  have hS : (ShortComplex.cokernelSequence
      (horizontalFirstPageCoherentMap K p)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _ }
  have hd : QuasiIso (CochainComplex.mappingCone.descShortComplex
      (ShortComplex.cokernelSequence
        (horizontalFirstPageCoherentMap K p))) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS
  let _ := hd
  dsimp [horizontalFirstPageCoherentMappingConeToDirectColumn]
  infer_instance

/-- Coherent relative homology is canonically the homology of the direct
column complex. -/
noncomputable def horizontalFirstPageCoherentRelativeHomologyDirectColumnIso
    (p q : ℕ) :
    horizontalFirstPageCoherentRelativeHomology K p q ≅
      (horizontalDirectColumnCochain K p).homology (-(p : ℤ) - q) := by
  cases p with
  | zero =>
      let n : ℤ := -((0 : ℕ) : ℤ) - q
      let M := CochainComplex.mappingCone (horizontalFirstPageCoherentMap K 0)
      let g := horizontalFirstPageCoherentMappingConeToDirectColumn K 0
      let hg : QuasiIso g :=
        horizontalFirstPageCoherentMappingConeToDirectColumn_quasiIso K 0
      let _ := hg
      change ((HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) n).obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)) ≅
        (horizontalDirectColumnCochain K 0).homology n
      exact (HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) n).app M ≪≫
        isoOfQuasiIsoAt g n
  | succ p =>
      let n : ℤ := -((p + 1 : ℕ) : ℤ) - q
      let M := CochainComplex.mappingCone
        (horizontalFirstPageCoherentMap K (p + 1))
      let g := horizontalFirstPageCoherentMappingConeToDirectColumn K (p + 1)
      let hg : QuasiIso g :=
        horizontalFirstPageCoherentMappingConeToDirectColumn_quasiIso K (p + 1)
      let _ := hg
      change ((HomotopyCategory.homologyFunctor C
          (ComplexShape.up ℤ) n).obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)) ≅
        (horizontalDirectColumnCochain K (p + 1)).homology n
      exact (HomotopyCategory.homologyFunctorFactors C
          (ComplexShape.up ℤ) n).app M ≪≫
        isoOfQuasiIsoAt g n

/-- The forward relative-homology comparison is induced by the canonical
mapping-cone-to-column map. -/
theorem horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom
    (p q : ℕ) :
    (horizontalFirstPageCoherentRelativeHomologyDirectColumnIso K p q).hom =
      (HomotopyCategory.homologyFunctorFactors C
        (ComplexShape.up ℤ) (-(p : ℤ) - q)).hom.app
          (CochainComplex.mappingCone (horizontalFirstPageCoherentMap K p)) ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageCoherentMappingConeToDirectColumn K p)
          (-(p : ℤ) - q) := by
  cases p <;>
    simp [horizontalFirstPageCoherentRelativeHomologyDirectColumnIso]

/-- Coherent identification of a first-page object with direct-column
homology. -/
noncomputable def horizontalFirstPageCoherentDirectColumnIso (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      (horizontalDirectColumnCochain K p).homology (-(p : ℤ) - q) :=
  horizontalFirstPageCoherentXIso K p q ≪≫
    horizontalFirstPageCoherentRelativeHomologyDirectColumnIso K p q

/-- The cokernel-composition sequence for a coherent filtration window,
identified with the adjacent direct-column short exact sequence. -/
noncomputable def horizontalFirstPageCoherentAdjacentShortComplexIso :
    (p : ℕ) →
      CategoryTheory.cokernelCompShortComplex
          (horizontalFirstPageCoherentMap K p)
          (horizontalFirstPageCoherentSuccessorMap K p) ≅
        horizontalFirstPageAdjacentDirectShortComplex K p
  | 0 => by
      exact horizontalFirstPageAdjacentShortComplexIso K 0
  | p + 1 => by
      exact CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq
          (horizontalFirstPageFiltrationMap K (p + 1))
          (horizontalFirstPageNextFiltrationMap K (p + 1))
          (horizontalFirstPageMiddleStageIso K p)
          (horizontalFirstPageNextFiltrationMap K p)
          (horizontalFirstPageNextFiltrationMap_eq_middle K p) ≪≫
        horizontalFirstPageAdjacentShortComplexIso K (p + 1)

/-- The right endpoint of one adjacent-column comparison agrees, through the
canonical cokernel identification, with the next comparison's left endpoint. -/
theorem horizontalFirstPageAdjacentShortComplexIso_endpoint (p : ℕ) :
    (horizontalFirstPageAdjacentShortComplexIso K p).hom.τ₃ =
      (horizontalFirstPageNextCokernelIso K p).hom ≫
        (horizontalFirstPageAdjacentShortComplexIso K (p + 1)).hom.τ₁ := by
  simp [horizontalFirstPageAdjacentShortComplexIso,
    horizontalFirstPageAdjacentLeftIso,
    horizontalFirstPageAdjacentRightIso]

set_option maxHeartbeats 500000 in
-- Normalizing both branches of the recursively defined comparison is expensive.
/-- Consecutive coherent adjacent-column comparisons use literally the same
map at their common endpoint. -/
theorem horizontalFirstPageCoherentAdjacentShortComplexIso_endpoint_coherence
    (p : ℕ) :
    (horizontalFirstPageCoherentAdjacentShortComplexIso K p).hom.τ₃ =
      (horizontalFirstPageCoherentAdjacentShortComplexIso K (p + 1)).hom.τ₁ := by
  cases p with
  | zero =>
      change (horizontalFirstPageAdjacentShortComplexIso K 0).hom.τ₃ =
        ((CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq
            (horizontalFirstPageFiltrationMap K 1)
            (horizontalFirstPageNextFiltrationMap K 1)
            (horizontalFirstPageMiddleStageIso K 0)
            (horizontalFirstPageNextFiltrationMap K 0)
            (horizontalFirstPageNextFiltrationMap_eq_middle K 0) ≪≫
          horizontalFirstPageAdjacentShortComplexIso K 1).hom.τ₁)
      rw [CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq_trans_hom_τ₁]
      exact horizontalFirstPageAdjacentShortComplexIso_endpoint K 0
  | succ p =>
      change ((CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq
            (horizontalFirstPageFiltrationMap K (p + 1))
            (horizontalFirstPageNextFiltrationMap K (p + 1))
            (horizontalFirstPageMiddleStageIso K p)
            (horizontalFirstPageNextFiltrationMap K p)
            (horizontalFirstPageNextFiltrationMap_eq_middle K p) ≪≫
          horizontalFirstPageAdjacentShortComplexIso K (p + 1)).hom.τ₃) =
        ((CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq
            (horizontalFirstPageFiltrationMap K (p + 2))
            (horizontalFirstPageNextFiltrationMap K (p + 2))
            (horizontalFirstPageMiddleStageIso K (p + 1))
            (horizontalFirstPageNextFiltrationMap K (p + 1))
            (horizontalFirstPageNextFiltrationMap_eq_middle K (p + 1)) ≪≫
          horizontalFirstPageAdjacentShortComplexIso K (p + 2)).hom.τ₁)
      rw [CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq_trans_hom_τ₃,
        CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq_trans_hom_τ₁]
      exact horizontalFirstPageAdjacentShortComplexIso_endpoint K (p + 1)

set_option maxHeartbeats 500000 in
-- Normalizing the positive-column branch of the recursive comparison is expensive.
/-- The left endpoint of the coherent adjacent-column comparison is the
chosen coherent cokernel comparison. -/
theorem horizontalFirstPageCoherentAdjacentShortComplexIso_hom_τ₁
    (p : ℕ) :
    (horizontalFirstPageCoherentAdjacentShortComplexIso K p).hom.τ₁ =
      (horizontalFirstPageCoherentCokernelIso K p).hom := by
  cases p with
  | zero => rfl
  | succ p =>
      change ((CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq
            (horizontalFirstPageFiltrationMap K (p + 1))
            (horizontalFirstPageNextFiltrationMap K (p + 1))
            (horizontalFirstPageMiddleStageIso K p)
            (horizontalFirstPageNextFiltrationMap K p)
            (horizontalFirstPageNextFiltrationMap_eq_middle K p) ≪≫
          horizontalFirstPageAdjacentShortComplexIso K (p + 1)).hom.τ₁) =
        (horizontalFirstPageAdjacentRightIso K p).hom
      rw [CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq_trans_hom_τ₁]
      rfl

/-- The right endpoint of the coherent adjacent-column comparison is the
chosen coherent cokernel comparison for the next column. -/
theorem horizontalFirstPageCoherentAdjacentShortComplexIso_hom_τ₃
    (p : ℕ) :
    (horizontalFirstPageCoherentAdjacentShortComplexIso K p).hom.τ₃ =
      (horizontalFirstPageCoherentCokernelIso K (p + 1)).hom := by
  rw [horizontalFirstPageCoherentAdjacentShortComplexIso_endpoint_coherence,
    horizontalFirstPageCoherentAdjacentShortComplexIso_hom_τ₁]

/-- Inverse form of the coherent right-endpoint comparison. -/
theorem horizontalFirstPageCoherentAdjacentShortComplexIso_inv_τ₃
    (p : ℕ) :
    (horizontalFirstPageCoherentAdjacentShortComplexIso K p).inv.τ₃ =
      (horizontalFirstPageCoherentCokernelIso K (p + 1)).inv := by
  apply (Iso.inv_eq_inv
    (ShortComplex.π₃.mapIso
      (horizontalFirstPageCoherentAdjacentShortComplexIso K p))
    (horizontalFirstPageCoherentCokernelIso K (p + 1))).2
  exact horizontalFirstPageCoherentAdjacentShortComplexIso_hom_τ₃ K p

/-- Connecting map obtained directly from the coherent filtration window,
transported to direct-column homology. -/
noncomputable def horizontalFirstPageCoherentConnectingMap (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).homology
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalDirectColumnCochain K p).homology (-(p : ℤ) - q) := by
  have hm : Mono (horizontalFirstPageCoherentSuccessorMap K p) := by
    unfold horizontalFirstPageCoherentSuccessorMap
    infer_instance
  let _ := hm
  let e := horizontalFirstPageCoherentAdjacentShortComplexIso K p
  exact HomologicalComplex.homologyMap e.inv.τ₃
      (-((p + 1 : ℕ) : ℤ) - q) ≫
    (CategoryTheory.cokernelCompShortComplex_shortExact
      (horizontalFirstPageCoherentMap K p)
      (horizontalFirstPageCoherentSuccessorMap K p)).δ
        (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q)
          (by simp only [ComplexShape.up_Rel]; push_cast; omega) ≫
    HomologicalComplex.homologyMap e.hom.τ₁ (-(p : ℤ) - q)

/-- The coherent filtration connecting map is the previously constructed
adjacent-column connecting map. -/
theorem horizontalFirstPageCoherentConnectingMap_eq_adjacent (p q : ℕ) :
    horizontalFirstPageCoherentConnectingMap K p q =
      horizontalFirstPageAdjacentConnectingMap K p q := by
  have hm : Mono (horizontalFirstPageCoherentSuccessorMap K p) := by
    unfold horizontalFirstPageCoherentSuccessorMap
    infer_instance
  let _ := hm
  let S := CategoryTheory.cokernelCompShortComplex
    (horizontalFirstPageCoherentMap K p)
    (horizontalFirstPageCoherentSuccessorMap K p)
  let hS := CategoryTheory.cokernelCompShortComplex_shortExact
    (horizontalFirstPageCoherentMap K p)
    (horizontalFirstPageCoherentSuccessorMap K p)
  let e := horizontalFirstPageCoherentAdjacentShortComplexIso K p
  let hT := horizontalFirstPageAdjacentDirectShortExact K p
  have hnat := HomologicalComplex.HomologySequence.δ_naturality
    e.hom hS hT
    (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q)
    (by simp only [ComplexShape.up_Rel]; push_cast; omega)
  dsimp [horizontalFirstPageCoherentMap,
    horizontalFirstPageCoherentSuccessorMap] at hnat
  dsimp [horizontalFirstPageCoherentConnectingMap,
    horizontalFirstPageAdjacentConnectingMap]
  rw [hnat]
  have he : e.inv.τ₃ ≫ e.hom.τ₃ = 𝟙 _ := by
    change (e.inv ≫ e.hom).τ₃ = _
    rw [e.inv_hom_id]
    rfl
  rw [← HomologicalComplex.homologyMap_comp_assoc, he,
    HomologicalComplex.homologyMap_id, Category.id_comp]

set_option maxRecDepth 3000 in
/-- Under the coherent direct-column identifications, the actual differential
on the spectral sequence's first page is the coherent connecting map. -/
theorem horizontalFirstPage_d_coherentDirectColumn (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).d
        (p + 1, q) (p, q) ≫
      (horizontalFirstPageCoherentDirectColumnIso K p q).hom =
    (horizontalFirstPageCoherentDirectColumnIso K (p + 1) q).hom ≫
      horizontalFirstPageCoherentConnectingMap K p q := by
  let X := horizontalCompleteFiltrationSpectralObject K
  let data :=
    CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological
  have hrel : (ComplexShape.spectralSequenceNat ⟨-(1 : ℤ), (1 : ℤ) - 1⟩).Rel
      (p + 1, q) (p, q) := by
    simp only [ComplexShape.spectralSequenceNat_rel_iff]
    constructor <;> omega
  have hj : horizontalFirstPageUpperIndex p =
      data.i₁ (p + 1, q) :=
    horizontalFirstPageUpperIndex_eq_i₁_succ p q
  have hpage := X.spectralSequence_first_page_d_eq data
    (p + 1, q) (p, q) hrel
    (horizontalFirstPageCoherentLowerIndex p)
    (horizontalFirstPageUpperIndex p)
    (horizontalFirstPageUpperIndex (p + 1))
    (horizontalFirstPageCoherentLowerIndex_eq_i₁ p q) hj
    (horizontalFirstPageUpperIndex_eq_i₂ (p + 1) q)
    (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q)
    (horizontalFirstPageDegree_eq (p + 1) q) (by omega)
  have htarget
      (hi₁ : horizontalFirstPageCoherentLowerIndex p = data.i₁ (p, q))
      (hi₂ : horizontalFirstPageUpperIndex p = data.i₂ (p, q))
      (hn : -(p : ℤ) - q = data.deg (p, q)) :
      X.spectralSequenceFirstPageXIso data (p, q)
          (horizontalFirstPageCoherentLowerIndex p)
          (horizontalFirstPageUpperIndex p) hi₁ hi₂
          (-(p : ℤ) - q) hn =
        horizontalFirstPageCoherentXIso K p q := by
    dsimp [X, data]
    unfold horizontalFirstPageCoherentXIso
    congr 1
  have hsource
      (hi₁ : horizontalFirstPageUpperIndex p = data.i₁ (p + 1, q))
      (hi₂ : horizontalFirstPageUpperIndex (p + 1) = data.i₂ (p + 1, q))
      (hn : -((p + 1 : ℕ) : ℤ) - q = data.deg (p + 1, q)) :
      X.spectralSequenceFirstPageXIso data (p + 1, q)
          (horizontalFirstPageUpperIndex p)
          (horizontalFirstPageUpperIndex (p + 1)) hi₁ hi₂
          (-((p + 1 : ℕ) : ℤ) - q) hn =
        horizontalFirstPageCoherentXIso K (p + 1) q := by
    dsimp [X, data]
    unfold horizontalFirstPageCoherentXIso
    congr 1
  unfold horizontalFirstQuadrantSpectralSequence
  rw [hpage, htarget, hsource]
  dsimp [horizontalFirstPageCoherentDirectColumnIso]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply (cancel_epi
    (horizontalFirstPageCoherentXIso K (p + 1) q).hom).2
  rw [horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom
      (K := K) p q,
    horizontalFirstPageCoherentRelativeHomologyDirectColumnIso_hom
      (K := K) (p + 1) q]
  have hm : Mono (horizontalFirstPageCoherentSuccessorMap K p) := by
    unfold horizontalFirstPageCoherentSuccessorMap
    infer_instance
  let _ := hm
  have hδ := CochainComplex.mappingCone.homologySequenceδ_cokernelComp
    (horizontalFirstPageCoherentMap K p)
    (horizontalFirstPageCoherentSuccessorMap K p)
    (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q)
    (by push_cast; omega)
  rw [horizontalCompleteFiltrationSpectralObject_δ K]
  dsimp [horizontalFirstPageCoherentMappingConeToDirectColumn,
    horizontalFirstPageCoherentConnectingMap]
  simp only [Category.assoc, HomologicalComplex.homologyMap_comp]
  dsimp [horizontalFirstPageCoherentMap,
    horizontalFirstPageCoherentSuccessorMap] at hδ
  rw [reassoc_of% hδ]
  dsimp [horizontalFirstPageCoherentMap]
  have hcancel :
      HomologicalComplex.homologyMap
          (horizontalFirstPageCoherentCokernelIso K (p + 1)).hom
          (-((p + 1 : ℕ) : ℤ) - q) ≫
        HomologicalComplex.homologyMap
          (horizontalFirstPageCoherentCokernelIso K (p + 1)).inv
          (-((p + 1 : ℕ) : ℤ) - q) = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp,
      (horizontalFirstPageCoherentCokernelIso K (p + 1)).hom_inv_id,
      HomologicalComplex.homologyMap_id]
  dsimp [horizontalFirstPageCoherentMap,
    horizontalFirstPageCoherentSuccessorMap] at hcancel
  rw [horizontalFirstPageCoherentAdjacentShortComplexIso_inv_τ₃,
    horizontalFirstPageCoherentAdjacentShortComplexIso_hom_τ₁]
  rw [reassoc_of% hcancel]

/-- Under the coherent direct-column identifications, the first-page
differential is the adjacent-column connecting map. -/
theorem horizontalFirstPage_d_coherentDirectColumn_eq_adjacent (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).d
        (p + 1, q) (p, q) ≫
      (horizontalFirstPageCoherentDirectColumnIso K p q).hom =
    (horizontalFirstPageCoherentDirectColumnIso K (p + 1) q).hom ≫
      horizontalFirstPageAdjacentConnectingMap K p q := by
  rw [horizontalFirstPage_d_coherentDirectColumn K p q,
    horizontalFirstPageCoherentConnectingMap_eq_adjacent K p q]

/-- Coherent identification of a first-page object with ordinary vertical
homology in its column. -/
noncomputable def horizontalFirstPageCoherentVerticalHomologyIso (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      (K.X p).homology q :=
  horizontalFirstPageCoherentDirectColumnIso K p q ≪≫
    horizontalDirectColumnHomologyIso K p q

/-- After transport to ordinary vertical homology, the actual first-page
differential is the adjacent-column connecting map. -/
theorem horizontalFirstPage_d_coherentVerticalHomology_eq_adjacent
    (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).d
        (p + 1, q) (p, q) ≫
      (horizontalFirstPageCoherentVerticalHomologyIso K p q).hom =
      (horizontalFirstPageCoherentVerticalHomologyIso K (p + 1) q).hom ≫
      horizontalFirstPageAdjacentVerticalConnectingMap K p q := by
  dsimp [horizontalFirstPageCoherentVerticalHomologyIso]
  rw [← Category.assoc,
    horizontalFirstPage_d_coherentDirectColumn_eq_adjacent K p q]
  dsimp [horizontalFirstPageAdjacentVerticalConnectingMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- After the coherent vertical-homology transport, the actual first-page
differential is `(-1)^(q+1)` times the horizontal homology map. -/
theorem horizontalFirstPage_d_coherentVerticalHomology_eq_horizontal
    (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).d
        (p + 1, q) (p, q) ≫
      (horizontalFirstPageCoherentVerticalHomologyIso K p q).hom =
    (horizontalFirstPageCoherentVerticalHomologyIso K (p + 1) q).hom ≫
      (((q + 1 : ℕ) : ℤ).negOnePow •
        horizontalFirstPageHorizontalHomologyMap K p q) := by
  rw [horizontalFirstPage_d_coherentVerticalHomology_eq_adjacent K p q,
    horizontalFirstPageAdjacentVerticalConnectingMap_eq_horizontal K p q]

end HomologicalComplex₂
