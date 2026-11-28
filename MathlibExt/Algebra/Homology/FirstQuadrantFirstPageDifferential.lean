/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageBoundaryComparison
public import MathlibExt.Algebra.Homology.MappingConeCokernelConnecting

/-!
# The differential of the horizontal-filtration first page

Let `K` be a first-quadrant bicomplex in an abelian category. Choose coherent filtration
windows for column `p`: its upper endpoint is the column's upper stage, and the lower endpoint
in a positive column is the preceding upper endpoint. The relative homology is taken in
cochain degree `-p-q`.

These windows identify the first-page object at `(p,q)` with direct-column and vertical
homology. The differential from `(p+1,q)` to `(p,q)` is the adjacent-column connecting map.
Under the coherent vertical-homology isomorphisms, it is `(-1)^(q+1)` times `H_q(K.d(p+1,p))`.
The formulas include `p=0`, hence the edge from column one to column zero.
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

/-- The common endpoint of consecutive first-page filtration windows.

The upper endpoint for column `p` is the lower endpoint selected for column `p+1` by the
first-page indexing data. -/
theorem horizontalFirstPageUpperIndex_eq_i₁_succ (p q : ℕ) :
    horizontalFirstPageUpperIndex p =
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₁
        (p + 1, q) := by
  change horizontalFirstPageUpperIndex p = horizontalFirstPageLowerIndex (p + 1)
  exact horizontalFirstPageUpperIndex_eq_lowerIndex_succ p

/-- The upper endpoint of a first-page filtration window.

The chosen upper index for column `p` equals the first-page upper endpoint at `(p,q)`. -/
theorem horizontalFirstPageUpperIndex_eq_i₂ (p q : ℕ) :
    horizontalFirstPageUpperIndex p =
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₂
        (p, q) := by
  rfl

/-- The cochain degree of a first-page bidegree.

The first-page indexing data selects degree `-p-q` at bidegree `(p,q)`. -/
theorem horizontalFirstPageDegree_eq (p q : ℕ) :
    -(p : ℤ) - q =
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.deg
        (p, q) := by
  rfl

/-- The coherent lower endpoints of first-page filtration windows.

At column zero use its chosen lower index; at column `p+1` use the upper index of column `p`. -/
abbrev horizontalFirstPageCoherentLowerIndex : ℕ → EInt
  | 0 => horizontalFirstPageLowerIndex 0
  | p + 1 => horizontalFirstPageUpperIndex p

/-- The first-page lower endpoint in coherent coordinates.

The coherent lower index equals the lower endpoint selected by the first-page indexing data. -/
theorem horizontalFirstPageCoherentLowerIndex_eq_i₁ (p q : ℕ) :
    horizontalFirstPageCoherentLowerIndex p =
      CategoryTheory.Abelian.SpectralObject.coreE₁FirstQuadrantHomological.i₁
        (p, q) := by
  cases p with
  | zero => rfl
  | succ p => exact horizontalFirstPageUpperIndex_eq_i₁_succ p q

/-- The order relation of coherent first-page window endpoints.

For every column, the coherent lower endpoint lies below its upper endpoint. -/
theorem horizontalFirstPageCoherentIndex_le :
    (p : ℕ) → horizontalFirstPageCoherentLowerIndex p ≤
      horizontalFirstPageUpperIndex p
  | 0 => horizontalFirstPageIndex_le 0
  | p + 1 => horizontalFirstPageUpperIndex_le_succ p

/-- The filtration map of a coherent first-page window.

Use the complete filtration diagram map from the coherent lower stage of column `p` to its
upper stage. -/
noncomputable abbrev horizontalFirstPageCoherentMap (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageCoherentLowerIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) :=
  (horizontalCompleteFiltrationCochainDiagram K).map
    (homOfLE (horizontalFirstPageCoherentIndex_le p))

/-- The coherent filtration map in column zero.

The zero-column coherent map is its first-page filtration map. -/
theorem horizontalFirstPageCoherentMap_zero :
    horizontalFirstPageCoherentMap K 0 =
      horizontalFirstPageFiltrationMap K 0 := by
  rfl

/-- The coherent filtration map in a positive column.

At column `p+1`, the coherent map is the next-stage filtration map from the preceding upper
stage. -/
theorem horizontalFirstPageCoherentMap_succ (p : ℕ) :
    horizontalFirstPageCoherentMap K (p + 1) =
      horizontalFirstPageNextFiltrationMap K p := by
  rfl

/-- The map between successive first-page upper stages.

The complete filtration diagram maps the upper stage of column `p` to that of column `p+1`. -/
noncomputable def horizontalFirstPageCoherentSuccessorMap (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1)) :=
  (horizontalCompleteFiltrationCochainDiagram K).map
    (homOfLE (horizontalFirstPageUpperIndex_le_succ p))

/-- The successor upper-stage map as the next coherent window.

The upper-stage successor map is the coherent filtration map for column `p+1`. -/
theorem horizontalFirstPageCoherentSuccessorMap_eq_map_succ (p : ℕ) :
    horizontalFirstPageCoherentSuccessorMap K p =
      horizontalFirstPageCoherentMap K (p + 1) := by
  rfl

/-- The successor upper-stage map as the next filtration map.

The coherent upper-stage successor is the next-stage complete filtration map. -/
theorem horizontalFirstPageCoherentSuccessorMap_eq_next (p : ℕ) :
    horizontalFirstPageCoherentSuccessorMap K p =
      horizontalFirstPageNextFiltrationMap K p :=
  (horizontalFirstPageCoherentSuccessorMap_eq_map_succ K p).trans
    (horizontalFirstPageCoherentMap_succ K p)

/-- The relative homology of a coherent first-page window.

For `(p,q)`, take the spectral object's relative homology of the coherent lower-to-upper
filtration map in cochain degree `-p-q`. -/
noncomputable abbrev horizontalFirstPageCoherentRelativeHomology (p q : ℕ) : C :=
  ((horizontalCompleteFiltrationSpectralObject K).H (-(p : ℤ) - q)).obj
    (mk₁ (homOfLE (horizontalFirstPageCoherentIndex_le p)))

/-- The relative-homology coordinate of a first-page object.

The first-page object at `(p,q)` is isomorphic to relative homology of its coherent window at
degree `-p-q`. -/
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

/-- The direct-column cokernel of a coherent filtration window.

The cokernel of the coherent window map is isomorphic to the direct column complex, with the
separate zero-column comparison at `p=0`. -/
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

/-- The mapping-cone comparison of a coherent window with its direct column.

The mapping cone maps through the cokernel sequence and the coherent cokernel isomorphism to
the direct column. -/
noncomputable def horizontalFirstPageCoherentMappingConeToDirectColumn
    (p : ℕ) :
    CochainComplex.mappingCone (horizontalFirstPageCoherentMap K p) ⟶
      horizontalDirectColumnCochain K p :=
  CochainComplex.mappingCone.descShortComplex
      (ShortComplex.cokernelSequence (horizontalFirstPageCoherentMap K p)) ≫
    (horizontalFirstPageCoherentCokernelIso K p).hom

/-- The quasi-isomorphism from a coherent window cone to its direct column.

The coherent filtration map is monic, so its cone-to-cokernel map and direct-column comparison
give a quasi-isomorphism. -/
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

/-- The direct-column homology of a coherent filtration window.

Its relative homology at degree `-p-q` is canonically isomorphic to direct-column homology in
that degree. -/
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

/-- The homology map of the coherent window-to-column comparison.

The forward relative-homology isomorphism is the homotopy-category homology comparison
followed by homology of the cone-to-column map. -/
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

/-- The coherent direct-column coordinate of a first-page object.

Compose the relative-window comparison with the cone-to-column homology comparison. -/
noncomputable def horizontalFirstPageCoherentDirectColumnIso (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      (horizontalDirectColumnCochain K p).homology (-(p : ℤ) - q) :=
  horizontalFirstPageCoherentXIso K p q ≪≫
    horizontalFirstPageCoherentRelativeHomologyDirectColumnIso K p q

/-- Precomposition transport of a cokernel-composition sequence.

Given `f'=e.hom ≫ f` and an isomorphism from the cokernel-composition sequence of `f,g` to a
short complex `T`, the transported sequence of `f',g` has an isomorphism to `T` together with
its equality to the canonical composite. -/
noncomputable def cokernelPrecompShortComplexIsoData
    {X Y Z X' : CochainComplex C ℤ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (e : X' ≅ X) (f' : X' ⟶ Y) (h : f' = e.hom ≫ f)
    {T : ShortComplex (CochainComplex C ℤ)}
    (E : CategoryTheory.cokernelCompShortComplex f g ≅ T) :
    { I : CategoryTheory.cokernelCompShortComplex f' g ≅ T //
      I = CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq f g e f' h ≪≫ E } := by
  let P := CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq f g e f' h
  let full := P ≪≫ E
  have hP : P.hom.τ₃ = 𝟙 _ :=
    CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq_hom_τ₃ f g e f' h
  let I : CategoryTheory.cokernelCompShortComplex f' g ≅ T :=
    ShortComplex.isoMk
      ((ShortComplex.π₁.mapIso P) ≪≫ (ShortComplex.π₁.mapIso E))
      ((ShortComplex.π₂.mapIso P) ≪≫ (ShortComplex.π₂.mapIso E))
      (ShortComplex.π₃.mapIso E)
      (by exact full.hom.comm₁₂)
      (by
        have hComm := full.hom.comm₂₃
        change (P.hom.τ₂ ≫ E.hom.τ₂) ≫ T.g =
          (CategoryTheory.cokernelCompShortComplex f' g).g ≫
            (P.hom.τ₃ ≫ E.hom.τ₃) at hComm
        rw [hP, Category.id_comp] at hComm
        exact hComm)
  refine ⟨I, ?_⟩
  apply Iso.ext
  apply ShortComplex.Hom.ext
  · rfl
  · rfl
  · change E.hom.τ₃ = P.hom.τ₃ ≫ E.hom.τ₃
    rw [hP, Category.id_comp]

/-- The adjacent-column sequence of coherent filtration windows.

The cokernel-composition short complex of a window map and its successor is isomorphic to the
adjacent direct-column short exact sequence. -/
noncomputable def horizontalFirstPageCoherentAdjacentShortComplexIso :
    (p : ℕ) →
      CategoryTheory.cokernelCompShortComplex
          (horizontalFirstPageCoherentMap K p)
          (horizontalFirstPageCoherentSuccessorMap K p) ≅
        horizontalFirstPageAdjacentDirectShortComplex K p
  | 0 => by
      exact horizontalFirstPageAdjacentShortComplexIso K 0
  | p + 1 => by
      exact (cokernelPrecompShortComplexIsoData
          (horizontalFirstPageFiltrationMap K (p + 1))
          (horizontalFirstPageNextFiltrationMap K (p + 1))
          (horizontalFirstPageMiddleStageIso K p)
          (horizontalFirstPageNextFiltrationMap K p)
          (horizontalFirstPageNextFiltrationMap_eq_middle K p)
          (horizontalFirstPageAdjacentShortComplexIso K (p + 1))).1

/-- The shared endpoint of consecutive adjacent-column comparisons.

The right endpoint map of one comparison equals its cokernel identification followed by the
next comparison's left endpoint map. -/
theorem horizontalFirstPageAdjacentShortComplexIso_endpoint (p : ℕ) :
    (horizontalFirstPageAdjacentShortComplexIso K p).hom.τ₃ =
      (horizontalFirstPageNextCokernelIso K p).hom ≫
        (horizontalFirstPageAdjacentShortComplexIso K (p + 1)).hom.τ₁ := by
  simp [horizontalFirstPageAdjacentShortComplexIso,
    horizontalFirstPageAdjacentLeftIso,
    horizontalFirstPageAdjacentRightIso]

/-- The left endpoint map of a coherent adjacent-column comparison.

The left component is the coherent cokernel-to-direct-column comparison for column `p`. -/
theorem horizontalFirstPageCoherentAdjacentShortComplexIso_hom_τ₁
    (p : ℕ) :
    (horizontalFirstPageCoherentAdjacentShortComplexIso K p).hom.τ₁ =
      (horizontalFirstPageCoherentCokernelIso K p).hom := by
  cases p with
  | zero => rfl
  | succ p =>
      have hComponent :
          (horizontalFirstPageCoherentAdjacentShortComplexIso K (p + 1)).hom.τ₁ =
            (horizontalFirstPageNextCokernelIso K p).hom ≫
              (horizontalFirstPageAdjacentShortComplexIso K (p + 1)).hom.τ₁ :=
        CategoryTheory.cokernelCompShortComplexPrecompIsoOfEq_trans_hom_τ₁
          (horizontalFirstPageFiltrationMap K (p + 1))
          (horizontalFirstPageNextFiltrationMap K (p + 1))
          (horizontalFirstPageMiddleStageIso K p)
          (horizontalFirstPageNextFiltrationMap K p)
          (horizontalFirstPageNextFiltrationMap_eq_middle K p)
          (horizontalFirstPageAdjacentShortComplexIso K (p + 1))
      exact hComponent.trans (show
        (horizontalFirstPageNextCokernelIso K p).hom ≫
            (horizontalFirstPageAdjacentShortComplexIso K (p + 1)).hom.τ₁ =
          (horizontalFirstPageCoherentCokernelIso K (p + 1)).hom from rfl)

/-- Coherence of the shared endpoint in adjacent first-page windows.

The right endpoint of one coherent adjacent comparison is the same map as the left endpoint of
the next. -/
theorem horizontalFirstPageCoherentAdjacentShortComplexIso_endpoint_coherence
    (p : ℕ) :
    (horizontalFirstPageCoherentAdjacentShortComplexIso K p).hom.τ₃ =
      (horizontalFirstPageCoherentAdjacentShortComplexIso K (p + 1)).hom.τ₁ := by
  rw [horizontalFirstPageCoherentAdjacentShortComplexIso_hom_τ₁ K (p + 1)]
  cases p with
  | zero => rfl
  | succ p => rfl

/-- The right endpoint map of a coherent adjacent-column comparison.

The right component is the coherent cokernel-to-direct-column comparison for column `p+1`. -/
theorem horizontalFirstPageCoherentAdjacentShortComplexIso_hom_τ₃
    (p : ℕ) :
    (horizontalFirstPageCoherentAdjacentShortComplexIso K p).hom.τ₃ =
      (horizontalFirstPageCoherentCokernelIso K (p + 1)).hom := by
  rw [horizontalFirstPageCoherentAdjacentShortComplexIso_endpoint_coherence,
    horizontalFirstPageCoherentAdjacentShortComplexIso_hom_τ₁]

/-- The inverse right endpoint of a coherent adjacent-column comparison.

The inverse right component is the inverse coherent cokernel comparison for column `p+1`. -/
theorem horizontalFirstPageCoherentAdjacentShortComplexIso_inv_τ₃
    (p : ℕ) :
    (horizontalFirstPageCoherentAdjacentShortComplexIso K p).inv.τ₃ =
      (horizontalFirstPageCoherentCokernelIso K (p + 1)).inv := by
  apply (Iso.inv_eq_inv
    (ShortComplex.π₃.mapIso
      (horizontalFirstPageCoherentAdjacentShortComplexIso K p))
    (horizontalFirstPageCoherentCokernelIso K (p + 1))).2
  exact horizontalFirstPageCoherentAdjacentShortComplexIso_hom_τ₃ K p

/-- The coherent-window connecting map in direct-column coordinates.

Transport the cokernel-composition connecting morphism to direct-column homology from degree
`-(p+1)-q` to `-p-q`. -/
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

/-- Equality of coherent-window and adjacent-column connecting maps.

The transported connecting map of the coherent filtration window equals the adjacent direct-
column connecting morphism. -/
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

/-- The first-page differential in coherent direct-column coordinates.

The differential from `(p+1,q)` to `(p,q)` corresponds to the coherent-window connecting map
under the source and target direct-column isomorphisms. -/
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
  let n : ℤ := -((p + 1 : ℕ) : ℤ) - q
  let j : ℤ := -(p : ℤ) - q
  let f : horizontalFirstPageCoherentLowerIndex p ⟶ horizontalFirstPageUpperIndex p :=
    homOfLE (horizontalFirstPageCoherentIndex_le p)
  let g : horizontalFirstPageUpperIndex p ⟶ horizontalFirstPageUpperIndex (p + 1) :=
    homOfLE (horizontalFirstPageUpperIndex_le_succ p)
  let eS := horizontalFirstPageCoherentRelativeHomologyDirectColumnIso K (p + 1) q
  let eT := horizontalFirstPageCoherentRelativeHomologyDirectColumnIso K p q
  have hn : n + 1 = j := by dsimp [n, j]; push_cast; omega
  have hRelative : X.δ f g n j hn ≫ eT.hom =
      eS.hom ≫ horizontalFirstPageCoherentConnectingMap K p q := by
    dsimp only [X, f, g, n, j, eS, eT]
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
  unfold horizontalFirstQuadrantSpectralSequence
  rw [hpage, htarget, hsource]
  simp only [horizontalFirstPageCoherentDirectColumnIso, Iso.trans_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [X, f, g, n, j, eS, eT, Category.assoc] using
    congrArg (fun z => (horizontalFirstPageCoherentXIso K (p + 1) q).hom ≫ z) hRelative

/-- The adjacent-column formula for the first-page differential.

In coherent direct-column homology coordinates, the first-page differential is the adjacent-
column connecting morphism for every `p,q ≥ 0`. -/
theorem horizontalFirstPage_d_coherentDirectColumn_eq_adjacent (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).d
        (p + 1, q) (p, q) ≫
      (horizontalFirstPageCoherentDirectColumnIso K p q).hom =
    (horizontalFirstPageCoherentDirectColumnIso K (p + 1) q).hom ≫
      horizontalFirstPageAdjacentConnectingMap K p q := by
  rw [horizontalFirstPage_d_coherentDirectColumn K p q,
    horizontalFirstPageCoherentConnectingMap_eq_adjacent K p q]

/-- The coherent vertical-homology coordinate of a first-page object.

Compose the coherent direct-column isomorphism with the direct-column comparison to
`H_q(K_p)`. -/
noncomputable def horizontalFirstPageCoherentVerticalHomologyIso (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      (K.X p).homology q :=
  horizontalFirstPageCoherentDirectColumnIso K p q ≪≫
    horizontalDirectColumnHomologyIso K p q

/-- The adjacent connecting formula in vertical-homology coordinates.

The coherent vertical-homology comparison identifies the first-page differential with the
adjacent vertical connecting map. -/
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

/-- The sign of the first-page differential in coherent vertical coordinates.

For every `p,q ≥ 0`, the differential from `(p+1,q)` to `(p,q)` is `(-1)^(q+1)` times the
vertical-homology map of the horizontal bicomplex differential. -/
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
