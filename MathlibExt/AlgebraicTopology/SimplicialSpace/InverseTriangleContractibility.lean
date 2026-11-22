/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InverseTriangleNonempty
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingOperatorEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead

/-!
# Contractibility of the original strict inverse-triangle spaces

The same original candidate projections and composition sections prove
weakness of the original middle maps. Their accepted Reedy fibrations and
original identity pullbacks give trivial fibrations of both inverse spaces.
Public Kan Whitehead supplies whole simplicial contractions.

Source: Rezk (2001), Section 5.5 and Corollary 11.5.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.InverseTriangle

open SegalHomotopy

/-- The actual terminal zero-simplex is Kan using its public terminal isomorphism. -/
private lemma deltaZero_kanComplex : SSet.KanComplex (Δ[0] : SSet.{u}) := by
  change IsFibrant (Δ[0] : SSet.{u})
  rw [isFibrant_iff]
  let e : (Δ[0] : SSet.{u}) ≅ ⊤_ SSet.{u} :=
    IsTerminal.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀ terminalIsTerminal
  have h : terminal.from (Δ[0] : SSet.{u}) = e.hom := terminalIsTerminal.hom_ext _ _
  rw [h]
  exact (SSet.modelCategoryQuillen.fibration_iff e.hom).mpr
    (MorphismProperty.rlp_of_isIso SSet.modelCategoryQuillen.J e.hom)

variable (W : SimplicialSpace.{u}) (hW : segalSpaces W)
  (x y : (W.diagram _⦋0⦌) _⦋0⦌) (f : (mappingFibre W x y) _⦋0⦌)
  (hIso : IsIso (C := Object W hW) (X := ⟨x⟩) (Y := ⟨y⟩) (SSet.π₀.mk f))

include hW hIso

/-- The original right middle map is a trivial fibration at an invertible original hom class. -/
private lemma rightMiddle_trivialFibration :
    trivialFibrations SSet.{u} (rightMiddle W x y f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let q := FixedEdgeTriangle.rightProjection W x y f
  let s := FixedEdgeTriangle.rightSection W hW x y f
  have hq : SSet.realizationWeakEquivalences q :=
    (FixedEdgeTriangle.rightProjection_trivialFibration W hW x y f).2
  have hs : SSet.realizationWeakEquivalences s :=
    SSet.realizationWeakEquivalences.of_postcomp s q hq (by
      rw [(FixedEdgeTriangle.rightSectionLaws W hW x y f).1]
      exact SSet.realizationWeakEquivalences.id_mem _)
  have hg : IsEquivalenceEdge W hW ((mappingFibre.fst W x y).app (op ⦋0⦌) f) :=
    (isEquivalenceEdge_iff_of_fibre W hW _ f rfl).mpr hIso
  have hsm : s ≫ rightMiddle W x y f = mappingPrecomposition W hW x y x f := by
    simpa only [s, rightMiddle, Category.assoc] using
      (FixedEdgeTriangle.rightSectionLaws W hW x y f).2.2
  have hm : SSet.realizationWeakEquivalences (rightMiddle W x y f) :=
    SSet.realizationWeakEquivalences.of_precomp s (rightMiddle W x y f) hs (by
      rw [hsm]
      exact mappingPrecomposition_realizationWeakEquivalence W hW x y f hg x)
  let _ : Fibration (rightMiddle W x y f) := rightMiddle_fibration W x y f hW.1
  let _ : WeakEquivalence (rightMiddle W x y f) := (weakEquivalence_iff _).mpr hm
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

/-- The original left middle map uses the fixed-last postcomposition operator. -/
private lemma leftMiddle_trivialFibration :
    trivialFibrations SSet.{u} (leftMiddle W x y f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let q := FixedEdgeTriangle.leftProjection W x y f
  let s := FixedEdgeTriangle.leftSection W hW x y f
  have hq : SSet.realizationWeakEquivalences q :=
    (FixedEdgeTriangle.leftProjection_trivialFibration W hW x y f).2
  have hs : SSet.realizationWeakEquivalences s :=
    SSet.realizationWeakEquivalences.of_postcomp s q hq (by
      rw [(FixedEdgeTriangle.leftSectionLaws W hW x y f).1]
      exact SSet.realizationWeakEquivalences.id_mem _)
  have hg : IsEquivalenceEdge W hW ((mappingFibre.fst W x y).app (op ⦋0⦌) f) :=
    (isEquivalenceEdge_iff_of_fibre W hW _ f rfl).mpr hIso
  have hsm : s ≫ leftMiddle W x y f = mappingPostcomposition W hW y x y f := by
    simpa only [s, leftMiddle, Category.assoc] using
      (FixedEdgeTriangle.leftSectionLaws W hW x y f).2.2
  have hm : SSet.realizationWeakEquivalences (leftMiddle W x y f) :=
    SSet.realizationWeakEquivalences.of_precomp s (leftMiddle W x y f) hs (by
      rw [hsm]
      exact mappingPostcomposition_realizationWeakEquivalence W hW x y f hg y)
  let _ : Fibration (leftMiddle W x y f) := leftMiddle_fibration W x y f hW.1
  let _ : WeakEquivalence (leftMiddle W x y f) := (weakEquivalence_iff _).mpr hm
  exact (mem_trivialFibrations_iff _).mpr ⟨inferInstance, inferInstance⟩

/-- The same original right inverse-space point projection is a scalar trivial fibration. -/
theorem rightToPoint_trivialFibration :
    trivialFibrations SSet.{u} (rightToPoint W x y f) :=
  (trivialFibrations SSet.{u}).of_isPullback (right_isPullback W x y f)
    (rightMiddle_trivialFibration W hW x y f hIso)

/-- The same original left inverse-space point projection is a scalar trivial fibration. -/
theorem leftToPoint_trivialFibration :
    trivialFibrations SSet.{u} (leftToPoint W x y f) :=
  (trivialFibrations SSet.{u}).of_isPullback (left_isPullback W x y f)
    (leftMiddle_trivialFibration W hW x y f hIso)

/-- Full Kan weakness of the original right point projection retains every pointed homotopy map. -/
theorem rightToPoint_W : SSet.KanComplex.W (rightToPoint W x y f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : SSet.KanComplex (rightSpace W x y f) := rightSpace_kanComplex W x y f hW.1
  let _ : SSet.KanComplex (Δ[0] : SSet.{u}) := deltaZero_kanComplex
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr
    (rightToPoint_trivialFibration W hW x y f hIso).2

/-- Full Kan weakness of the original left point projection keeps the same strict fibre. -/
theorem leftToPoint_W : SSet.KanComplex.W (leftToPoint W x y f) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : SSet.KanComplex (leftSpace W x y f) := leftSpace_kanComplex W x y f hW.1
  let _ : SSet.KanComplex (Δ[0] : SSet.{u}) := deltaZero_kanComplex
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mpr
    (leftToPoint_trivialFibration W hW x y f hIso).2

/-- The whole original right inverse space contracts, without a natural choice of its point. -/
theorem rightSpace_contractible :
    ∃ s : (Δ[0] : SSet.{u}) ⟶ rightSpace W x y f,
      s ≫ rightToPoint W x y f = 𝟙 (Δ[0] : SSet.{u}) ∧
        Nonempty (SSet.Homotopy (rightToPoint W x y f ≫ s) (𝟙 (rightSpace W x y f))) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : SSet.KanComplex (rightSpace W x y f) := rightSpace_kanComplex W x y f hW.1
  let _ : SSet.KanComplex (Δ[0] : SSet.{u}) := deltaZero_kanComplex
  obtain ⟨s, H, _⟩ := SSet.KanComplex.W.exists_homotopy_inverse
    (rightToPoint_W W hW x y f hIso)
  exact ⟨s, SSet.stdSimplex.isTerminalObj₀.hom_ext _ _, H⟩

/-- The whole original left inverse space has the same literal contraction orientation. -/
theorem leftSpace_contractible :
    ∃ s : (Δ[0] : SSet.{u}) ⟶ leftSpace W x y f,
      s ≫ leftToPoint W x y f = 𝟙 (Δ[0] : SSet.{u}) ∧
        Nonempty (SSet.Homotopy (leftToPoint W x y f ≫ s) (𝟙 (leftSpace W x y f))) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : SSet.KanComplex (leftSpace W x y f) := leftSpace_kanComplex W x y f hW.1
  let _ : SSet.KanComplex (Δ[0] : SSet.{u}) := deltaZero_kanComplex
  obtain ⟨s, H, _⟩ := SSet.KanComplex.W.exists_homotopy_inverse
    (leftToPoint_W W hW x y f hIso)
  exact ⟨s, SSet.stdSimplex.isTerminalObj₀.hom_ext _ _, H⟩

end SimplicialSpace.InverseTriangle
