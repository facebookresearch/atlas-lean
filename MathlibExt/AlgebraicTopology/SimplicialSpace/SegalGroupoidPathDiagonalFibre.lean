/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalGroupoidPathDiagonal
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectZeroComparison
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpPullbackClosure
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpWeakCospanComparison

/-!
# The original Segal groupoid mapping fibre and its path diagonal fibre

The original mapping fibre is the point fibre of the actual zero-row
path projection. The proved ordinary Rezk comparison is weak between
sharp maps over the same whole zero row. Restriction at the same original
target therefore gives the actual weak mapping-to-diagonal-fibre map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.LeftDecalageObject

open SimplicialSpace.SegalHomotopy

/-- The original zero-row inverse keeps the whole original target map. -/
theorem zeroRowIso_inv_target (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    (zeroRowIso W x).inv ≫ (projection W x).app (op (SimplexCategory.mk 0)) = sourceEdgesTarget W x := by
  apply (cancel_epi (zeroRowIso W x).hom).mp
  simp only [Iso.hom_inv_id_assoc, zeroRowIso_target]

/-- The entire original mapping fibre is the actual zero-row path point pullback. -/
def zeroMappingFibreIso (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ≅ pullback ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y) := by
  let p := sourceEdgesTarget W x
  let q := (projection W x).app (op (SimplexCategory.mk 0))
  let b := SSet.yonedaEquiv.symm y
  have hs : p ≫ 𝟙 _ = (zeroRowIso W x).inv ≫ q := by
    simpa only [Category.comp_id] using (zeroRowIso_inv_target W x).symm
  let c := pullback.map p b q b (zeroRowIso W x).inv (𝟙 _) (𝟙 _) hs (by simp)
  let _ : IsIso c := pullback.map_isIso p b q b (zeroRowIso W x).inv
    (𝟙 _) (𝟙 _) hs (by simp)
  exact mappingSourceTargetIso W x y ≪≫ asIso c

/-- The original target vertex enters the diagonal through the literal original zero row. -/
def diagonalPoint (W : SimplicialSpace.{u}) (y : (W.diagram _⦋0⦌) _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ SSet.simplicialDiagonalFunctor.obj W.diagram :=
  SSet.yonedaEquiv.symm y ≫
    SSet.EquifibredDiagonal.rowVertexToDiagonal W.diagram (SimplexCategory.mk 0) 0

/-- The diagonal target map is precisely the original vertex's whole Yoneda point. -/
theorem diagonalPoint_eq_yoneda (W : SimplicialSpace.{u}) (y : (W.diagram _⦋0⦌) _⦋0⦌) :
    diagonalPoint W y = SSet.yonedaEquiv.symm
      (show (SSet.simplicialDiagonalFunctor.obj W.diagram) _⦋0⦌ from y) := by
  apply SSet.yonedaEquiv.injective
  simp only [diagonalPoint, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
    SSet.EquifibredDiagonal.rowVertexToDiagonal_app]
  have hc : SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 0) 0 = 𝟙 _ := by
    ext i
    fin_cases i
    rfl
  rw [hc, op_id, W.diagram.map_id]
  calc
    _ = (show (SSet.simplicialDiagonalFunctor.obj W.diagram) _⦋0⦌ from y) := rfl
    _ = _ := (Equiv.apply_symm_apply
      (SSet.yonedaEquiv (X := SSet.simplicialDiagonalFunctor.obj W.diagram))
      (show (SSet.simplicialDiagonalFunctor.obj W.diagram) _⦋0⦌ from y)).symm

/-- The whole original zero-row point map restricts the original ordinary Rezk comparison. -/
def zeroPointMap (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    pullback ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y) ⟶
      pullback (pullback.snd (diagonalProjection W x)
        (SSet.EquifibredDiagonal.rowVertexToDiagonal W.diagram (SimplexCategory.mk 0) 0))
        (SSet.yonedaEquiv.symm y) :=
  pullback.map ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y)
      (pullback.snd (diagonalProjection W x)
        (SSet.EquifibredDiagonal.rowVertexToDiagonal W.diagram (SimplexCategory.mk 0) 0))
      (SSet.yonedaEquiv.symm y)
      (SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison (projection W x)
        (SimplexCategory.mk 0) 0) (𝟙 _) (𝟙 _)
      (by
        simpa only [Category.comp_id] using
          (SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison_legs
            (projection W x) (SimplexCategory.mk 0) 0).2.symm)
      (by simp)

/-- The whole zero-row point fibre maps to the actual diagonal point fibre by the original Rezk lift. -/
def zeroPointToDiagonalFibre (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    pullback ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y) ⟶
      pullback (diagonalProjection W x) (diagonalPoint W y) :=
  zeroPointMap W x y ≫
    (SSet.SharpPullbackClosure.nestedPullbackIso (diagonalProjection W x)
      (SSet.EquifibredDiagonal.rowVertexToDiagonal W.diagram (SimplexCategory.mk 0) 0)
      (SSet.yonedaEquiv.symm y)).hom

/-- The actual mapping-to-diagonal-fibre map keeps the original zero-row isomorphism and Rezk lift. -/
def mappingToDiagonalFibre (W : SimplicialSpace.{u}) (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⟶ pullback (diagonalProjection W x) (diagonalPoint W y) :=
  (zeroMappingFibreIso W x y).hom ≫ zeroPointToDiagonalFibre W x y

/-- Genuine equivalence of every original edge makes the same restricted whole Rezk comparison weak. -/
theorem zeroPointMap_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hG : ∀ a : (W.diagram _⦋1⦌) _⦋0⦌, IsEquivalenceEdge W hW a)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (zeroPointMap W x y) := by
  let a := SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison (projection W x)
    (SimplexCategory.mk 0) 0
  let theta := SSet.EquifibredDiagonal.rowVertexToDiagonal W.diagram (SimplexCategory.mk 0) 0
  let q := pullback.snd (diagonalProjection W x) theta
  have ha : WeakEquivalence a := by
    apply (HomotopicalAlgebra.weakEquivalence_iff _).mpr
    apply SSet.EquifibredDiagonal.realizationWeak_vertexDiagonalPullbackComparison (projection W x)
    intro n m f
    exact relativeOperatorComparison_weak W hW hG x f
  have hp := projection_sharp W x hW.1 0
  have hq := SSet.SharpPullbackClosure.sharp_pullback_snd (diagonalProjection W x) theta
    (diagonal_sharp_and_row_comparisons W hW hG x).1
  have hs : (projection W x).app (op (SimplexCategory.mk 0)) ≫ 𝟙 _ = a ≫ q := by
    simpa only [Category.comp_id] using
      (SSet.EquifibredDiagonal.vertexDiagonalPullbackComparison_legs
        (projection W x) (SimplexCategory.mk 0) 0).2.symm
  have hm := SSet.SharpComparisonDraft.pullbackMap_weak
    ((projection W x).app (op (SimplexCategory.mk 0))) (SSet.yonedaEquiv.symm y) q (SSet.yonedaEquiv.symm y)
    a (𝟙 _) (𝟙 _) hs (by simp) ha (by infer_instance) (by infer_instance) hp hq
  have hc : WeakEquivalence (zeroPointMap W x y) := by
    simpa only [zeroPointMap, a, q, theta] using hm
  exact (HomotopicalAlgebra.weakEquivalence_iff (C := SSet.{u}) _).mp hc

/-- The actual original zero-row point-fibre comparison is weak for a Segal groupoid. -/
theorem zeroPointToDiagonalFibre_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hG : ∀ a : (W.diagram _⦋1⦌) _⦋0⦌, IsEquivalenceEdge W hW a)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (zeroPointToDiagonalFibre W x y) :=
  SSet.realizationWeakEquivalences.comp_mem _ _ (zeroPointMap_weak W hW hG x y)
    (SSet.realizationWeakEquivalences.of_isIso
      (SSet.SharpPullbackClosure.nestedPullbackIso (diagonalProjection W x)
        (SSet.EquifibredDiagonal.rowVertexToDiagonal W.diagram (SimplexCategory.mk 0) 0)
        (SSet.yonedaEquiv.symm y)).hom)

/-- The original mapping fibre maps weakly to the original diagonal path fibre. -/
theorem mappingToDiagonalFibre_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hG : ∀ a : (W.diagram _⦋1⦌) _⦋0⦌, IsEquivalenceEdge W hW a)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.realizationWeakEquivalences (mappingToDiagonalFibre W x y) :=
  SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso (zeroMappingFibreIso W x y).hom)
    (zeroPointToDiagonalFibre_weak W hW hG x y)

end SimplicialSpace.LeftDecalageObject
