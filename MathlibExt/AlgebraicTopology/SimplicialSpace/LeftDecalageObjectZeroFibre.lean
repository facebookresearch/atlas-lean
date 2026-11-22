/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyMappingFibre
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# The zero-row fibre of the original fixed-object path projection

The original zero-row projection is the target map on edges whose
source is fixed to the same original object. Pulling it back at the
prescribed target gives exactly the existing original mapping fibre.
Both total-edge and point maps remain the original pullback legs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The original zero-row fixed-source path object, displayed as its literal scalar pullback. -/
abbrev sourceEdges (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) : SSet.{u} :=
  pullback (W.diagram.δ (1 : Fin 2)) (SSet.yonedaEquiv.symm x)

/-- The original target projection retains the full original edge of the fixed-source pullback. -/
def sourceEdgesTarget (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    sourceEdges W x ⟶ W.diagram _⦋0⦌ :=
  pullback.fst _ _ ≫ W.diagram.δ (0 : Fin 2)

/-- The actual original source-edge pullback restricts further to the same prescribed target. -/
def mappingToSourceTargetFibre (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ⟶ pullback (sourceEdgesTarget W x) (SSet.yonedaEquiv.symm y) :=
  pullback.lift
    (pullback.lift (mappingFibre.fst W x y) (mappingFibre.snd W x y)
      (mappingFibre.source_eq W x y))
    (mappingFibre.snd W x y) (by
      rw [sourceEdgesTarget, ← Category.assoc, pullback.lift_fst, mappingFibre.target_eq])

set_option backward.isDefEq.respectTransparency false in
/-- The inverse keeps the whole original edge and the same fixed-source point. -/
def sourceTargetFibreToMapping (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    pullback (sourceEdgesTarget W x) (SSet.yonedaEquiv.symm y) ⟶ mappingFibre W x y :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _) (by
    apply prod.hom_ext
    · simp only [Category.assoc, mappingEndpoint_fst, mappingPointPair_fst]
      rw [pullback.condition]
      have hp : pullback.fst (sourceEdgesTarget W x) (SSet.yonedaEquiv.symm y) ≫
          pullback.snd (W.diagram.δ (1 : Fin 2)) (SSet.yonedaEquiv.symm x) =
        pullback.snd (sourceEdgesTarget W x) (SSet.yonedaEquiv.symm y) :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      rw [← Category.assoc, hp]
    · simp only [Category.assoc, mappingEndpoint_snd, mappingPointPair_snd]
      exact pullback.condition)

set_option backward.isDefEq.respectTransparency false in
/-- The entire original mapping fibre is the actual iterated source-and-target row-zero pullback. -/
def mappingSourceTargetIso (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre W x y ≅ pullback (sourceEdgesTarget W x) (SSet.yonedaEquiv.symm y) where
  hom := mappingToSourceTargetFibre W x y
  inv := sourceTargetFibreToMapping W x y
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [mappingToSourceTargetFibre, sourceTargetFibreToMapping, Category.assoc,
        pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [mappingToSourceTargetFibre, sourceTargetFibreToMapping, Category.assoc,
          pullback.lift_fst, Category.id_comp]
      · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

end SimplicialSpace.LeftDecalageObject
