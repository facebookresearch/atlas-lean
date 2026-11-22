/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentBooleanInterval
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCompositionFace
import MathlibExt.AlgebraicTopology.SimplicialCategory.HomotopyTwoCategory
import MathlibExt.AlgebraicTopology.Quasicategory.Core

/-!
# Original whole composition cell of an actual coherent-nerve triangle

The direct-to-through interval inclusion in the actual coherent
two-simplex maps to a complete original Hom edge from its direct edge
to the composite of its two short edges. All three original object
vertices and both parallel Hom boundaries are retained. Its two-cell
class is invertible when that original Hom is Kan.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.NativeTriangleCell
open SimplicialEnrichment

/-- The first supplied original object of the coherent two-simplex. -/
def p0 : coherentSimplex.{u} ⦋2⦌ := .mk (ULift.up 0)

/-- The middle supplied original object of that same simplex. -/
def p1 : coherentSimplex.{u} ⦋2⦌ := .mk (ULift.up 1)

/-- The last supplied original object of that same simplex. -/
def p2 : coherentSimplex.{u} ⦋2⦌ := .mk (ULift.up 2)

/-- The whole left short-edge vertex of the original through path. -/
def leftVertex : (p0.{u} ⟶[SSet.{u}] p1) _⦋0⦌ :=
  ComposableArrows.mk₀ (C := SimplicialThickening.Path (ULift.up.{u} (0 : Fin 3)) (ULift.up.{u} (1 : Fin
    3))) (CompositionFace.leftPath BooleanInterval.through
    (Set.mem_univ (ULift.up.{u} (1 : Fin 3))))

/-- The whole right short-edge vertex of the same original through path. -/
def rightVertex : (p1.{u} ⟶[SSet.{u}] p2) _⦋0⦌ :=
  ComposableArrows.mk₀ (C := SimplicialThickening.Path (ULift.up.{u} (1 : Fin 3)) (ULift.up.{u} (2 : Fin
    3))) (CompositionFace.rightPath BooleanInterval.through
    (Set.mem_univ (ULift.up.{u} (1 : Fin 3))))

/-- Original union composition of the two short edges is exactly the supplied whole through-path vertex. -/
theorem through_comp :
    (eComp SSet.{u} p0 p1 p2).app (op ⦋0⦌) (leftVertex, rightVertex) =
      BooleanInterval.throughVertex := by
  apply ComposableArrows.ext₀ (C := BooleanInterval.Path02.{u})
  exact CompositionFace.union_split BooleanInterval.through
    (Set.mem_univ (ULift.up.{u} (1 : Fin 3)))

/-- The actual original direct-to-through edge, with its complete two parallel boundaries. -/
def originalEdge : SSet.Edge BooleanInterval.directVertex.{u} BooleanInterval.throughVertex where
  edge := BooleanInterval.alphaCell
  src_eq := BooleanInterval.alphaCell_source
  tgt_eq := BooleanInterval.alphaCell_target

variable {C : Carrier.{u}} (σ : (coherentNerveFunctor.obj C) _⦋2⦌)

/-- The actual original first short edge represented by the supplied coherent triangle. -/
def left : (σ.obj p0 ⟶[SSet.{u}] σ.obj p1) _⦋0⦌ :=
  (σ.map p0 p1).app (op ⦋0⦌) leftVertex

/-- The actual original second short edge represented by that same triangle. -/
def right : (σ.obj p1 ⟶[SSet.{u}] σ.obj p2) _⦋0⦌ :=
  (σ.map p1 p2).app (op ⦋0⦌) rightVertex

/-- The actual original direct edge represented by the triangle at its two outer object vertices. -/
def direct : (σ.obj p0 ⟶[SSet.{u}] σ.obj p2) _⦋0⦌ :=
  (σ.map p0 p2).app (op ⦋0⦌) BooleanInterval.directVertex

/-- The supplied triangle's whole through edge is the actual composite of its original short edges. -/
theorem through_readback :
    (σ.map p0 p2).app (op ⦋0⦌) BooleanInterval.throughVertex =
      (eComp SSet.{u} (σ.obj p0) (σ.obj p1) (σ.obj p2)).app (op ⦋0⦌) (left σ, right σ) := by
  have h := congr($(σ.map_comp p0 p1 p2).app (op ⦋0⦌) (leftVertex, rightVertex))
  exact (congrArg (fun v => (σ.map p0 p2).app (op ⦋0⦌) v) through_comp).symm.trans h

/-- The actual complete Hom edge from the direct edge to the original composite, extracted from the same
  coherent triangle. -/
def compositionEdge : SSet.Edge (direct σ)
    ((eComp SSet.{u} (σ.obj p0) (σ.obj p1) (σ.obj p2)).app (op ⦋0⦌) (left σ, right σ)) where
  edge := (σ.map p0 p2).app (op ⦋1⦌) BooleanInterval.alphaCell
  src_eq := (originalEdge.map (σ.map p0 p2)).src_eq
  tgt_eq := (originalEdge.map (σ.map p0 p2)).tgt_eq.trans (through_readback σ)

/-- The actual original two-cell class represented by the same whole coherent triangle. -/
def compositionCell : SSet.HomotopyTwoCategory.oneCell (direct σ) ⟶
    SSet.HomotopyTwoCategory.oneCell
      ((eComp SSet.{u} (σ.obj p0) (σ.obj p1) (σ.obj p2)).app (op ⦋0⦌) (left σ, right σ)) :=
  SSet.HomotopyTwoCategory.twoCell (compositionEdge σ)

/-- Its whole original one-simplex is exactly the image of the original interval inclusion. -/
theorem compositionEdge_readback : (compositionEdge σ).edge =
    (σ.map p0 p2).app (op ⦋1⦌) BooleanInterval.alphaCell := rfl

/-- The actual composition two-cell of the supplied native coherent triangle is invertible under the
  original outer Hom Kan hypothesis. -/
theorem compositionCell_isIso [SSet.KanComplex (σ.obj p0 ⟶[SSet.{u}] σ.obj p2)] :
    IsIso (compositionCell σ) := SSet.Edge.isEquivalence_of_kanComplex (compositionEdge σ)

end CategoryTheory.CoherentRealization.NativeTriangleCell
