/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeOperators

/-!
# The original coefficient edge of the marked coherent one-simplex

The distinguished cone edge is the actual inclusion `{0} ⊆ {0,1}`.
Its source and target maxima differ, so it is not forced marked by the
cone weight. Zero-dimensional cone weights mark every edge, which
proves that original degeneracy maps supply marked coefficient edges.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight

attribute [local instance] vertexDecidableEq

/-- The original vertex zero in the coherent one-simplex. -/
def zeroOne : Vertex.{u} 1 := ULift.up (0 : Fin 2)

/-- The original singleton source of the coefficient edge. -/
def coefficientSource : ConeSubset (zeroOne.{u}) where
  vertices := {zeroOne}
  mem := Finset.mem_singleton_self _
  lower j _ := Fin.zero_le j.down

/-- The entire original two-vertex target of the coefficient edge. -/
def coefficientTarget : ConeSubset (zeroOne.{u}) where
  vertices := {zeroOne, ULift.up (1 : Fin 2)}
  mem := Finset.mem_insert_self _ _
  lower j _ := Fin.zero_le j.down

/-- The distinguished coefficient edge is the original inclusion of the singleton into the two-vertex subset. -/
def coefficientEdge : (nerve (ConeSubset (zeroOne.{u}))) _⦋1⦌ :=
  ComposableArrows.mk₁ (homOfLE (show coefficientSource ≤ coefficientTarget by
    change ({zeroOne} : Finset (Vertex.{u} 1)) ⊆ {zeroOne, ULift.up (1 : Fin 2)}
    exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)))

/-- The coefficient edge retains its original singleton source vertex. -/
theorem coefficientEdge_source : coefficientEdge.{u}.obj 0 = coefficientSource := rfl

/-- Its target is precisely the original entire two-vertex subset. -/
theorem coefficientEdge_target : coefficientEdge.{u}.obj 1 = coefficientTarget := rfl

/-- Every original edge of a zero-dimensional weight is marked by its necessarily constant maximum. -/
theorem coneWeight_zero_marked (i : Vertex.{u} 0) (e : (nerve (ConeSubset i)) _⦋1⦌) :
    e ∈ (coneWeight i).marking := by
  apply ULift.ext
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- Every actual degeneracy to the zero ordinal sends the original coefficient edge to a marked edge. -/
theorem coefficientEdge_image_zero (f : Vertex.{u} 1 →o Vertex.{u} 0) :
    (coneImage f zeroOne).hom.app (op ⦋1⦌) coefficientEdge ∈ (coneWeight (f zeroOne)).marking :=
  coneWeight_zero_marked _ _

end SSet.Marked.CoherentWeight
