/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeEdge
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCofaceSupport
import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalence

/-!
# The two original root-coefficient triangles for marked composition

The full original two-simplex cone contains the chains
`{0} ⊆ {0,1} ⊆ {0,1,2}` and `{0} ⊆ {0,2} ⊆ {0,1,2}`.
Their first edges are the original two nonzero coface images. The middle
edge of the first chain is the original zero-coface edge acted on by
the whole original path `{0,1}`. The final edge of the second chain is
already marked by its unchanged original maximum. Every subset, edge,
triangle and path is the actual original one.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The SAME original root of the two-simplex. -/
def rootTriangleZero : Vertex.{u} 2 := ULift.up (0 : Fin 3)

/-- Its SAME original middle vertex. -/
def rootTriangleOne : Vertex.{u} 2 := ULift.up (1 : Fin 3)

/-- The original singleton root subset. -/
def rootTriangleSingleton : ConeSubset (rootTriangleZero.{u}) where
  vertices := {rootTriangleZero}
  mem := Finset.mem_singleton_self _
  lower j _ := Fin.zero_le j.down

/-- The original adjacent root pair, retaining both original vertices. -/
def rootTriangleAdjacent : ConeSubset (rootTriangleZero.{u}) where
  vertices := {rootTriangleZero, rootTriangleOne}
  mem := Finset.mem_insert_self _ _
  lower j _ := Fin.zero_le j.down

/-- The original long root pair, retaining both original endpoints. -/
def rootTriangleLong : ConeSubset (rootTriangleZero.{u}) where
  vertices := {rootTriangleZero, ULift.up (2 : Fin 3)}
  mem := Finset.mem_insert_self _ _
  lower j _ := Fin.zero_le j.down

/-- The whole original three-vertex root subset. -/
def rootTriangleWhole : ConeSubset (rootTriangleZero.{u}) where
  vertices := {rootTriangleZero, rootTriangleOne, ULift.up (2 : Fin 3)}
  mem := Finset.mem_insert_self _ _
  lower j _ := Fin.zero_le j.down

/-- The SAME first adjacent inclusion. -/
def rootTriangleFirst : rootTriangleSingleton.{u} ⟶ rootTriangleAdjacent :=
  homOfLE (by
    change ({rootTriangleZero} : Finset (Vertex.{u} 2)) ⊆ {rootTriangleZero, rootTriangleOne}
    simp)

/-- The SAME second inclusion of the whole original first chain. -/
def rootTriangleMiddle : rootTriangleAdjacent.{u} ⟶ rootTriangleWhole :=
  homOfLE (by
    change ({rootTriangleZero, rootTriangleOne} : Finset (Vertex.{u} 2)) ⊆
      {rootTriangleZero, rootTriangleOne, ULift.up (2 : Fin 3)}
    simp)

/-- The SAME original long-pair inclusion from the root singleton. -/
def rootTriangleDirect : rootTriangleSingleton.{u} ⟶ rootTriangleLong :=
  homOfLE (by
    change ({rootTriangleZero} : Finset (Vertex.{u} 2)) ⊆ {rootTriangleZero, ULift.up (2 : Fin 3)}
    simp)

/-- The SAME final inclusion keeps the original maximum vertex two. -/
def rootTriangleConstant : rootTriangleLong.{u} ⟶ rootTriangleWhole :=
  homOfLE (by
    change ({rootTriangleZero, ULift.up (2 : Fin 3)} : Finset (Vertex.{u} 2)) ⊆
      {rootTriangleZero, rootTriangleOne, ULift.up (2 : Fin 3)}
    simp)

/-- The entire original root-to-three-vertex inclusion. -/
def rootTriangleFull : rootTriangleSingleton.{u} ⟶ rootTriangleWhole :=
  rootTriangleFirst ≫ rootTriangleMiddle

/-- Both SAME original chains compose to precisely the whole root-to-three-vertex inclusion. -/
theorem rootTriangle_second_comp : rootTriangleDirect.{u} ≫ rootTriangleConstant = rootTriangleFull :=
  Subsingleton.elim _ _

/-- The genuine original first inclusion triangle, with all three of its original edges. -/
def rootTriangleFirstComp : Edge.CompStruct (nerve.edgeMk rootTriangleFirst.{u})
    (nerve.edgeMk rootTriangleMiddle) (nerve.edgeMk rootTriangleFull) :=
  Edge.CompStruct.mk (ComposableArrows.mk₂ rootTriangleFirst rootTriangleMiddle)
    (nerve.δ₂_mk₂_eq _ _) (nerve.δ₀_mk₂_eq _ _) (nerve.δ₁_mk₂_eq _ _)

/-- The genuine original second inclusion triangle retains the SAME full long edge. -/
def rootTriangleSecondComp : Edge.CompStruct (nerve.edgeMk rootTriangleDirect.{u})
    (nerve.edgeMk rootTriangleConstant) (nerve.edgeMk rootTriangleFull) :=
  Edge.CompStruct.mk (ComposableArrows.mk₂ rootTriangleDirect rootTriangleConstant)
    (nerve.δ₂_mk₂_eq _ _) (nerve.δ₀_mk₂_eq _ _)
    ((nerve.δ₁_mk₂_eq _ _).trans (congrArg ComposableArrows.mk₁ rootTriangle_second_comp))

/-- The original coface omitting vertex two reads the SAME adjacent coefficient edge. -/
theorem rootTriangle_first_image :
    (coneImage (coneCofaceEmbedding.{u} (2 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌)
      coefficientEdge = (nerve.edgeMk rootTriangleFirst).edge := by
  refine CategoryTheory.Functor.ext (fun k => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  fin_cases k <;> apply ConeSubset.ext
  · change ({zeroOne} : Finset (Vertex.{u} 1)).image (coneCofaceEmbedding (2 : Fin 3)) =
      {rootTriangleZero}
    rw [Finset.image_singleton]
    rfl
  · change ({zeroOne, ULift.up (1 : Fin 2)} : Finset (Vertex.{u} 1)).image
      (coneCofaceEmbedding (2 : Fin 3)) = {rootTriangleZero, rootTriangleOne}
    rw [Finset.image_insert, Finset.image_singleton]
    rfl

/-- The original coface omitting vertex one reads the SAME long coefficient edge. -/
theorem rootTriangle_direct_image :
    (coneImage (coneCofaceEmbedding.{u} (1 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌)
      coefficientEdge = (nerve.edgeMk rootTriangleDirect).edge := by
  refine CategoryTheory.Functor.ext (fun k => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  fin_cases k <;> apply ConeSubset.ext
  · change ({zeroOne} : Finset (Vertex.{u} 1)).image (coneCofaceEmbedding (1 : Fin 3)) =
      {rootTriangleZero}
    rw [Finset.image_singleton]
    rfl
  · change ({zeroOne, ULift.up (1 : Fin 2)} : Finset (Vertex.{u} 1)).image
      (coneCofaceEmbedding (1 : Fin 3)) = {rootTriangleZero, ULift.up (2 : Fin 3)}
    rw [Finset.image_insert, Finset.image_singleton]
    rfl

/-- The entire original path from zero to one contains precisely its two original vertices. -/
def rootTrianglePath : SimplicialThickening.Path (rootTriangleZero.{u}) rootTriangleOne where
  I := {rootTriangleZero, rootTriangleOne}
  left := Set.mem_insert _ _
  right := Set.mem_insert_of_mem _ (Set.mem_singleton _)
  left_le j _ := Fin.zero_le j.down
  le_right j hj := by
    rcases hj with rfl | hj
    · decide
    · exact le_of_eq (Set.mem_singleton_iff.mp hj)

/-- The SAME constant whole original path is its actual original nerve edge. -/
def rootTrianglePathWord : (nerve (SimplicialThickening.Path (rootTriangleZero.{u}) rootTriangleOne)) _⦋1⦌ :=
  ComposableArrows.mk₁ (𝟙 rootTrianglePath)

/-- Acting by the SAME whole path on the SAME zero-coface coefficient edge gives the full original middle inclusion. -/
theorem rootTriangle_middle_action :
    (coneAction rootTriangleZero rootTriangleOne).hom.app (op ⦋1⦌)
      (rootTrianglePathWord.{u},
        (coneImage (coneCofaceEmbedding (0 : Fin 3)).toOrderHom zeroOne).hom.app (op ⦋1⦌)
          coefficientEdge) = (nerve.edgeMk rootTriangleMiddle).edge := by
  refine CategoryTheory.Functor.ext (fun k => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  fin_cases k <;> apply ConeSubset.ext
  · change rootTrianglePath.I.toFinite.toFinset ∪
      ({zeroOne} : Finset (Vertex.{u} 1)).image (coneCofaceEmbedding (0 : Fin 3)) =
        {rootTriangleZero, rootTriangleOne}
    rw [Finset.image_singleton]
    change rootTrianglePath.I.toFinite.toFinset ∪ {rootTriangleOne} = _
    simp [rootTrianglePath]
  · change rootTrianglePath.I.toFinite.toFinset ∪
      ({zeroOne, ULift.up (1 : Fin 2)} : Finset (Vertex.{u} 1)).image
        (coneCofaceEmbedding (0 : Fin 3)) = {rootTriangleZero, rootTriangleOne, ULift.up (2 : Fin 3)}
    rw [Finset.image_insert, Finset.image_singleton]
    change rootTrianglePath.I.toFinite.toFinset ∪ {rootTriangleOne, ULift.up (2 : Fin 3)} = _
    ext j
    simp [rootTrianglePath]

/-- The SAME original long-to-whole coefficient edge is already marked by its unchanged maximum. -/
theorem rootTriangle_constant_marked :
    (nerve.edgeMk rootTriangleConstant.{u}).edge ∈ (coneWeight rootTriangleZero).marking := by
  have maximum_eq (a : ConeSubset (rootTriangleZero.{u}))
      (h : ULift.up (2 : Fin 3) ∈ a.vertices) : a.maximum = ULift.up (2 : Fin 3) :=
    le_antisymm le_top (a.le_maximum _ h)
  exact (maximum_eq rootTriangleLong (by simp [rootTriangleLong])).trans
    (maximum_eq rootTriangleWhole (by simp [rootTriangleWhole])).symm

end SSet.Marked.CoherentWeight
