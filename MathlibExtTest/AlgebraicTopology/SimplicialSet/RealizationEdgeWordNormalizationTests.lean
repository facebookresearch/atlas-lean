/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationEdgeWordNormalization

/-!
# Tests for realization edge-word normalization

These public-only clients exercise dependent chain order, arbitrary-object
endpoint transports, identity-only common refinement, the canonical row
bridge, and the exact boundary adapter.  They do not construct a grid.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace RealizationEdgeWordNormalizationTests

private def vertex (i : Fin 4) : (Δ[3] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm i

private def edge (i j : Fin 4) (h : i ≤ j) :
    (Δ[3] : SSet.{u}).Edge (vertex i) (vertex j) :=
  SSet.Edge.mk (SSet.stdSimplex.edge 3 i j h)
    (by apply SSet.stdSimplex.obj₀Equiv.injective; rfl)
    (by apply SSet.stdSimplex.obj₀Equiv.injective; rfl)

private def e01 : (Δ[3] : SSet.{u}).Edge (vertex 0) (vertex 1) :=
  edge 0 1 (by decide)

private def e12 : (Δ[3] : SSet.{u}).Edge (vertex 1) (vertex 2) :=
  edge 1 2 (by decide)

private def e23 : (Δ[3] : SSet.{u}).Edge (vertex 2) (vertex 3) :=
  edge 2 3 (by decide)

private def e02 : (Δ[3] : SSet.{u}).Edge (vertex 0) (vertex 2) :=
  edge 0 2 (by decide)

private def w01 : SSet.RealizationEdgeWord (Δ[3] : SSet.{u})
    (SSet.FundamentalGroupoid.mk (vertex 0))
    (SSet.FundamentalGroupoid.mk (vertex 1)) :=
  SSet.RealizationEdgeWord.edge _ _ e01

private def w12 : SSet.RealizationEdgeWord (Δ[3] : SSet.{u})
    (SSet.FundamentalGroupoid.mk (vertex 1))
    (SSet.FundamentalGroupoid.mk (vertex 2)) :=
  SSet.RealizationEdgeWord.edge _ _ e12

private def w23 : SSet.RealizationEdgeWord (Δ[3] : SSet.{u})
    (SSet.FundamentalGroupoid.mk (vertex 2))
    (SSet.FundamentalGroupoid.mk (vertex 3)) :=
  SSet.RealizationEdgeWord.edge _ _ e23

private def w02 : SSet.RealizationEdgeWord (Δ[3] : SSet.{u})
    (SSet.FundamentalGroupoid.mk (vertex 0))
    (SSet.FundamentalGroupoid.mk (vertex 2)) :=
  SSet.RealizationEdgeWord.edge _ _ e02

private def twoStep : SSet.RealizationEdgeWord (Δ[3] : SSet.{u})
    (SSet.FundamentalGroupoid.mk (vertex 0))
    (SSet.FundamentalGroupoid.mk (vertex 2)) :=
  w01.compose w12

private def threeStepLeft : SSet.RealizationEdgeWord (Δ[3] : SSet.{u})
    (SSet.FundamentalGroupoid.mk (vertex 0))
    (SSet.FundamentalGroupoid.mk (vertex 3)) :=
  (w01.compose w12).compose w23

private def threeStepRight : SSet.RealizationEdgeWord (Δ[3] : SSet.{u})
    (SSet.FundamentalGroupoid.mk (vertex 0))
    (SSet.FundamentalGroupoid.mk (vertex 3)) :=
  w01.compose (w12.compose w23)

private def twoStepChain :
    SSet.RealizationEdgeWord.SignedChain (Δ[3] : SSet.{u}) 2
      (vertex 0) (vertex 2) :=
  .snoc (.snoc (.nil (vertex 0)) (.forward e01)) (.forward e12)

section ChainOrientation

example : twoStepChain.toHom =
    SSet.FundamentalGroupoid.homMk e01 ≫
      SSet.FundamentalGroupoid.homMk e12 := by
  simp [twoStepChain]

example : twoStepChain.vertexAt 0 = vertex 0 := by simp
example : twoStepChain.vertexAt 1 = vertex 1 := by rfl
example : twoStepChain.vertexAt 2 = vertex 2 := by rfl

example :
    (twoStepChain.edgeAt 0).data =
      (SSet.SignedEdge.forward e01).data := by
  rfl

example :
    (twoStepChain.edgeAt 1).data =
      (SSet.SignedEdge.forward e12).data := by
  rfl

/-- Reverse order is e12 inverse followed by e01 inverse. -/
example :
    (twoStepChain.reverse.edgeAt 0).data =
      (SSet.SignedEdge.reverse e12).data := by
  rfl

example :
    (twoStepChain.reverse.edgeAt 1).data =
      (SSet.SignedEdge.reverse e01).data := by
  rfl

example :
    twoStepChain.toComposableArrows.hom =
      eqToHom (congrArg SSet.FundamentalGroupoid.mk
        twoStepChain.vertexAt_zero) ≫
      twoStepChain.toHom ≫
      eqToHom (congrArg SSet.FundamentalGroupoid.mk
        twoStepChain.vertexAt_last).symm :=
  twoStepChain.rowComposite_eq_toHom

end ChainOrientation

section Normalization

example :
    (SSet.RealizationEdgeWord.normalize twoStep).1 = 2 := by
  rfl

example :
    SSet.RealizationEdgeWord.normalizedToHom
        (SSet.RealizationEdgeWord.normalize twoStep) =
      twoStep.toHom := by
  simp

example :
    _root_.Path.Homotopic.Quotient.mk
        (SSet.RealizationEdgeWord.normalizedRealizedPath
          (SSet.RealizationEdgeWord.normalize twoStep)) =
      _root_.Path.Homotopic.Quotient.mk twoStep.realizedPath := by
  exact SSet.RealizationEdgeWord.normalize_realizedPath_class twoStep

/-- Arbitrary groupoid objects retain explicit endpoint conjugation. -/
example {X : SSet.{u}} (a : SSet.FundamentalGroupoid X) :
    SSet.RealizationEdgeWord.normalizedToHom
        (SSet.RealizationEdgeWord.normalize
          (SSet.RealizationEdgeWord.identity a)) =
      𝟙 a := by
  simpa using SSet.RealizationEdgeWord.normalize_toHom
    (SSet.RealizationEdgeWord.identity a)

example :
    SSet.RealizationEdgeWord.normalizedToHom
        (SSet.RealizationEdgeWord.normalize threeStepLeft) =
      SSet.RealizationEdgeWord.normalizedToHom
        (SSet.RealizationEdgeWord.normalize threeStepRight) := by
  simp [threeStepLeft, threeStepRight, Category.assoc]

end Normalization

section CommonRefinement

private def idWord0 : SSet.RealizationEdgeWord (Δ[3] : SSet.{u})
    (SSet.FundamentalGroupoid.mk (vertex 0))
    (SSet.FundamentalGroupoid.mk (vertex 0)) :=
  SSet.RealizationEdgeWord.identity _

private def idEdge0 : (Δ[3] : SSet.{u}).Edge (vertex 0) (vertex 0) :=
  SSet.Edge.id (vertex 0)

private def idEdgeWord0 : SSet.RealizationEdgeWord (Δ[3] : SSet.{u})
    (SSet.FundamentalGroupoid.mk (vertex 0))
    (SSet.FundamentalGroupoid.mk (vertex 0)) :=
  SSet.RealizationEdgeWord.edge _ _ idEdge0

private def twoEmpty :=
  SSet.RealizationEdgeWord.commonNormalization idWord0 idWord0

private def oneEmpty :=
  SSet.RealizationEdgeWord.commonNormalization idWord0 idEdgeWord0

private def unequal :=
  SSet.RealizationEdgeWord.commonNormalization w02 twoStep

private def reverseShort : SSet.RealizationEdgeWord (Δ[3] : SSet.{u})
    (SSet.FundamentalGroupoid.mk (vertex 1))
    (SSet.FundamentalGroupoid.mk (vertex 0)) :=
  w01.inverse

private def reverseLong : SSet.RealizationEdgeWord (Δ[3] : SSet.{u})
    (SSet.FundamentalGroupoid.mk (vertex 1))
    (SSet.FundamentalGroupoid.mk (vertex 0)) :=
  reverseShort.compose idEdgeWord0

private def reversePadded :=
  SSet.RealizationEdgeWord.commonNormalization reverseShort reverseLong

private def oneEmptyEdgeZero : Fin oneEmpty.length :=
  ⟨0, by change 0 < 1; decide⟩

private def unequalEdgeOne : Fin unequal.length :=
  ⟨1, by change 1 < 2; decide⟩

private def reversePaddedEdgeZero : Fin reversePadded.length :=
  ⟨0, by change 0 < 2; decide⟩

private def reversePaddedEdgeOne : Fin reversePadded.length :=
  ⟨1, by change 1 < 2; decide⟩

example : twoEmpty.length = 0 := by rfl
example : oneEmpty.length = 1 := by rfl
example : unequal.length = 2 := by rfl
example : reversePadded.length = 2 := by rfl

example : oneEmpty.left.vertexAt 0 = vertex 0 := by simp
example : oneEmpty.left.vertexAt 1 = vertex 0 := by rfl

example :
    (oneEmpty.left.edgeAt oneEmptyEdgeZero).data =
      (SSet.SignedEdge.identity (vertex 0)).data := by
  rfl

example : unequal.left.vertexAt 1 = vertex 2 := by rfl
example : unequal.left.vertexAt 2 = vertex 2 := by rfl

example :
    (unequal.left.edgeAt unequalEdgeOne).data =
      (SSet.SignedEdge.identity (vertex 2)).data := by
  rfl

example :
    (reversePadded.left.edgeAt reversePaddedEdgeZero).data =
      (SSet.SignedEdge.reverse e01).data := by
  rfl

example :
    (reversePadded.left.edgeAt reversePaddedEdgeOne).data =
      (SSet.SignedEdge.identity (vertex 0)).data := by
  rfl

example :
    SSet.RealizationEdgeWord.normalizedToHom
      ⟨unequal.length, unequal.left⟩ = w02.toHom :=
  unequal.left_toHom

example :
    SSet.RealizationEdgeWord.normalizedToHom
      ⟨unequal.length, unequal.right⟩ = twoStep.toHom :=
  unequal.right_toHom

example :
    _root_.Path.Homotopic.Quotient.mk
        (SSet.RealizationEdgeWord.normalizedRealizedPath
          ⟨unequal.length, unequal.left⟩) =
      _root_.Path.Homotopic.Quotient.mk w02.realizedPath :=
  unequal.left_path_class

example :
    _root_.Path.Homotopic.Quotient.mk
        (SSet.RealizationEdgeWord.normalizedRealizedPath
          ⟨unequal.length, unequal.right⟩) =
      _root_.Path.Homotopic.Quotient.mk twoStep.realizedPath :=
  unequal.right_path_class

end CommonRefinement

section BoundaryAdapter

private def zeroRows :
    SSet.RealizationEdgeWord.BoundaryRows (Δ[3] : SSet.{u}) 0
      (vertex 0) (vertex 0) :=
  ⟨.nil (vertex 0), .nil (vertex 0)⟩

example : zeroRows.bottomVertex 0 = vertex 0 := by simp
example : zeroRows.topVertex 0 = vertex 0 := by simp

example (c : Fin 0) : False := Fin.elim0 c

example {cols rows : ℕ} {x y : (Δ[3] : SSet.{u}) _⦋0⦌}
    (B : SSet.RealizationEdgeWord.BoundaryRows (Δ[3] : SSet.{u})
      cols x y) (r : Fin rows) :
    (B.leftVertical r).toHom =
      𝟙 (SSet.FundamentalGroupoid.mk x) := by
  simp

example {cols rows : ℕ} {x y : (Δ[3] : SSet.{u}) _⦋0⦌}
    (B : SSet.RealizationEdgeWord.BoundaryRows (Δ[3] : SSet.{u})
      cols x y) (r : Fin rows) :
    (B.rightVertical r).toHom =
      𝟙 (SSet.FundamentalGroupoid.mk y) := by
  simp

example {cols rows : ℕ} {x y : (Δ[3] : SSet.{u}) _⦋0⦌}
    (B : SSet.RealizationEdgeWord.BoundaryRows (Δ[3] : SSet.{u})
      cols x y)
    (G : SSet.RelativeGridCertificate (Δ[3] : SSet.{u}) rows cols) :
    Prop :=
  SSet.RealizationEdgeWord.BoundaryRows.FitsGrid B G

example {cols rows : ℕ} {x y : (Δ[3] : SSet.{u}) _⦋0⦌}
    (B : SSet.RealizationEdgeWord.BoundaryRows (Δ[3] : SSet.{u})
      cols x y)
    (G : SSet.RelativeGridCertificate (Δ[3] : SSet.{u}) rows cols)
    (h : SSet.RealizationEdgeWord.BoundaryRows.FitsGrid B G)
    (c : Fin cols) :
    G.horizontal 0 c =
      SSet.RealizationEdgeWord.SignedChain.castEdge
        (B.bottomHorizontal c)
        (h.bottom_vertex c.castSucc).symm
        (h.bottom_vertex c.succ).symm :=
  h.bottom_horizontal c

end BoundaryAdapter

section BoundaryReflection

private def oneSignedLoopRows :
    SSet.RealizationEdgeWord.BoundaryRows (Δ[3] : SSet.{u}) 1
      (vertex 0) (vertex 0) :=
  ⟨.snoc (.nil (vertex 0)) (.forward idEdge0),
    .snoc (.nil (vertex 0)) (.reverse idEdge0)⟩

private def unequalRows :
    SSet.RealizationEdgeWord.BoundaryRows (Δ[3] : SSet.{u}) 2
      (vertex 0) (vertex 2) :=
  unequal.boundaryRows

/-- The theorem is universe-polymorphic and includes arbitrary certificate
endpoint transports. -/
example {X : SSet.{u}} {cols rows : ℕ} {x y : X _⦋0⦌}
    (B : SSet.RealizationEdgeWord.BoundaryRows X cols x y)
    (G : SSet.RelativeGridCertificate X rows cols) (h : B.FitsGrid G) :
    SSet.RealizationEdgeWord.normalizedToHom ⟨cols, B.bottom⟩ =
      SSet.RealizationEdgeWord.normalizedToHom ⟨cols, B.top⟩ :=
  SSet.RealizationEdgeWord.BoundaryRows.FitsGridBoundaryReflection B G h

/-- Zero columns reduce both rows to the endpoint identity. -/
example {rows : ℕ}
    (G : SSet.RelativeGridCertificate (Δ[3] : SSet.{u}) rows 0)
    (h : zeroRows.{u}.FitsGrid G) :
    SSet.RealizationEdgeWord.normalizedToHom ⟨0, zeroRows.{u}.bottom⟩ =
      SSet.RealizationEdgeWord.normalizedToHom ⟨0, zeroRows.{u}.top⟩ :=
  SSet.RealizationEdgeWord.BoundaryRows.FitsGridBoundaryReflection
    (X := (Δ[3] : SSet.{u})) (rows := rows) zeroRows.{u} G h

/-- One column exercises a forward identity edge against formal reverse
traversal of the same repeated-vertex edge. -/
example {rows : ℕ}
    (G : SSet.RelativeGridCertificate (Δ[3] : SSet.{u}) rows 1)
    (h : oneSignedLoopRows.{u}.FitsGrid G) :
    SSet.RealizationEdgeWord.normalizedToHom
        ⟨1, oneSignedLoopRows.{u}.bottom⟩ =
      SSet.RealizationEdgeWord.normalizedToHom
        ⟨1, oneSignedLoopRows.{u}.top⟩ :=
  SSet.RealizationEdgeWord.BoundaryRows.FitsGridBoundaryReflection
    (X := (Δ[3] : SSet.{u})) (rows := rows) oneSignedLoopRows.{u} G h

/-- Two columns exercise a direct forward edge padded by an identity against
the two-step forward refinement, with distinct literal endpoints. -/
example {rows : ℕ}
    (G : SSet.RelativeGridCertificate (Δ[3] : SSet.{u}) rows 2)
    (h : unequalRows.{u}.FitsGrid G) :
    SSet.RealizationEdgeWord.normalizedToHom ⟨2, unequalRows.{u}.bottom⟩ =
      SSet.RealizationEdgeWord.normalizedToHom ⟨2, unequalRows.{u}.top⟩ :=
  SSet.RealizationEdgeWord.BoundaryRows.FitsGridBoundaryReflection
    (X := (Δ[3] : SSet.{u})) (rows := rows) unequalRows.{u} G h

example {X : SSet.{1}} {cols rows : ℕ} {x y : X _⦋0⦌}
    (B : SSet.RealizationEdgeWord.BoundaryRows X cols x y)
    (G : SSet.RelativeGridCertificate X rows cols) (h : B.FitsGrid G) :
    SSet.RealizationEdgeWord.normalizedToHom ⟨cols, B.bottom⟩ =
      SSet.RealizationEdgeWord.normalizedToHom ⟨cols, B.top⟩ :=
  SSet.RealizationEdgeWord.BoundaryRows.FitsGridBoundaryReflection B G h

example {X : SSet.{0}} {cols rows : ℕ} {x y : X _⦋0⦌}
    (B : SSet.RealizationEdgeWord.BoundaryRows X cols x y)
    (G : SSet.RelativeGridCertificate X rows cols) (h : B.FitsGrid G) :
    SSet.RealizationEdgeWord.normalizedToHom ⟨cols, B.bottom⟩ =
      SSet.RealizationEdgeWord.normalizedToHom ⟨cols, B.top⟩ :=
  SSet.RealizationEdgeWord.BoundaryRows.FitsGridBoundaryReflection B G h

end BoundaryReflection

section Universes

example {X : SSet.{1}} {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) :
    SSet.RealizationEdgeWord.normalizedToHom
        (SSet.RealizationEdgeWord.normalize w) = w.toHom := by
  simp

example {X : SSet.{0}} {a b : SSet.FundamentalGroupoid X}
    (w : SSet.RealizationEdgeWord X a b) :
    SSet.RealizationEdgeWord.normalizedToHom
        (SSet.RealizationEdgeWord.normalize w) = w.toHom := by
  simp

end Universes

/-- error: Unknown constant `SSet.RealizationEdgeWord.exists_fitsGrid` -/
#guard_msgs (error, substring := true) in
#check SSet.RealizationEdgeWord.exists_fitsGrid

/-- error: Unknown constant
`SSet.RealizationEdgeWord.exists_relativeGridCertificate` -/
#guard_msgs (error, substring := true) in
#check SSet.RealizationEdgeWord.exists_relativeGridCertificate

/-- error: Unknown constant
`SSet.RealizationEdgeWord.SignedChain.splitEdge` -/
#guard_msgs (error, substring := true) in
#check SSet.RealizationEdgeWord.SignedChain.splitEdge

#print axioms SSet.RealizationEdgeWord.SignedChain.rowComposite_eq_toHom
#print axioms
  SSet.RealizationEdgeWord.map_normalizedToHom_eq_mk_normalizedRealizedPath
#print axioms SSet.RealizationEdgeWord.normalize_toHom
#print axioms SSet.RealizationEdgeWord.normalize_realizedPath_class
#print axioms SSet.RealizationEdgeWord.commonNormalization
#print axioms
  SSet.RealizationEdgeWord.BoundaryRows.FitsGridBoundaryReflection

end RealizationEdgeWordNormalizationTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
