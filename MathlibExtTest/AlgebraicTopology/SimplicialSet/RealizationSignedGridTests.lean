/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationSignedGrid

/-!
# Tests for signed realization-grid algebra

These clients exercise only relation-assuming finite category algebra. They do
not construct target triangles or assert existence of an approximating grid.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace RealizationSignedGridTests

private noncomputable def identityGrid {X : SSet.{u}} (x : X _⦋0⦌)
    (rows cols : ℕ) : SSet.RelativeGridCertificate X rows cols where
  vertex := fun _ _ => x
  horizontal := fun _ _ => SSet.SignedEdge.identity x
  vertical := fun _ _ => SSet.SignedEdge.identity x
  diagonal := fun _ _ => SSet.SignedEdge.identity x
  lower := fun _ _ => ⟨by simp⟩
  upper := fun _ _ => ⟨by simp⟩
  leftVertex := x
  rightVertex := x
  left_vertex := fun _ => rfl
  right_vertex := fun _ => rfl
  left_constant := fun _ => by simp
  right_constant := fun _ => by simp

section SignedEdges

example {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    (SSet.SignedEdge.forward e).toHom =
      SSet.FundamentalGroupoid.homMk e := by
  simp

example {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge y x) :
    (SSet.SignedEdge.reverse e).toHom =
      inv (SSet.FundamentalGroupoid.homMk e) := by
  simp

example {X : SSet.{u}} {x y : X _⦋0⦌} (h : x = y) :
    (SSet.SignedEdge.ofEq h).toHom =
      eqToHom (congrArg SSet.FundamentalGroupoid.mk h) := by
  simp

example {X : SSet.{u}} (x : X _⦋0⦌) :
    (SSet.SignedEdge.identity x).toHom = 𝟙 _ := by
  simp

example {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) :
    e.reverseTraversal.reverseTraversal = e := by
  simp

example {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.SignedEdge X x y) :
    e.reverseTraversal.toHom = inv e.toHom := by
  simp

end SignedEdges

section RelationsAndTelescopes

example {X : SSet.{u}} (G : SSet.RelativeGridCertificate X 1 1) :
    (G.horizontal 0 0).toHom ≫ (G.vertical 0 1).toHom =
      (G.vertical 0 0).toHom ≫ (G.horizontal 1 0).toHom :=
  G.square 0 0

example {X : SSet.{u}} (G : SSet.RelativeGridCertificate X 1 1) :
    ((G.horizontal 0 0).toHom ≫ (G.vertical 0 1).toHom =
      (G.diagonal 0 0).toHom) ∧
    ((G.vertical 0 0).toHom ≫ (G.horizontal 1 0).toHom =
      (G.diagonal 0 0).toHom) :=
  ⟨(G.lower 0 0).relation, (G.upper 0 0).relation⟩

example {X : SSet.{u}} (G : SSet.RelativeGridCertificate X 2 3)
    (r : Fin 2) :
    G.rowComposite r.castSucc ≫ (G.vertical r (Fin.last 3)).toHom =
      (G.vertical r 0).toHom ≫ G.rowComposite r.succ :=
  G.strip r

example {X : SSet.{u}} (G : SSet.RelativeGridCertificate X 2 3)
    (r : Fin 2) :
    G.normalizedRow r.castSucc = G.normalizedRow r.succ :=
  G.normalizedRow_castSucc_eq_succ r

example {X : SSet.{u}} (G : SSet.RelativeGridCertificate X 2 3) :
    G.normalizedRow 0 = G.normalizedRow (Fin.last 2) :=
  G.bottomRow_eq_topRow

example {X : SSet.{u}} (G : SSet.RelativeGridCertificate X 2 3)
    (r : Fin 2) :
    ((G.vertical r 0).toHom =
      eqToHom (congrArg SSet.FundamentalGroupoid.mk
        ((G.left_vertex r.castSucc).trans (G.left_vertex r.succ).symm))) ∧
    ((G.vertical r (Fin.last 3)).toHom =
      eqToHom (congrArg SSet.FundamentalGroupoid.mk
        ((G.right_vertex r.castSucc).trans
          (G.right_vertex r.succ).symm))) :=
  ⟨G.left_constant r, G.right_constant r⟩

end RelationsAndTelescopes

section BoundaryCases

example {X : SSet.{u}} (x : X _⦋0⦌) :
    (identityGrid x 1 1).normalizedRow 0 =
      (identityGrid x 1 1).normalizedRow (Fin.last 1) :=
  (identityGrid x 1 1).bottomRow_eq_topRow

example {X : SSet.{u}} (x : X _⦋0⦌) :
    (identityGrid x 3 4).normalizedRow 0 =
      (identityGrid x 3 4).normalizedRow (Fin.last 3) :=
  (identityGrid x 3 4).bottomRow_eq_topRow

example {X : SSet.{u}} (x : X _⦋0⦌) :
    (identityGrid x 0 0).normalizedRow 0 =
      (identityGrid x 0 0).normalizedRow (Fin.last 0) :=
  (identityGrid x 0 0).bottomRow_eq_topRow

example {X : SSet.{u}} (x : X _⦋0⦌) :
    (identityGrid x 0 3).normalizedRow 0 =
      (identityGrid x 0 3).normalizedRow (Fin.last 0) :=
  (identityGrid x 0 3).bottomRow_eq_topRow

example {X : SSet.{u}} (x : X _⦋0⦌) (r : Fin 4) :
    (identityGrid x 3 0).rowComposite r = 𝟙 _ := by
  simp

example {X : SSet.{u}} (x : X _⦋0⦌) (r : Fin 4) :
    (identityGrid x 3 1).rowComposite r =
      ((identityGrid x 3 1).horizontal r 0).toHom := by
  simp

example {X : SSet.{1}} (x : X _⦋0⦌) :
    (identityGrid x 2 2).normalizedRow 0 =
      (identityGrid x 2 2).normalizedRow (Fin.last 2) :=
  (identityGrid x 2 2).bottomRow_eq_topRow

example {X : SSet.{0}} (x : X _⦋0⦌) :
    (identityGrid x 2 2).normalizedRow 0 =
      (identityGrid x 2 2).normalizedRow (Fin.last 2) :=
  (identityGrid x 2 2).bottomRow_eq_topRow

end BoundaryCases

/-- error: Unknown constant `SSet.exists_relativeGridCertificate` -/
#guard_msgs (error, substring := true) in
#check SSet.exists_relativeGridCertificate

#print axioms SSet.SignedEdge.toHom
#print axioms SSet.RelativeGridCertificate.square
#print axioms SSet.RelativeGridCertificate.bottomRow_eq_topRow

end RealizationSignedGridTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
