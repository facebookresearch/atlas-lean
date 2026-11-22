/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeDoubleCofaceSupport
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCofaceImages

/-!
# The full original marked lower/lower intersection at the root

The exact original two-lower-face subcomplex inherits every original
maximum mark. Its unchanged two coordinate projections preserve the
whole original inclusion. The original double-coface supported image
isomorphism gives its full marked smaller-root-cone parametrization.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual full original lower/lower root-coordinate intersection retains both original omitted vertices and
every inherited original maximum mark. -/
def coneLowerLowerRootFaceWeight {n : ℕ} (j k : Fin (n + 3)) : Marked.{u} :=
  comap (coneWeight (⊥ : Vertex.{u} (n + 2)))
    (coneCoordinateFace (⊥ : Vertex.{u} (n + 2)) (ULift.up j) false ⊓
      coneCoordinateFace (⊥ : Vertex.{u} (n + 2)) (ULift.up k) false).ι

/-- The whole original marked two-lower-face intersection enters the unchanged original full root cone. -/
def coneLowerLowerRootFaceInclusion {n : ℕ} (j k : Fin (n + 3)) :
    coneLowerLowerRootFaceWeight.{u} j k ⟶ coneWeight (⊥ : Vertex.{u} (n + 2)) :=
  comapHom (coneWeight (⊥ : Vertex.{u} (n + 2)))
    (coneCoordinateFace (⊥ : Vertex.{u} (n + 2)) (ULift.up j) false ⊓
      coneCoordinateFace (⊥ : Vertex.{u} (n + 2)) (ULift.up k) false).ι

/-- The actual original full lower/lower intersection retains its unchanged first original coordinate projection. -/
def coneLowerLowerRootFaceLeft {n : ℕ} (j k : Fin (n + 3)) :
    coneLowerLowerRootFaceWeight.{u} j k ⟶ coneLowerRootFaceWeight j :=
  (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 2)))).map (homOfLE inf_le_left)

/-- The actual original full lower/lower intersection retains its unchanged second original coordinate projection. -/
def coneLowerLowerRootFaceRight {n : ℕ} (j k : Fin (n + 3)) :
    coneLowerLowerRootFaceWeight.{u} j k ⟶ coneLowerRootFaceWeight k :=
  (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 2)))).map (homOfLE inf_le_right)

/-- The unchanged original first coordinate projection retains the whole actual original intersection inclusion. -/
theorem coneLowerLowerRootFaceLeft_inclusion {n : ℕ} (j k : Fin (n + 3)) :
    coneLowerLowerRootFaceLeft.{u} j k ≫ coneLowerRootFaceInclusion j = coneLowerLowerRootFaceInclusion j k := by
  apply Hom.ext
  rfl

/-- The unchanged original second coordinate projection retains the whole actual original intersection inclusion. -/
theorem coneLowerLowerRootFaceRight_inclusion {n : ℕ} (j k : Fin (n + 3)) :
    coneLowerLowerRootFaceRight.{u} j k ≫ coneLowerRootFaceInclusion k = coneLowerLowerRootFaceInclusion j k := by
  apply Hom.ext
  rfl

/-- The original lower coordinate inclusion is monomorphic because its entire original scalar carrier is the
unchanged marked subcomplex inclusion. -/
instance coneLowerRootFaceInclusion_mono {n : ℕ} (j : Fin (n + 2)) :
    Mono (coneLowerRootFaceInclusion.{u} j) :=
  (mono_iff_underlying _).mpr
    (inferInstance : Mono (coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) (ULift.up j) false).ι)

/-- The complete original smaller root cone is genuinely isomorphic to the full marked original positive lower/lower
root intersection through its original supported double-coface image. -/
def coneLowerLowerRootFaceIso {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3))
    (h : j.castSucc < k) (hj : 0 < j) :
    coneWeight (⊥ : Vertex.{u} n) ≅ coneLowerLowerRootFaceWeight.{u} j.castSucc k :=
  coneDoubleCofaceMarkedIso j k h (⊥ : Vertex.{u} n) ≪≫
    eqToIso (congrArg (fun i : Vertex.{u} (n + 2) =>
      comap (coneWeight i) (coneCoordinateFace i (ULift.up j.castSucc) false ⊓
        coneCoordinateFace i (ULift.up k) false).ι) (coneDoubleCofaceEmbedding_root j k h hj))

/-- The full original marked lower/lower root parametrization retains precisely the unchanged whole original
double-coface cone image and genuine original root equality as its attaching composite. -/
theorem coneLowerLowerRootFaceIso_inclusion {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 3))
    (h : j.castSucc < k) (hj : 0 < j) :
    (coneLowerLowerRootFaceIso.{u} j k h hj).hom ≫ coneLowerLowerRootFaceInclusion j.castSucc k =
      coneImage (coneDoubleCofaceEmbedding j k h).toOrderHom (⊥ : Vertex.{u} n) ≫
        eqToHom (congrArg (fun i : Vertex.{u} (n + 2) => coneWeight i) (coneDoubleCofaceEmbedding_root j k h hj)) := by
  let f := coneDoubleCofaceEmbedding.{u} j k h
  let e := coneDoubleCofaceMarkedIso j k h (⊥ : Vertex.{u} n)
  let hr := coneDoubleCofaceEmbedding_root.{u} j k h hj
  let z := fun i : Vertex.{u} (n + 2) =>
    comapHom (coneWeight i) (coneCoordinateFace i (ULift.up j.castSucc) false ⊓ coneCoordinateFace i (ULift.up k)
      false).ι
  have ht := eqToHom_naturality z hr
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => e.hom ≫ a) ht.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ eqToHom (congrArg (fun i : Vertex.{u} (n + 2) => coneWeight i) hr))
          (coneDoubleCofaceMarkedIso_inclusion j k h (⊥ : Vertex.{u} n)))))

end SSet.Marked.CoherentWeight
