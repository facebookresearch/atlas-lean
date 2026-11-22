/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeCofaceSupport
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryCell
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SubcomplexFunctor

/-!
# The original lower coordinate faces at the cone root

Every positive omitted coface vertex leaves the original root fixed.
The genuine whole marked coface image is therefore exactly the same
lower root-coordinate face. Its inclusion and entry into the complete
root boundary retain the original simplex words and maximum marking.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- Omitting a positive original vertex preserves exactly the same original cone root. -/
theorem coneCofaceEmbedding_root {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneCofaceEmbedding.{u} j (⊥ : Vertex.{u} n) = (⊥ : Vertex.{u} (n + 1)) := by
  apply ULift.ext
  exact Fin.succAbove_ne_zero_zero (ne_of_gt hj)

/-- The actual original lower root-coordinate face inherits the original whole maximum-preserving marking. -/
def coneLowerRootFaceWeight {n : ℕ} (j : Fin (n + 2)) : Marked.{u} :=
  comap (coneWeight (⊥ : Vertex.{u} (n + 1)))
    (coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) (ULift.up j) false).ι

/-- The original full lower root face enters the unchanged full original root cone. -/
def coneLowerRootFaceInclusion {n : ℕ} (j : Fin (n + 2)) :
    coneLowerRootFaceWeight.{u} j ⟶ coneWeight (⊥ : Vertex.{u} (n + 1)) :=
  comapHom (coneWeight (⊥ : Vertex.{u} (n + 1)))
    (coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) (ULift.up j) false).ι

/-- The whole original supported-subcomplex embedding isomorphism keeps precisely the original cone image after its
unchanged supported inclusion. -/
theorem coneEmbeddingSupportedIso_inclusion {n m : ℕ} (f : Vertex.{u} n ↪o Vertex.{u} m)
    (i : Vertex.{u} n) :
    (coneEmbeddingSupportedIso f i).hom ≫
        comapHom (coneWeight (f i)) (coneSupportedSubcomplex f i).ι = coneImage f.toOrderHom i := by
  apply Hom.ext
  ext q a
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- The genuine complete coface image keeps precisely the original whole cone-image map after its unchanged
lower-face inclusion. -/
theorem coneCofaceMarkedIso_inclusion {n : ℕ} (j : Fin (n + 2)) (i : Vertex.{u} n) :
    (coneCofaceMarkedIso j i).hom ≫
        comapHom (coneWeight (coneCofaceEmbedding j i))
          (coneCoordinateFace (coneCofaceEmbedding j i) (ULift.up j) false).ι =
      coneImage (coneCofaceEmbedding j).toOrderHom i := by
  let f := coneCofaceEmbedding.{u} j
  let h := coneCofaceSupportedSubcomplex j i
  let e := coneEmbeddingSupportedIso f i
  let z := fun A : (nerve (ConeSubset (f i))).Subcomplex => comapHom (coneWeight (f i)) A.ι
  have ht : eqToHom (congrArg (fun A : (nerve (ConeSubset (f i))).Subcomplex =>
      comap (coneWeight (f i)) A.ι) h) ≫ z (coneCoordinateFace (f i) (ULift.up j) false) =
        z (coneSupportedSubcomplex f i) :=
    (eqToHom_naturality z h).symm.trans (Category.comp_id _)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun v => e.hom ≫ v) ht).trans (coneEmbeddingSupportedIso_inclusion f i))

/-- The full original smaller root cone is isomorphic to precisely the original lower root-coordinate face through
its same marked coface image and genuine root equality. -/
def coneLowerRootFaceIso {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneWeight (⊥ : Vertex.{u} n) ≅ coneLowerRootFaceWeight.{u} j :=
  coneCofaceMarkedIso j (⊥ : Vertex.{u} n) ≪≫
    eqToIso (congrArg (fun i : Vertex.{u} (n + 1) =>
      comap (coneWeight i) (coneCoordinateFace i (ULift.up j) false).ι)
        (coneCofaceEmbedding_root j hj))

/-- The rooted original lower-face isomorphism retains its exact cone-image inclusion and whole original root
transport. -/
theorem coneLowerRootFaceIso_inclusion {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    (coneLowerRootFaceIso.{u} j hj).hom ≫ coneLowerRootFaceInclusion j =
      coneImage (coneCofaceEmbedding j).toOrderHom (⊥ : Vertex.{u} n) ≫
        eqToHom (congrArg (fun i : Vertex.{u} (n + 1) => coneWeight i) (coneCofaceEmbedding_root j hj)) := by
  let h := coneCofaceEmbedding_root.{u} j hj
  let e := coneCofaceMarkedIso j (⊥ : Vertex.{u} n)
  let z := fun i : Vertex.{u} (n + 1) =>
    comapHom (coneWeight i) (coneCoordinateFace i (ULift.up j) false).ι
  have ht := eqToHom_naturality z h
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun v => e.hom ≫ v) ht.symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun v => v ≫ eqToHom (congrArg (fun i : Vertex.{u} (n + 1) => coneWeight i) h))
          (coneCofaceMarkedIso_inclusion j (⊥ : Vertex.{u} n)))))

/-- Every actual positive lower root-coordinate face lies in the same complete original coordinate boundary. -/
theorem coneLowerRootFace_le_boundary {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) (ULift.up j) false ≤
      coneCoordinateBoundary (⊥ : Vertex.{u} (n + 1)) :=
  (le_iSup (fun ε : Bool => coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) (ULift.up j) ε) false).trans
    (le_iSup (fun k : {k : Vertex.{u} (n + 1) // (⊥ : Vertex.{u} (n + 1)) < k} =>
      ⨆ ε : Bool, coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) k.val ε) ⟨ULift.up j, hj⟩)

/-- The whole marked original lower root face enters the same actual complete supported root coefficient. -/
def coneLowerRootFaceToBoundary {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneLowerRootFaceWeight.{u} j ⟶ coneRootBoundaryMarked (⊥ : Vertex.{u} (n + 1)) :=
  (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1)))).map
    (homOfLE (coneLowerRootFace_le_boundary j hj)) ≫ (coneRootBoundaryRootIso (n + 1)).inv

/-- The original lower root-face entry preserves exactly its unchanged marked inclusion in the full original cone. -/
theorem coneLowerRootFaceToBoundary_inclusion {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneLowerRootFaceToBoundary.{u} j hj ≫ coneRootBoundaryInclusion (⊥ : Vertex.{u} (n + 1)) =
      coneLowerRootFaceInclusion j := by
  apply Hom.ext
  rfl

end SSet.Marked.CoherentWeight
