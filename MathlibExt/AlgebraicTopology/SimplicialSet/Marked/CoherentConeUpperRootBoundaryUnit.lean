/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeAfterUpperColimit
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootBoundaryAfter
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SubcomplexFunctor

/-!
# The original upper root-coordinate entry into the same boundary

The original upper face enters the full positive-maximum cone through
its existing marked support isomorphism and unchanged inclusion.
That positive cone entry into the complete root boundary is exactly
the same original marked upper-coordinate inclusion.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The genuine original positive support chart retains exactly its original positive cone inclusion. -/
theorem coneAfterSupportIso_inclusion {n : ℕ} (i k : Vertex.{u} n) :
    (coneAfterSupportIso i k).hom ≫ comapHom (coneWeight i) (coneAfterSubcomplex i k).ι =
      coneAfterInclusion i k := by
  apply Hom.ext
  ext q a
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- Every whole original upper face keeps precisely its original unchanged inclusion after entering the full
positive coefficient. -/
theorem coneUpperFaceToAfter_inclusion {n : ℕ} (i k : Vertex.{u} n) (j : AfterVertex k) :
    coneUpperFaceToAfter i k j ≫ coneAfterInclusion i k = coneUpperFaceInclusion i j.val := by
  let e := coneAfterSupportIso i k
  let p := ((coneAfterUpperDiagram i k).multicofork.toLinearOrder.map
    (subcomplexFunctor (coneWeight i))).π j
  let s := comapHom (coneWeight i) (coneAfterSubcomplex i k).ι
  have he : e.inv ≫ coneAfterInclusion i k = s :=
    (congrArg (fun a => e.inv ≫ a) (coneAfterSupportIso_inclusion i k).symm).trans
      (e.inv_hom_id_assoc s)
  have hp : p ≫ s = coneUpperFaceInclusion i j.val := by
    apply Hom.ext
    rfl
  exact (Category.assoc _ _ _).trans ((congrArg (fun a => p ≫ a) he).trans hp)

/-- Every actual positive upper root-coordinate face lies in the same complete original coordinate boundary. -/
theorem coneUpperRootFace_le_boundary {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) (ULift.up j) true ≤
      coneCoordinateBoundary (⊥ : Vertex.{u} (n + 1)) :=
  (le_iSup (fun ε : Bool => coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) (ULift.up j) ε) true).trans
    (le_iSup (fun k : {k : Vertex.{u} (n + 1) // (⊥ : Vertex.{u} (n + 1)) < k} =>
      ⨆ ε : Bool, coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) k.val ε) ⟨ULift.up j, hj⟩)

/-- The entire original marked upper root face enters the same actual supported coefficient by its unchanged
coordinate inclusion. -/
def coneUpperRootFaceToBoundary {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneUpperFaceMarked (⊥ : Vertex.{u} (n + 1)) (ULift.up j) ⟶
      coneRootBoundaryMarked (⊥ : Vertex.{u} (n + 1)) :=
  (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1)))).map
    (homOfLE (coneUpperRootFace_le_boundary j hj)) ≫ (coneRootBoundaryRootIso (n + 1)).inv

/-- The marked upper-root entry keeps exactly its unchanged original whole cone inclusion. -/
theorem coneUpperRootFaceToBoundary_inclusion {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneUpperRootFaceToBoundary.{u} j hj ≫ coneRootBoundaryInclusion (⊥ : Vertex.{u} (n + 1)) =
      coneUpperFaceInclusion (⊥ : Vertex.{u} (n + 1)) (ULift.up j) := by
  apply Hom.ext
  rfl

/-- The existing complete positive-cone upper-face map retains precisely the same actual root-boundary coordinate
entry. -/
theorem coneUpperFaceToAfter_rootBoundary {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up j, hj⟩ ≫
        coneRootBoundaryAfterInclusion (⊥ : Vertex.{u} (n + 1)) =
      coneUpperRootFaceToBoundary.{u} j hj := by
  let p := coneRootBoundaryInclusion (⊥ : Vertex.{u} (n + 1))
  apply (cancel_mono p).mp
  have h₁ := (Category.assoc _ _ _).trans
    ((congrArg (fun a => coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 1))
      (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up j, hj⟩ ≫ a)
        (coneRootBoundaryAfterInclusion_inclusion (⊥ : Vertex.{u} (n + 1)))).trans
          (coneUpperFaceToAfter_inclusion (⊥ : Vertex.{u} (n + 1))
            (⊥ : Vertex.{u} (n + 1)) ⟨ULift.up j, hj⟩))
  exact h₁.trans (coneUpperRootFaceToBoundary_inclusion j hj).symm

end SSet.Marked.CoherentWeight
