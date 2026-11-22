/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateHornMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateSkeletonCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SubcomplexFunctor

/-!
# The original marked root-horn skeletal prism ladder

The native relative skeletal filtration of the original smaller-root
coordinate boundary gives the actual whole upper-endpoint prism stages.
Their marking is inherited from the SAME complete original prism. The
initial stage is the original horn source and the actual marked cocone is
a full colimit. This retains every original scalar and all stage maps;
weakness of the successor attachments is a separate conclusion.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual original smaller-root scalar stages are the native relative skeletal filtration of its unchanged
coordinate-boundary inclusion. -/
def coneRootCoordinateScalarSkeleton (n d : ℕ) : (coneWeight (⊥ : Vertex.{u} n)).toSSet.Subcomplex :=
  SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d

/-- The initial native scalar stage is precisely the entire unchanged original coordinate boundary. -/
theorem coneRootCoordinateScalarSkeleton_zero (n : ℕ) :
    coneRootCoordinateScalarSkeleton.{u} n 0 = coneCoordinateBoundary (⊥ : Vertex.{u} n) := by
  rw [coneRootCoordinateScalarSkeleton, SSet.skeletonOfMono_zero]
  ext q x
  change (∃ a : (coneCoordinateBoundary (⊥ : Vertex.{u} n)).toSSet.obj q, a.val = x) ↔
    x ∈ (coneCoordinateBoundary (⊥ : Vertex.{u} n)).obj q
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The complete original prism stage retains its unchanged whole upper endpoint and the actual native scalar
skeletal stage. -/
def coneRootCoordinateHornStage (n d : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ (coneWeight (⊥ : Vertex.{u} n)).toSSet).Subcomplex :=
  Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d)

/-- The initial original horn-prism stage is its SAME original upper endpoint and smaller-root coordinate-boundary
source. -/
theorem coneRootCoordinateHornStage_zero (n : ℕ) :
    coneRootCoordinateHornStage.{u} n 0 =
      Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n)) := by
  rw [coneRootCoordinateHornStage, coneRootCoordinateScalarSkeleton_zero]
  rfl

/-- Every actual original scalar skeletal inclusion gives the SAME whole original prism-stage inclusion. -/
theorem coneRootCoordinateHornStage_mono (n : ℕ) : Monotone (coneRootCoordinateHornStage.{u} n) := by
  intro d e h q z hz
  apply (Subcomplex.mem_unionProd_iff _ _ z).mpr
  rcases (Subcomplex.mem_unionProd_iff _ _ z).mp hz with hs | hi
  · left
    exact (SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι).monotone h _ hs
  · exact Or.inr hi

/-- Every original whole prism simplex belongs to an actual original skeletal stage, so the complete native stage
union is the entire original prism. -/
theorem coneRootCoordinateHornStage_iSup (n : ℕ) : ⨆ d : ℕ, coneRootCoordinateHornStage.{u} n d = ⊤ := by
  ext q z
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.top_obj, Set.mem_univ, iff_true]
  refine ⟨q.unop.len + 1, ?_⟩
  apply (Subcomplex.mem_unionProd_iff _ _ z).mpr
  left
  change z.2 ∈ (SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι (q.unop.len + 1)).obj q
  rw [SSet.skeletonOfMono_obj_eq_top _ (by
    change q.unop.len < q.unop.len + 1
    omega)]
  exact Set.mem_univ _

/-- The SAME actual original horn-prism stages carry the complete original larger-root marking by comap along their
literal inclusions. -/
def coneRootCoordinateHornFiltration {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) : ℕ ⥤ Marked.{u} :=
  (coneRootCoordinateHornStage_mono n).functor ⋙ subcomplexFunctor (coneRootCoordinateWholeAmbient j hj)

/-- The actual native original stage inclusions form the whole marked cocone into the SAME original complete root
prism. -/
def coneRootCoordinateHornFiltrationCocone {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    Cocone (coneRootCoordinateHornFiltration j hj) :=
  subcomplexCocone (coneRootCoordinateWholeAmbient j hj) (coneRootCoordinateHornStage_mono n).functor

/-- The initial actual marked stage is exactly the SAME original horn-prism source with its entire inherited
original marking. -/
def coneRootCoordinateHornFiltrationIsoBot {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    (coneRootCoordinateHornFiltration j hj).obj 0 ≅
      comap (coneRootCoordinateWholeAmbient j hj)
        (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n))).ι :=
  (subcomplexFunctor (coneRootCoordinateWholeAmbient j hj)).mapIso
    (eqToIso (coneRootCoordinateHornStage_zero n))

/-- The entire original marked root-horn skeletal prism ladder is a genuine full marked colimit, through the
original scalar skeletal union and exact original mark coverage. -/
def coneRootCoordinateHornFiltrationIsColimit {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) : IsColimit (coneRootCoordinateHornFiltrationCocone j hj) := by
  let F : ℕ ⥤ (coneRootCoordinateWholeAmbient j hj).toSSet.Subcomplex :=
    (coneRootCoordinateHornStage_mono.{u} n).functor
  let _ : IsFilteredOrEmpty ℕ := inferInstance
  let _ : PreservesColimitsOfShape ℕ
      (Subcomplex.toSSetFunctor (X := (coneRootCoordinateWholeAmbient j hj).toSSet)) := inferInstance
  apply subcomplexCoconeIsColimit (coneRootCoordinateWholeAmbient j hj) F 0
  · intro e he
    exact (congrArg (fun A => e ∈ A.obj (op ⦋1⦌)) (coneRootCoordinateHornStage_zero n)).to_iff.mpr
      (coneRootCoordinateWholeAmbient_marks_mem j hj hj' e he)
  · exact IsColimit.ofIsoColimit
      (isColimitOfPreserves (Subcomplex.toSSetFunctor (X := (coneRootCoordinateWholeAmbient j hj).toSSet))
        (CompleteLattice.colimitCocone F).isColimit)
      (Cocone.ext (Subcomplex.eqToIso (coneRootCoordinateHornStage_iSup n) ≪≫
        Subcomplex.topIso (coneRootCoordinateWholeAmbient j hj).toSSet))

/-- The SAME original horn-prism inclusion is the actual natural-number transfinite composition of the whole
original marked skeletal stage maps. -/
def coneRootCoordinateHornFiltrationTransfiniteComposition {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) :
    CategoryTheory.TransfiniteCompositionOfShape ℕ
      (comapHom (coneRootCoordinateWholeAmbient j hj)
        (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n))).ι) where
  F := coneRootCoordinateHornFiltration j hj
  isoBot := coneRootCoordinateHornFiltrationIsoBot j hj
  incl := (coneRootCoordinateHornFiltrationCocone j hj).ι
  isColimit := coneRootCoordinateHornFiltrationIsColimit j hj hj'
  fac := by
    apply Hom.ext
    change Subcomplex.toSSetFunctor.map (eqToHom (coneRootCoordinateHornStage_zero n).symm) ≫
      (coneRootCoordinateHornStage n 0).ι =
        (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n))).ι
    exact Subcomplex.homOfLE_ι (leOfHom (eqToHom (coneRootCoordinateHornStage_zero n).symm))

end SSet.Marked.CoherentWeight
