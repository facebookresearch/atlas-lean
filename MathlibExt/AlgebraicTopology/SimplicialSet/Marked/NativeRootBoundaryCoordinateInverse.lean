/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateBoundaryLegs
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootCoordinateCocone

/-!
# The genuine complete original marked root-coordinate inverse

The actual full original marked coordinate-boundary colimit descends
the genuine lower/upper inverse cocone into the same native boundary
source root coefficient. Every original coordinate leg is retained.
The unchanged native source map recovers the original whole root
unit, and the complete original upper-coordinate cover reads exactly
the same original positive section on the entire positive root cone.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The original complete marked root-coordinate boundary maps into its same actual native source root coefficient
by genuine full marked colimit descent and the unchanged original supported-root isomorphism. -/
def nativeRootBoundaryCoordinateInverse (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    coneRootBoundaryMarked (⊥ : Vertex.{u} (n + 1)) ⟶ nativeBoundarySourceRootValue B (n + 1) σ :=
  (coneRootBoundaryRootIso (n + 1)).hom ≫
    (coneCoordinateBoundaryMarkedIsColimit (⊥ : Vertex.{u} (n + 1))).desc (nativeRootCoordinateInverseCocone B n σ)

/-- Every full original marked root-coordinate boundary leg retains exactly its same genuine native source inverse
under the complete original marked root inverse. -/
theorem nativeRootBoundaryCoordinateInverse_leg (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (a : RootCoordinateIndex.{u} n) :
    coneRootCoordinateFaceToBoundary n a ≫ nativeRootBoundaryCoordinateInverse B n σ = nativeRootCoordinateInverse B
      n σ a := by
  let e := coneRootBoundaryRootIso.{u} (n + 1)
  let π := ((coneCoordinateBoundaryDiagram (⊥ : Vertex.{u} (n + 1))).multicofork.map
    (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1))))).π a
  let d := (coneCoordinateBoundaryMarkedIsColimit (⊥ : Vertex.{u} (n + 1))).desc (nativeRootCoordinateInverseCocone
    B n σ)
  have hf : π ≫ d = nativeRootCoordinateInverse B n σ a :=
    (coneCoordinateBoundaryMarkedIsColimit (⊥ : Vertex.{u} (n + 1))).fac (nativeRootCoordinateInverseCocone B n σ)
      (.right a)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => π ≫ f) (e.inv_hom_id_assoc d)).trans hf)

/-- Each whole original marked coordinate inverse retains precisely its unchanged coordinate-boundary entry and
original native unit under the same actual all-face source comparison. -/
theorem nativeRootCoordinateInverse_source (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌)
    (a : RootCoordinateIndex.{u} n) :
    nativeRootCoordinateInverse B n σ a ≫
      (nativeBoundaryRootSourceMap B n σ).app ((EnrichedFunctor.opposite (simplexInto B σ)).obj
        (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) =
      coneRootCoordinateFaceToBoundary n a ≫
        (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootBoundaryDiagram (n + 1))).app
          (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))) := by
  rcases a with ⟨⟨⟨j⟩, hj⟩, ε⟩
  cases ε
  · exact nativeLowerRootBoundaryInverse_source B σ j hj
  · exact nativeUpperRootBoundaryInverse_source B σ j hj

/-- The same original native all-face source map recovers the entire unchanged marked root-boundary unit from the
genuine complete original coordinate inverse. -/
theorem nativeRootBoundaryCoordinateInverse_source (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    nativeRootBoundaryCoordinateInverse B n σ ≫
      (nativeBoundaryRootSourceMap B n σ).app ((EnrichedFunctor.opposite (simplexInto B σ)).obj
        (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) =
      (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootBoundaryDiagram (n + 1))).app
        (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))) := by
  let e := coneRootBoundaryRootIso.{u} (n + 1)
  let C := coneCoordinateBoundaryMarkedIsColimit (⊥ : Vertex.{u} (n + 1))
  let d := C.desc (nativeRootCoordinateInverseCocone B n σ)
  let κ := (nativeBoundaryRootSourceMap B n σ).app ((EnrichedFunctor.opposite (simplexInto B σ)).obj
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))))
  let η := (EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ)) (coneRootBoundaryDiagram (n + 1))).app
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
  have hd : d ≫ κ = e.inv ≫ η := by
    apply Multicofork.IsColimit.hom_ext C
    intro a
    let π := ((coneCoordinateBoundaryDiagram (⊥ : Vertex.{u} (n + 1))).multicofork.map
      (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1))))).π a
    have hf : π ≫ d = nativeRootCoordinateInverse B n σ a := C.fac (nativeRootCoordinateInverseCocone B n σ) (.right a)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ κ) hf).trans
        ((nativeRootCoordinateInverse_source B n σ a).trans (Category.assoc π e.inv η)))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => e.hom ≫ f) hd).trans (e.hom_inv_id_assoc η))

/-- On the entire original positive root cone, the complete genuine marked coordinate inverse retains exactly the
same original whole positive section in the actual native boundary source. -/
theorem nativeRootBoundaryCoordinateInverse_positive (B : SSet.{u}) (n : ℕ) (σ : B _⦋n + 1⦌) :
    coneRootBoundaryAfterInclusion (⊥ : Vertex.{u} (n + 1)) ≫ nativeRootBoundaryCoordinateInverse B n σ =
      (nativePositiveRootBoundarySection B σ).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))) := by
  let e := coneAfterSupportIso (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1))
  let C := coneAfterUpperSupportIsColimit (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1))
  let γ := nativeRootBoundaryCoordinateInverse B n σ
  let b := coneRootBoundaryAfterInclusion (⊥ : Vertex.{u} (n + 1))
  let P := (nativePositiveRootBoundarySection B σ).app (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
  apply (cancel_epi e.inv).mp
  apply Multicofork.IsColimit.hom_ext C
  intro j
  let π := ((coneAfterUpperDiagram (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1))).multicofork.toLinearOrder.map
    (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1))))).π j
  let u := coneUpperFaceToAfter (⊥ : Vertex.{u} (n + 1)) (⊥ : Vertex.{u} (n + 1)) j
  have hg : coneUpperRootFaceToBoundary j.val.down j.property ≫ γ = nativeUpperRootBoundaryInverse B σ j.val.down
    j.property :=
    nativeRootBoundaryCoordinateInverse_leg B n σ (coneRootUpperIndex n j.val.down j.property)
  have hu : u ≫ (b ≫ γ) = u ≫ P :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ γ) (coneUpperFaceToAfter_rootBoundary j.val.down j.property)).trans hg)
  exact (Category.assoc π e.inv (b ≫ γ)).symm.trans (hu.trans (Category.assoc π e.inv P))

end SSet.Marked
