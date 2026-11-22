/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootCoordinateRelativeWeakCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryChart
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentDiagramProjectiveMonomorphisms

/-!
# Actual native free-root coordinate and scalar weak attachments

The free source is the original thickened coherent-simplex root, with
the unchanged marked scalar cell and every original Hom coordinate.
Its actual full weak-mono left class follows from the genuine coefficient
model. The same whole base simplex left-extends that original free arrow.
It is a trivial cofibration in the actual coherent diagram model, retaining
its original universal unit map over arbitrary original non-Kan bases.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq
  coefficientMarkedModelCategory

/-- The original whole marked coordinate/scalar cell is freed at the unchanged original thickened coherent-simplex
root. -/
def coneRootCoordinateScalarFreeArrow {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌) : Arrow (EnrichedDiagram (Index.{u} (n + 1))ᵒᵖ) :=
  Arrow.mk ((enrichedFreeDiagramFunctor (Index.{u} (n + 1))ᵒᵖ
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))).map
      (coneRootCoordinateScalarCell j hj a))

/-- The actual original free-root scalar attachment lies in the full original coefficient weak-mono projective left
class. -/
theorem coneRootCoordinateScalarFreeArrow_projectiveWeakLeft {n d : ℕ}
    (j : Fin (n + 2)) (hj : 0 < j) (hj' : j < Fin.last (n + 1)) (hd : 0 < d)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (ha₀ : (a.obj 0).maximum = (⊥ : Vertex.{u} n))
    (ha₁ : (a.obj (Fin.last d)).maximum = (⊤ : Vertex.{u} n)) :
    (enrichedFreeGenerators (Index.{u} (n + 1))ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      (coneRootCoordinateScalarFreeArrow j hj a).hom := by
  let c := op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))
  let f := coneRootCoordinateScalarCell j hj a
  have hleft : coefficientGeneratingWeakMonos.rlp.llp f := by
    rw [coefficientGeneratingWeakMonos_rlp, fibrations_llp]
    exact coneRootCoordinateScalarCell_trivialCofibration j hj hj' hd a ha₀ ha₁
  intro F G p hp
  exact (Adjunction.hasLiftingProperty_iff
    (enrichedFreeEvaluationAdjunction (Index.{u} (n + 1))ᵒᵖ c) f p).mpr
      (hleft (p.app c)
        ((enrichedFreeGenerators_rlp_iff (Index.{u} (n + 1))ᵒᵖ coefficientGeneratingWeakMonos p).mp hp c))

/-- The same whole original base simplex left-extends the original free-root marked coordinate/scalar arrow. -/
def nativeRootCoordinateScalarFreeArrow {n d : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (j : Fin (n + 2)) (hj : 0 < j) (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌) :
    Arrow (EnrichedDiagram (realization B)ᵒᵖ) :=
  (EnrichedLeftKan.leftExtension (EnrichedFunctor.opposite (simplexInto B σ))).mapArrow.obj
    (coneRootCoordinateScalarFreeArrow j hj a)

/-- Every actual native free-root coordinate/scalar attachment retains the full original weak-mono projective left
class over its same whole original base simplex. -/
theorem nativeRootCoordinateScalarFreeArrow_projectiveWeakLeft {n d : ℕ}
    (B : SSet.{u}) (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) (hd : 0 < d)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (ha₀ : (a.obj 0).maximum = (⊥ : Vertex.{u} n))
    (ha₁ : (a.obj (Fin.last d)).maximum = (⊤ : Vertex.{u} n)) :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      (nativeRootCoordinateScalarFreeArrow B σ j hj a).hom :=
  enrichedLeftKan_freeLeft (EnrichedFunctor.opposite (simplexInto B σ)) coefficientGeneratingWeakMonos
    (coneRootCoordinateScalarFreeArrow j hj a).hom
    (coneRootCoordinateScalarFreeArrow_projectiveWeakLeft j hj hj' hd a ha₀ ha₁)

/-- The unchanged native free-root coordinate/scalar map is a genuine trivial cofibration in the actually
constructed original coherent marked model. -/
theorem nativeRootCoordinateScalarFreeArrow_trivialCofibration {n d : ℕ}
    (B : SSet.{u}) (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) (hd : 0 < d)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌)
    (ha₀ : (a.obj 0).maximum = (⊥ : Vertex.{u} n))
    (ha₁ : (a.obj (Fin.last d)).maximum = (⊤ : Vertex.{u} n)) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
      (nativeRootCoordinateScalarFreeArrow B σ j hj a).hom := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeRootCoordinateScalarFreeArrow_projectiveWeakLeft B σ j hj hj' hd a ha₀ ha₁

/-- The same actual original relative nondegenerate scalar supplies a native free-root trivial cofibration without
endpoint, dimension or weak-class certificates as inputs. -/
theorem nativeRootCoordinateRelativeFreeArrow_trivialCofibration {n : ℕ}
    (B : SSet.{u}) (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) (s : (coneCoordinateBoundary (⊥ : Vertex.{u} n)).N) :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
      (nativeRootCoordinateScalarFreeArrow B σ j hj s.simplex).hom := by
  obtain ⟨h₀, h₁⟩ := coneRootCoordinateRelative_native_maxima s
  have hd := coneRootCoordinateRelative_native_positive_dim
    (nativeRootCoordinate_inner_positive_dimension j hj hj') s
  exact nativeRootCoordinateScalarFreeArrow_trivialCofibration B σ j hj hj' hd s.simplex h₀ h₁

/-- The same native map evaluates to a genuine coefficient trivial cofibration at every actual coherent-base object,
retaining the whole original component map. -/
theorem nativeRootCoordinateRelativeFreeArrow_component_trivialCofibration {n : ℕ}
    (B : SSet.{u}) (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) (s : (coneCoordinateBoundary (⊥ : Vertex.{u} n)).N)
    (x : (realization B)ᵒᵖ) :
    trivialCofibrations Marked.{u} ((nativeRootCoordinateScalarFreeArrow B σ j hj s.simplex).hom.app x) := by
  let _ := coherentDiagramModelCategory B
  let f := (nativeRootCoordinateScalarFreeArrow B σ j hj s.simplex).hom
  have ht := nativeRootCoordinateRelativeFreeArrow_trivialCofibration B σ j hj hj' s
  have hc : (coherentDiagramGeneratingMonos B).rlp.llp f := ht.1
  have hw : coherentDiagramWeakEquivalences B f := ht.2
  exact ⟨coherentDiagram_projectiveLeft_evaluation_cofibration B f hc x,
    (EvaluationTransfer.evaluationProperty_iff
      (fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c)
      (weakEquivalences Marked.{u}) f).mp hw x⟩

/-- The actual native free-root attachment retains its exact original universal unit mate as a whole enriched map. -/
theorem nativeRootCoordinateScalarFreeArrow_unit {n d : ℕ}
    (B : SSet.{u}) (σ : B _⦋n + 1⦌) (j : Fin (n + 2)) (hj : 0 < j)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌) :
    EnrichedLeftKan.universalHomEquiv (EnrichedFunctor.opposite (simplexInto B σ))
      (coneRootCoordinateScalarFreeArrow j hj a).left
      (nativeRootCoordinateScalarFreeArrow B σ j hj a).right
      (nativeRootCoordinateScalarFreeArrow B σ j hj a).hom =
        (coneRootCoordinateScalarFreeArrow j hj a).hom ≫
          EnrichedLeftKan.unit (EnrichedFunctor.opposite (simplexInto B σ))
            (coneRootCoordinateScalarFreeArrow j hj a).right :=
  EnrichedLeftKan.map_homEquiv (EnrichedFunctor.opposite (simplexInto B σ))
    (coneRootCoordinateScalarFreeArrow j hj a).hom

end SSet.Marked
