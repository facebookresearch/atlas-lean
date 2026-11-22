/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornCoordinatePairs
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeHornLowerSource
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeRootBoundaryCoordinateInverse

/-!
# The entire original marked horn-coordinate source inverse

Every retained original lower and upper coordinate has its actual
whole source map. The genuine component monomorphism into the original
full boundary detects every original ordered intersection relation.
The actual marked coordinate colimit then constructs the complete root
inverse, retaining all original scalar words, marks and coordinate legs.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked
open CoherentWeight CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every retained complete original marked horn coordinate enters the true original native horn through its genuine
original lower or upper source map. -/
def nativeHornCoordinateInverse {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (a : RootHornCoordinateIndex.{u} n k) :
    coneRootHornCoordinateFaceWeight k a ⟶ nativeOriginalHornSourceRootValue B σ k := by
  rcases a with ⟨⟨j⟩, hj⟩ | ⟨⟨j⟩, hj, hjk⟩
  · exact nativeHornUpperInverse B σ k hk j hj
  · exact nativeHornLowerInverse B σ k j hj (fun h => hjk (congrArg ULift.up h))

/-- Every retained original whole horn-coordinate map recovers precisely its unchanged original full-boundary
coordinate inverse under the actual native component inclusion. -/
theorem nativeHornCoordinateInverse_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (a : RootHornCoordinateIndex.{u} n k) :
    nativeHornCoordinateInverse B σ k hk a ≫
      (nativeOriginalHornToBoundary B σ k).app
        ((EnrichedFunctor.opposite (simplexInto B σ)).obj
          (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) =
      nativeRootCoordinateInverse B n σ (coneRootHornCoordinateOriginalIndex k a) := by
  rcases a with ⟨⟨j⟩, hj⟩ | ⟨⟨j⟩, hj, hjk⟩
  · exact nativeHornUpperInverse_boundary B σ k hk j hj
  · exact nativeHornLowerInverse_boundary B σ k j hj (fun h => hjk (congrArg ULift.up h))

/-- Every full original lower/lower, lower/upper, upper/lower and upper/upper horn intersection satisfies its actual
original marked source relation. -/
theorem nativeHornCoordinateInverse_condition {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (a b : RootHornCoordinateIndex.{u} n k) :
    coneRootHornCoordinatePairLeft k a b ≫ nativeHornCoordinateInverse B σ k hk a =
      coneRootHornCoordinatePairRight k a b ≫ nativeHornCoordinateInverse B σ k hk b := by
  let x := (EnrichedFunctor.opposite (simplexInto B σ)).obj
    (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))
  let μ := (nativeOriginalHornToBoundary B σ k).app x
  let _ : Mono μ := nativeOriginalHornToBoundary_component_mono B σ k x
  apply (cancel_mono μ).mp
  let l := coneRootHornCoordinatePairLeft k a b
  let r := coneRootHornCoordinatePairRight k a b
  let f := nativeHornCoordinateInverse B σ k hk a
  let g := nativeHornCoordinateInverse B σ k hk b
  let f' := nativeRootCoordinateInverse B n σ (coneRootHornCoordinateOriginalIndex k a)
  let g' := nativeRootCoordinateInverse B n σ (coneRootHornCoordinateOriginalIndex k b)
  have hf : f ≫ μ = f' := nativeHornCoordinateInverse_boundary B σ k hk a
  have hg : g ≫ μ = g' := nativeHornCoordinateInverse_boundary B σ k hk b
  have h : l ≫ f' = r ≫ g' := nativeRootCoordinateInverse_condition B n σ
    (coneRootHornCoordinateOriginalIndex k a) (coneRootHornCoordinateOriginalIndex k b)
  exact (Category.assoc l f μ).trans
    ((congrArg (fun t => l ≫ t) hf).trans
      (h.trans ((congrArg (fun t => r ≫ t) hg.symm).trans (Category.assoc r g μ).symm)))

/-- The same entire original horn-coordinate multispan retains every complete original marked face and ordered pair
intersection. -/
abbrev nativeHornCoordinateSpan {n : ℕ} (k : Fin (n + 2)) :=
  (coneRootHornCoordinateDiagram k).multispanIndex.map
    (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1))))

/-- All genuine original coordinate inverse maps give the actual complete original marked horn multicofork in the
true original native source coefficient. -/
def nativeHornCoordinateInverseCocone {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) : Multicofork (nativeHornCoordinateSpan.{u} k) :=
  Multicofork.ofπ _ (nativeOriginalHornSourceRootValue B σ k)
    (nativeHornCoordinateInverse B σ k hk)
    (fun p => nativeHornCoordinateInverse_condition B σ k hk p.1 p.2)

/-- The complete same original supported root horn maps into its actual original native source coefficient by
genuine full marked coordinate-colimit descent. -/
def nativeHornRootCoordinateInverse {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    coneRootHornMarked k (⊥ : Vertex.{u} (n + 1)) ⟶ nativeOriginalHornSourceRootValue B σ k :=
  (coneRootHornRootIso k).hom ≫
    (coneRootHornCoordinateMarkedIsColimit k).desc (nativeHornCoordinateInverseCocone B σ k hk)

/-- Every entire original horn-coordinate leg retains exactly its same genuine whole marked native source inverse. -/
theorem nativeHornRootCoordinateInverse_leg {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) (a : RootHornCoordinateIndex.{u} n k) :
    coneRootHornCoordinateFaceToHorn k a ≫ nativeHornRootCoordinateInverse B σ k hk =
      nativeHornCoordinateInverse B σ k hk a := by
  let e := coneRootHornRootIso.{u} k
  let π := ((coneRootHornCoordinateDiagram k).multicofork.map
    (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1))))).π a
  let d := (coneRootHornCoordinateMarkedIsColimit k).desc (nativeHornCoordinateInverseCocone B σ k hk)
  have hf : π ≫ d = nativeHornCoordinateInverse B σ k hk a :=
    (coneRootHornCoordinateMarkedIsColimit k).fac (nativeHornCoordinateInverseCocone B σ k hk) (.right a)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => π ≫ f) (e.inv_hom_id_assoc d)).trans hf)

/-- The complete original marked horn-root inverse recovers precisely the original whole boundary inverse after the
literal original support and native source inclusions. -/
theorem nativeHornRootCoordinateInverse_boundary {n : ℕ} (B : SSet.{u}) (σ : B _⦋n + 1⦌)
    (k : Fin (n + 2)) (hk : 0 < k) :
    nativeHornRootCoordinateInverse B σ k hk ≫
      (nativeOriginalHornToBoundary B σ k).app
        ((EnrichedFunctor.opposite (simplexInto B σ)).obj
          (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1))))) =
      coneRootHornToBoundary k (⊥ : Vertex.{u} (n + 1)) ≫ nativeRootBoundaryCoordinateInverse B n σ := by
  let e := coneRootHornRootIso.{u} k
  let C := coneRootHornCoordinateMarkedIsColimit k
  let d := C.desc (nativeHornCoordinateInverseCocone B σ k hk)
  let μ := (nativeOriginalHornToBoundary B σ k).app
    ((EnrichedFunctor.opposite (simplexInto B σ)).obj
      (op (SimplicialThickening.mk (⊥ : Vertex.{u} (n + 1)))))
  let h := coneRootHornToBoundary k (⊥ : Vertex.{u} (n + 1))
  let γ := nativeRootBoundaryCoordinateInverse B n σ
  have hd : d ≫ μ = e.inv ≫ (h ≫ γ) := by
    apply Multicofork.IsColimit.hom_ext C
    intro a
    let π := ((coneRootHornCoordinateDiagram k).multicofork.map
      (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1))))).π a
    let p := coneRootHornCoordinateFaceToHorn k a
    have hf : π ≫ d = nativeHornCoordinateInverse B σ k hk a :=
      C.fac (nativeHornCoordinateInverseCocone B σ k hk) (.right a)
    have hl : π ≫ (d ≫ μ) = nativeRootCoordinateInverse B n σ (coneRootHornCoordinateOriginalIndex k a) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ μ) hf).trans (nativeHornCoordinateInverse_boundary B σ k hk a))
    have hr : π ≫ (e.inv ≫ (h ≫ γ)) = nativeRootCoordinateInverse B n σ (coneRootHornCoordinateOriginalIndex k a) :=
      (Category.assoc π e.inv (h ≫ γ)).symm.trans
        ((Category.assoc p h γ).symm.trans
          ((congrArg (fun f => f ≫ γ) (coneRootHornCoordinateFaceToHorn_boundary k a)).trans
            (nativeRootBoundaryCoordinateInverse_leg B n σ (coneRootHornCoordinateOriginalIndex k a))))
    exact hl.trans hr.symm
  exact (Category.assoc e.hom d μ).trans
    ((congrArg (fun f => e.hom ≫ f) hd).trans (e.hom_inv_id_assoc (h ≫ γ)))

end SSet.Marked
