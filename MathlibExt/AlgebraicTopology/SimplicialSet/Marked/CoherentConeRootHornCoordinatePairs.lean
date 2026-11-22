/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootHornBoundaryInclusion
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateBoundaryLegs

/-!
# Every original marked coordinate and intersection of the root horn

All original upper faces and every nonomitted original lower face keep
their original labels, complete simplex words and maximum marking.
Every ordered pair keeps its actual full original intersection and both
original projections. Their actual simplicial multicoequalizer lifts to
a marked colimit through the same inherited marking on every edge.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original horn retains every positive upper coordinate and precisely the nonomitted positive lower
coordinates. -/
abbrev RootHornCoordinateIndex (n : ℕ) (k : Fin (n + 2)) :=
  Sum {j : Vertex.{u} (n + 1) // ⊥ < j}
    {j : Vertex.{u} (n + 1) // ⊥ < j ∧ j ≠ ULift.up k}

/-- Every retained original horn coordinate keeps its same original complete boundary-coordinate label. -/
def coneRootHornCoordinateOriginalIndex {n : ℕ} (k : Fin (n + 2))
    (a : RootHornCoordinateIndex.{u} n k) : RootCoordinateIndex.{u} n :=
  match a with
  | .inl j => (j, true)
  | .inr j => (⟨j.val, j.property.1⟩, false)

/-- The entire original horn face is the same original constant-coordinate subcomplex. -/
def coneRootHornCoordinateFaceAt {n : ℕ} (k : Fin (n + 2))
    (a : RootHornCoordinateIndex.{u} n k) : (nerve (ConeSubset (⊥ : Vertex.{u} (n + 1)))).Subcomplex :=
  coneCoordinateFaceAt (⊥ : Vertex.{u} (n + 1)) (coneRootHornCoordinateOriginalIndex k a)

/-- Every retained original horn coordinate inherits the same full original marked face. -/
abbrev coneRootHornCoordinateFaceWeight {n : ℕ} (k : Fin (n + 2))
    (a : RootHornCoordinateIndex.{u} n k) :=
  coneRootCoordinateFaceWeight n (coneRootHornCoordinateOriginalIndex k a)

/-- Every original ordered horn-coordinate pair retains its complete original marked intersection. -/
abbrev coneRootHornCoordinatePairWeight {n : ℕ} (k : Fin (n + 2))
    (a b : RootHornCoordinateIndex.{u} n k) :=
  coneRootCoordinatePairWeight n (coneRootHornCoordinateOriginalIndex k a) (coneRootHornCoordinateOriginalIndex k b)

/-- The unchanged first projection of each complete original marked horn-coordinate intersection. -/
abbrev coneRootHornCoordinatePairLeft {n : ℕ} (k : Fin (n + 2))
    (a b : RootHornCoordinateIndex.{u} n k) :=
  coneRootCoordinatePairLeft n (coneRootHornCoordinateOriginalIndex k a) (coneRootHornCoordinateOriginalIndex k b)

/-- The unchanged second projection of each complete original marked horn-coordinate intersection. -/
abbrev coneRootHornCoordinatePairRight {n : ℕ} (k : Fin (n + 2))
    (a b : RootHornCoordinateIndex.{u} n k) :=
  coneRootCoordinatePairRight n (coneRootHornCoordinateOriginalIndex k a) (coneRootHornCoordinateOriginalIndex k b)

/-- The actual original retained coordinate faces and every full original intersection present precisely the same
entire original root-coordinate horn. -/
theorem coneRootHornCoordinateDiagram {n : ℕ} (k : Fin (n + 2)) :
    Subcomplex.MulticoequalizerDiagram (coneRootCoordinateHorn.{u} k)
      (coneRootHornCoordinateFaceAt.{u} k)
      (fun a b => coneRootHornCoordinateFaceAt.{u} k a ⊓ coneRootHornCoordinateFaceAt.{u} k b) where
  iSup_eq := by
    change (⨆ a : RootHornCoordinateIndex.{u} n k, coneRootHornCoordinateFaceAt k a :
      (nerve (ConeSubset (⊥ : Vertex.{u} (n + 1)))).Subcomplex) =
      ⨆ a : RootHornCoordinateIndex.{u} n k,
        match a with
        | .inl j => coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) j.val true
        | .inr j => coneCoordinateFace (⊥ : Vertex.{u} (n + 1)) j.val false
    apply congrArg (fun f : RootHornCoordinateIndex.{u} n k →
      (nerve (ConeSubset (⊥ : Vertex.{u} (n + 1)))).Subcomplex => ⨆ a, f a)
    funext a
    cases a <;> rfl
  eq_inf _ _ := rfl

/-- Every entire original coordinate face and intersection gives the actual simplicial colimit of the original root
horn. -/
def coneRootHornCoordinateIsColimit {n : ℕ} (k : Fin (n + 2)) :
    IsColimit ((coneRootHornCoordinateDiagram.{u} k).multicofork.map Subcomplex.toSSetFunctor) :=
  (coneRootHornCoordinateDiagram.{u} k).isColimit

/-- The same complete original coordinate/intersection cocone is genuinely a marked colimit with every inherited
original maximum mark retained. -/
def coneRootHornCoordinateMarkedIsColimit {n : ℕ} (k : Fin (n + 2)) :
    IsColimit ((coneRootHornCoordinateDiagram.{u} k).multicofork.map
      (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1))))) := by
  apply isColimitOfUnderlyingMarking
  · exact (Multicofork.isColimitMapEquiv _ forget).symm (coneRootHornCoordinateIsColimit.{u} k)
  · intro e he
    rcases (mem_coneRootCoordinateHorn_iff k _ e.val).mp e.property with ⟨j, hj⟩ | ⟨j, hj⟩
    · let s : RootHornCoordinateIndex.{u} n k := .inl j
      let a : (coneRootHornCoordinateFaceAt k s : SSet.{u}) _⦋1⦌ :=
        ⟨e.val, (mem_coneCoordinateFace_true (⊥ : Vertex.{u} (n + 1)) j.val e.val).mpr hj⟩
      exact ⟨.right s, a, he, rfl⟩
    · let s : RootHornCoordinateIndex.{u} n k := .inr j
      let a : (coneRootHornCoordinateFaceAt k s : SSet.{u}) _⦋1⦌ :=
        ⟨e.val, (mem_coneCoordinateFace_false (⊥ : Vertex.{u} (n + 1)) j.val e.val).mpr hj⟩
      exact ⟨.right s, a, he, rfl⟩

/-- Every retained original whole marked coordinate enters the supported root horn by its actual full marked colimit
leg and unchanged original root isomorphism. -/
def coneRootHornCoordinateFaceToHorn {n : ℕ} (k : Fin (n + 2))
    (a : RootHornCoordinateIndex.{u} n k) :
    coneRootHornCoordinateFaceWeight k a ⟶ coneRootHornMarked k (⊥ : Vertex.{u} (n + 1)) :=
  ((coneRootHornCoordinateDiagram.{u} k).multicofork.map
    (subcomplexFunctor (coneWeight (⊥ : Vertex.{u} (n + 1))))).π a ≫ (coneRootHornRootIso k).inv

/-- Each original horn-coordinate entry retains its original complete cone inclusion. -/
theorem coneRootHornCoordinateFaceToHorn_inclusion {n : ℕ} (k : Fin (n + 2))
    (a : RootHornCoordinateIndex.{u} n k) :
    coneRootHornCoordinateFaceToHorn k a ≫ coneRootHornInclusion k (⊥ : Vertex.{u} (n + 1)) =
      coneRootCoordinateFaceInclusion n (coneRootHornCoordinateOriginalIndex k a) := by
  apply Hom.ext
  rfl

/-- Every retained original coordinate enters the full boundary through exactly its same original whole marked
coordinate leg. -/
theorem coneRootHornCoordinateFaceToHorn_boundary {n : ℕ} (k : Fin (n + 2))
    (a : RootHornCoordinateIndex.{u} n k) :
    coneRootHornCoordinateFaceToHorn k a ≫ coneRootHornToBoundary k (⊥ : Vertex.{u} (n + 1)) =
      coneRootCoordinateFaceToBoundary n (coneRootHornCoordinateOriginalIndex k a) := by
  apply Hom.ext
  rfl

end SSet.Marked.CoherentWeight
