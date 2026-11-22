/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateHornFiltration
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateSkeletonMaps
import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct

/-!
# The actual original scalar-cell squares in the whole marked horn ladder

Every original relative scalar cell enters the same old whole horn prism
through its original boundary and unchanged upper endpoint. Its entire
scalar prism enters the actual successor stage through its native scalar
attaching map. Both maps retain the same global original prism and its
inherited marking; their full marked square has the original scalar cell
as its left map.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original cell's endpoint/boundary prism enters the SAME old whole stage through its complete scalar map. -/
def coneRootCoordinateSkeletonCornerMap {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) : SSet.{u}) ⟶
      (coneRootCoordinateHornStage n d : SSet.{u}) :=
  Subcomplex.lift
    ((Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι ≫
      (𝟙 (Δ[1] : SSet.{u}) ⊗ₘ c.map)) (by
    rintro q z ⟨a, rfl⟩
    apply (Subcomplex.mem_unionProd_iff _ _ _).mpr
    rcases (Subcomplex.mem_unionProd_iff _ _ a.val).mp a.property with hs | hi
    · left
      change a.val.2 ∈ ((SSet.skeletonOfMono (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d).preimage c.map).obj q
      rw [c.preimage_map]
      exact hs
    · exact Or.inr hi)

/-- The SAME complete original scalar prism enters the successor through its unchanged native scalar attaching map. -/
def coneRootCoordinateSkeletonPrismMap {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    (Δ[1] : SSet.{u}) ⊗ Δ[d] ⟶ (coneRootCoordinateHornStage n (d + 1) : SSet.{u}) :=
  (𝟙 (Δ[1] : SSet.{u}) ⊗ₘ coneRootCoordinateSkeletonSuccessorMap c) ≫
    Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n (d + 1))

/-- The whole original corner map retains its complete unchanged scalar map into the original global prism. -/
theorem coneRootCoordinateSkeletonCornerMap_inclusion {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    coneRootCoordinateSkeletonCornerMap c ≫ (coneRootCoordinateHornStage n d).ι =
      (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι ≫
        (𝟙 (Δ[1] : SSet.{u}) ⊗ₘ c.map) := Subcomplex.lift_ι _ _

/-- The complete original successor prism map retains precisely its same original scalar map. -/
theorem coneRootCoordinateSkeletonPrismMap_inclusion {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    coneRootCoordinateSkeletonPrismMap c ≫ (coneRootCoordinateHornStage n (d + 1)).ι =
      𝟙 (Δ[1] : SSet.{u}) ⊗ₘ c.map := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro z
  apply Prod.ext
  · rfl
  · exact congrArg (fun f : (Δ[d] : SSet.{u}) ⟶
        (coneWeight (⊥ : Vertex.{u} n)).toSSet => f.app q z.2)
      (coneRootCoordinateSkeletonSuccessorMap_inclusion c)

/-- The SAME boundary leg enters the OLD whole prism stage through the actual native scalar boundary map. -/
theorem coneRootCoordinateSkeletonCornerMap_boundary {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫
        coneRootCoordinateSkeletonCornerMap c =
      (𝟙 (Δ[1] : SSet.{u}) ⊗ₘ coneRootCoordinateSkeletonBoundaryMap c) ≫
        Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (congrArg (fun f : (boundary.{u} d : SSet.{u}) ⟶
        (coneWeight (⊥ : Vertex.{u} n)).toSSet => f.app q z.2)
      (coneRootCoordinateSkeletonBoundaryMap_inclusion c)).symm

/-- The original whole upper-endpoint leg retains its SAME entire original scalar map into the unchanged whole
smaller-root cube. -/
theorem coneRootCoordinateSkeletonCornerMap_endpoint {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫
        coneRootCoordinateSkeletonCornerMap c =
      (𝟙 (horn.{u} 1 (Fin.last 1) : SSet.{u}) ⊗ₘ c.map) ≫
        Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  rfl

/-- Every original scalar corner and successor prism commute through the SAME actual whole original skeletal
inclusion. -/
theorem coneRootCoordinateSkeletonCornerMap_successor {n d : ℕ}
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    coneRootCoordinateSkeletonCornerMap c ≫
        Subcomplex.homOfLE (coneRootCoordinateHornStage_mono n (Nat.le_succ d)) =
      (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι ≫
        coneRootCoordinateSkeletonPrismMap c := by
  apply (cancel_mono (coneRootCoordinateHornStage n (d + 1)).ι).mp
  rw [Category.assoc, Subcomplex.homOfLE_ι, coneRootCoordinateSkeletonCornerMap_inclusion,
    Category.assoc, coneRootCoordinateSkeletonPrismMap_inclusion]
  rfl

/-- Every original successor scalar prism retains the SAME complete original global larger-root map. -/
theorem coneRootCoordinateSkeletonPrismMap_global {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    coneRootCoordinateSkeletonPrismMap c ≫ (coneRootCoordinateHornStage n (d + 1)).ι ≫
        coneRootCoordinateWholeMap j hj = coneRootCoordinateScalarMap j hj c.simplex :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ coneRootCoordinateWholeMap j hj)
      (coneRootCoordinateSkeletonPrismMap_inclusion c)).trans
        (coneRootCoordinateWholeMap_scalar j hj c.simplex))

/-- The SAME original corner retains its full global original scalar inclusion and prism map. -/
theorem coneRootCoordinateSkeletonCornerMap_global {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    coneRootCoordinateSkeletonCornerMap c ≫ (coneRootCoordinateHornStage n d).ι ≫
        coneRootCoordinateWholeMap j hj =
      (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι ≫
        coneRootCoordinateScalarMap j hj c.simplex :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ coneRootCoordinateWholeMap j hj)
      (coneRootCoordinateSkeletonCornerMap_inclusion c)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun f => (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι ≫ f)
            (coneRootCoordinateWholeMap_scalar j hj c.simplex))))

/-- Read the same global original successor prism on each entire original simplex. -/
theorem coneRootCoordinateSkeletonPrismMap_global_app {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d)
    (q : SimplexCategoryᵒᵖ) (e : ((Δ[1] : SSet.{u}) ⊗ Δ[d]).obj q) :
    (coneRootCoordinateWholeMap j hj).app q ((coneRootCoordinateSkeletonPrismMap c).app q e).val =
      (coneRootCoordinateScalarMap j hj c.simplex).app q e :=
  congrArg (fun f : (Δ[1] : SSet.{u}) ⊗ Δ[d] ⟶
    (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet => f.app q e)
      (coneRootCoordinateSkeletonPrismMap_global j hj c)

/-- Read the SAME original corner on its unchanged whole original endpoint/boundary simplex. -/
theorem coneRootCoordinateSkeletonCornerMap_global_app {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d)
    (q : SimplexCategoryᵒᵖ)
    (e : (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).toSSet.obj q) :
    (coneRootCoordinateWholeMap j hj).app q ((coneRootCoordinateSkeletonCornerMap c).app q e).val =
      (coneRootCoordinateScalarMap j hj c.simplex).app q e.val :=
  congrArg (fun f : (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).toSSet ⟶
    (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet => f.app q e)
      (coneRootCoordinateSkeletonCornerMap_global j hj c)

/-- The whole original scalar prism map into its native successor preserves precisely the SAME inherited original
marking. -/
def coneRootCoordinateSkeletonMarkedPrismMap {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    coneRootCoordinateScalarAmbient j hj c.simplex ⟶ (coneRootCoordinateHornFiltration j hj).obj (d + 1) where
  hom := coneRootCoordinateSkeletonPrismMap c
  preserve {e} he := by
    have h := coneRootCoordinateSkeletonPrismMap_global_app j hj c (op ⦋1⦌) e
    change (((coneRootCoordinateWholeMap j hj).app (op ⦋1⦌)
      ((coneRootCoordinateSkeletonPrismMap c).app (op ⦋1⦌) e).val).obj 0).maximum =
        (((coneRootCoordinateWholeMap j hj).app (op ⦋1⦌)
          ((coneRootCoordinateSkeletonPrismMap c).app (op ⦋1⦌) e).val).obj 1).maximum
    change (((coneRootCoordinateScalarMap j hj c.simplex).app (op ⦋1⦌) e).obj 0).maximum =
      (((coneRootCoordinateScalarMap j hj c.simplex).app (op ⦋1⦌) e).obj 1).maximum at he
    exact (congrArg (fun a => (a.obj 0).maximum) h).trans
      (he.trans (congrArg (fun a => (a.obj 1).maximum) h).symm)

/-- The SAME original scalar corner enters the OLD actual whole marked stage with its full unchanged inherited
marking. -/
def coneRootCoordinateSkeletonMarkedCornerMap {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    comap (coneRootCoordinateScalarAmbient j hj c.simplex)
        (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι ⟶
      (coneRootCoordinateHornFiltration j hj).obj d where
  hom := coneRootCoordinateSkeletonCornerMap c
  preserve {e} he := by
    have h := coneRootCoordinateSkeletonCornerMap_global_app j hj c (op ⦋1⦌) e
    change (((coneRootCoordinateWholeMap j hj).app (op ⦋1⦌)
      ((coneRootCoordinateSkeletonCornerMap c).app (op ⦋1⦌) e).val).obj 0).maximum =
        (((coneRootCoordinateWholeMap j hj).app (op ⦋1⦌)
          ((coneRootCoordinateSkeletonCornerMap c).app (op ⦋1⦌) e).val).obj 1).maximum
    change (((coneRootCoordinateScalarMap j hj c.simplex).app (op ⦋1⦌) e.val).obj 0).maximum =
      (((coneRootCoordinateScalarMap j hj c.simplex).app (op ⦋1⦌) e.val).obj 1).maximum at he
    exact (congrArg (fun a => (a.obj 0).maximum) h).trans
      (he.trans (congrArg (fun a => (a.obj 1).maximum) h).symm)

/-- The SAME complete original scalar coefficient cell is the left map of its genuine marked square in the whole
original horn ladder. -/
theorem coneRootCoordinateSkeletonMarkedSquare {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    coneRootCoordinateSkeletonMarkedCornerMap j hj c ≫
        (coneRootCoordinateHornFiltration j hj).map (homOfLE (Nat.le_succ d)) =
      coneRootCoordinateScalarCell j hj c.simplex ≫ coneRootCoordinateSkeletonMarkedPrismMap j hj c :=
  Hom.ext (coneRootCoordinateSkeletonCornerMap_successor c)

/-- Every actual original marked successor stage map covers all its target marks through the unchanged initial horn
source. -/
theorem coneRootCoordinateHornFiltration_step_markingSurjective {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) (d : ℕ) :
    MarkingSurjective ((coneRootCoordinateHornFiltration j hj).map (homOfLE (Nat.le_succ d))) := by
  apply subcomplexFunctor_map_markingSurjective (coneRootCoordinateWholeAmbient j hj)
    (coneRootCoordinateHornStage n 0) _ (homOfLE (coneRootCoordinateHornStage_mono n (Nat.le_succ d)))
    (coneRootCoordinateHornStage_mono n (Nat.zero_le d))
  intro e he
  exact (congrArg (fun A => e ∈ A.obj (op ⦋1⦌)) (coneRootCoordinateHornStage_zero n)).to_iff.mpr
    (coneRootCoordinateWholeAmbient_marks_mem j hj hj' e he)

end SSet.Marked.CoherentWeight
