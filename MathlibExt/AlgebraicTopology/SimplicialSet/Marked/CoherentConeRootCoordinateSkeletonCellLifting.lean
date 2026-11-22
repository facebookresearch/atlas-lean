/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateSkeletonCorners

/-!
# Actual coefficient lifts of the original scalar cells in the whole horn ladder

Each unchanged native scalar square has its already-proved actual
coefficient trivial cofibration as its left map. The full coefficient
weak factorization system therefore supplies a genuine marked lift
against an actual coefficient fibration. Its entire original underlying
prism, boundary and successor maps remain unchanged.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq coefficientMarkedModelCategory

/-- The actual original scalar cell supplies a full marked lift in every original whole skeletal-stage square
against an actual coefficient fibration. -/
theorem coneRootCoordinateSkeletonCell_markedLift {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) {X Y : Marked.{u}} (p : X ⟶ Y) (hp : fibrations Marked.{u} p)
    (top : (coneRootCoordinateHornFiltration j hj).obj d ⟶ X)
    (bottom : (coneRootCoordinateHornFiltration j hj).obj (d + 1) ⟶ Y)
    (sq : CommSq top ((coneRootCoordinateHornFiltration j hj).map (homOfLE (Nat.le_succ d))) p bottom)
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    ∃ l : coneRootCoordinateScalarAmbient j hj c.simplex ⟶ X,
      coneRootCoordinateScalarCell j hj c.simplex ≫ l = coneRootCoordinateSkeletonMarkedCornerMap j hj c ≫ top ∧
        l ≫ p = coneRootCoordinateSkeletonMarkedPrismMap j hj c ≫ bottom := by
  let hlp : HasLiftingProperty (coneRootCoordinateScalarCell j hj c.simplex) p :=
    hasLiftingProperty_of_wfs _ _ (coneRootCoordinateSkeletonCell_trivialCofibration j hj hj' c) hp
  have hs : CommSq (coneRootCoordinateSkeletonMarkedCornerMap j hj c ≫ top)
      (coneRootCoordinateScalarCell j hj c.simplex) p
      (coneRootCoordinateSkeletonMarkedPrismMap j hj c ≫ bottom) := CommSq.mk (by
    calc
      (coneRootCoordinateSkeletonMarkedCornerMap j hj c ≫ top) ≫ p =
          coneRootCoordinateSkeletonMarkedCornerMap j hj c ≫ (top ≫ p) := Category.assoc _ _ _
      _ = coneRootCoordinateSkeletonMarkedCornerMap j hj c ≫
          (((coneRootCoordinateHornFiltration j hj).map (homOfLE (Nat.le_succ d))) ≫ bottom) :=
        congrArg (fun f => coneRootCoordinateSkeletonMarkedCornerMap j hj c ≫ f) sq.w
      _ = (coneRootCoordinateSkeletonMarkedCornerMap j hj c ≫
          (coneRootCoordinateHornFiltration j hj).map (homOfLE (Nat.le_succ d))) ≫ bottom :=
        (Category.assoc _ _ _).symm
      _ = (coneRootCoordinateScalarCell j hj c.simplex ≫ coneRootCoordinateSkeletonMarkedPrismMap j hj c) ≫ bottom :=
        congrArg (fun f => f ≫ bottom) (coneRootCoordinateSkeletonMarkedSquare j hj c)
      _ = coneRootCoordinateScalarCell j hj c.simplex ≫
          (coneRootCoordinateSkeletonMarkedPrismMap j hj c ≫ bottom) := Category.assoc _ _ _)
  obtain ⟨l, hl, hr⟩ := hlp.sq_hasLift hs
  exact ⟨l, hl, hr⟩

/-- The genuine marked scalar lift retains the SAME entire original underlying prism and both original attaching
equations. -/
theorem coneRootCoordinateSkeletonCell_underlyingLift {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) {X Y : Marked.{u}} (p : X ⟶ Y) (hp : fibrations Marked.{u} p)
    (top : (coneRootCoordinateHornFiltration j hj).obj d ⟶ X)
    (bottom : (coneRootCoordinateHornFiltration j hj).obj (d + 1) ⟶ Y)
    (sq : CommSq top ((coneRootCoordinateHornFiltration j hj).map (homOfLE (Nat.le_succ d))) p bottom)
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    ∃ l : (Δ[1] : SSet.{u}) ⊗ Δ[d] ⟶ X.toSSet,
      (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι ≫ l =
        coneRootCoordinateSkeletonCornerMap c ≫ top.hom ∧
      l ≫ p.hom = coneRootCoordinateSkeletonPrismMap c ≫ bottom.hom := by
  obtain ⟨l, hl, hr⟩ := coneRootCoordinateSkeletonCell_markedLift j hj hj' p hp top bottom sq c
  exact ⟨l.hom, congrArg Hom.hom hl, congrArg Hom.hom hr⟩

/-- The genuine actual scalar lift retains both original boundary and whole-endpoint legs together with its full
original prism square. -/
theorem coneRootCoordinateSkeletonCell_fullLift {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) {X Y : Marked.{u}} (p : X ⟶ Y) (hp : fibrations Marked.{u} p)
    (top : (coneRootCoordinateHornFiltration j hj).obj d ⟶ X)
    (bottom : (coneRootCoordinateHornFiltration j hj).obj (d + 1) ⟶ Y)
    (sq : CommSq top ((coneRootCoordinateHornFiltration j hj).map (homOfLE (Nat.le_succ d))) p bottom)
    (c : SSet.relativeCellComplexOfMono.Cell (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) :
    ∃ l : (Δ[1] : SSet.{u}) ⊗ Δ[d] ⟶ X.toSSet,
      (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι ≫ l =
        coneRootCoordinateSkeletonCornerMap c ≫ top.hom ∧
      l ≫ p.hom = coneRootCoordinateSkeletonPrismMap c ≫ bottom.hom ∧
      ((Δ[1] : SSet.{u}) ◁ (boundary.{u} d).ι) ≫ l =
        ((Δ[1] : SSet.{u}) ◁ coneRootCoordinateSkeletonBoundaryMap c) ≫
          Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫ top.hom ∧
      ((horn.{u} 1 (Fin.last 1)).ι ▷ (Δ[d] : SSet.{u})) ≫ l =
        ((horn.{u} 1 (Fin.last 1) : SSet.{u}) ◁ c.map) ≫
          Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫ top.hom := by
  obtain ⟨l, hl, hr⟩ := coneRootCoordinateSkeletonCell_underlyingLift j hj hj' p hp top bottom sq c
  refine ⟨l, hl, hr, ?_, ?_⟩
  · calc
      ((Δ[1] : SSet.{u}) ◁ (boundary.{u} d).ι) ≫ l =
          (Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫
            (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι) ≫ l :=
        congrArg (fun f => f ≫ l) (Subcomplex.unionProd.ι₁_ι _ _).symm
      _ = Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫
          ((Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι ≫ l) := Category.assoc _ _ _
      _ = Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫
          (coneRootCoordinateSkeletonCornerMap c ≫ top.hom) :=
        congrArg (fun f => Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫ f) hl
      _ = (Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫
          coneRootCoordinateSkeletonCornerMap c) ≫ top.hom := (Category.assoc _ _ _).symm
      _ = ((𝟙 (Δ[1] : SSet.{u}) ⊗ₘ coneRootCoordinateSkeletonBoundaryMap c) ≫
          Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d)) ≫ top.hom :=
        congrArg (fun f => f ≫ top.hom) (coneRootCoordinateSkeletonCornerMap_boundary c)
      _ = ((Δ[1] : SSet.{u}) ◁ coneRootCoordinateSkeletonBoundaryMap c) ≫
          Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫ top.hom :=
        (Category.assoc _ _ _).trans (congrArg (fun f => f ≫
          (Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫ top.hom))
            (id_tensorHom _ _))
  · calc
      ((horn.{u} 1 (Fin.last 1)).ι ▷ (Δ[d] : SSet.{u})) ≫ l =
          (Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫
            (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι) ≫ l :=
        congrArg (fun f => f ≫ l) (Subcomplex.unionProd.ι₂_ι _ _).symm
      _ = Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫
          ((Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (boundary.{u} d)).ι ≫ l) := Category.assoc _ _ _
      _ = Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫
          (coneRootCoordinateSkeletonCornerMap c ≫ top.hom) :=
        congrArg (fun f => Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫ f) hl
      _ = (Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (boundary.{u} d) ≫
          coneRootCoordinateSkeletonCornerMap c) ≫ top.hom := (Category.assoc _ _ _).symm
      _ = ((𝟙 (horn.{u} 1 (Fin.last 1) : SSet.{u}) ⊗ₘ c.map) ≫
          Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d)) ≫ top.hom :=
        congrArg (fun f => f ≫ top.hom) (coneRootCoordinateSkeletonCornerMap_endpoint c)
      _ = ((horn.{u} 1 (Fin.last 1) : SSet.{u}) ◁ c.map) ≫
          Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫ top.hom :=
        (Category.assoc _ _ _).trans (congrArg (fun f => f ≫
          (Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫ top.hom))
            (id_tensorHom _ _))

/-- The whole original interval/scalar successor leg commutes with the SAME actual full horn-stage inclusion. -/
theorem coneRootCoordinateHornStage_interval_successor (n d : ℕ) :
    ((Δ[1] : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.r (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) ≫
        Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n (d + 1)) =
      Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫
        Subcomplex.homOfLE (coneRootCoordinateHornStage_mono n (Nat.le_succ d)) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro e
  apply Subtype.ext
  rfl

/-- The retained whole original upper endpoint has precisely its SAME full map in every original skeletal successor. -/
theorem coneRootCoordinateHornStage_endpoint_successor (n d : ℕ) :
    Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫
        Subcomplex.homOfLE (coneRootCoordinateHornStage_mono n (Nat.le_succ d)) =
      Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n (d + 1)) := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro e
  apply Subtype.ext
  rfl

end SSet.Marked.CoherentWeight
