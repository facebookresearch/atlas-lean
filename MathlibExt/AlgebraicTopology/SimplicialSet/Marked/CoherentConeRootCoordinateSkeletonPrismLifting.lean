/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateSkeletonCellLifting
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Actual original coefficient lifts through the scalar coproduct and prism pushout

The original relative skeletal cells supply genuine coefficient lifts.
The actual interval tensor preserves their original native coproduct and
scalar pushout. The full unchanged upper-endpoint leg is retained using
the same native scalar pushout tensored with the original upper endpoint.
All original cell, boundary and successor maps remain literal.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq coefficientMarkedModelCategory

/-- Actual coefficient scalar lifts assemble over the original native coproduct, retaining its boundary, full upper
endpoint and original bottom map. -/
theorem coneRootCoordinateSkeletonCoproduct_lift {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) {X Y : Marked.{u}} (p : X ⟶ Y) (hp : fibrations Marked.{u} p)
    (top : (coneRootCoordinateHornFiltration j hj).obj d ⟶ X)
    (bottom : (coneRootCoordinateHornFiltration j hj).obj (d + 1) ⟶ Y)
    (sq : CommSq top ((coneRootCoordinateHornFiltration j hj).map (homOfLE (Nat.le_succ d))) p bottom) :
    ∃ L : (Δ[1] : SSet.{u}) ⊗
        SSet.relativeCellComplexOfMono.sigmaStdSimplex (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d ⟶ X.toSSet,
      ((Δ[1] : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.t (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) ≫
          (Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫ top.hom) =
        ((Δ[1] : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.l (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) ≫ L ∧
      L ≫ p.hom =
        ((Δ[1] : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.b (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) ≫
          Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n (d + 1)) ≫ bottom.hom ∧
      ((horn.{u} 1 (Fin.last 1)).ι ▷
          SSet.relativeCellComplexOfMono.sigmaStdSimplex (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) ≫ L =
        ((horn.{u} 1 (Fin.last 1) : SSet.{u}) ◁
          (SSet.relativeCellComplexOfMono.b (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d ≫
            (coneRootCoordinateScalarSkeleton n (d + 1)).ι)) ≫
          Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫ top.hom := by
  let I : SSet.{u} := Δ[1]
  let H : I.Subcomplex := horn.{u} 1 (Fin.last 1)
  let i := (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι
  let Cells := SSet.relativeCellComplexOfMono.Cell i d
  let a := Subcomplex.unionProd.ι₁ H (coneRootCoordinateScalarSkeleton n d) ≫ top.hom
  let e := Subcomplex.unionProd.ι₂ H (coneRootCoordinateScalarSkeleton n d) ≫ top.hom
  let b := Subcomplex.unionProd.ι₁ H (coneRootCoordinateScalarSkeleton n (d + 1)) ≫ bottom.hom
  have cells (c : Cells) := coneRootCoordinateSkeletonCell_fullLift j hj hj' p hp top bottom sq c
  choose l hwhole hright hboundary hendpoint using cells
  let cs : Cofan (fun _ : Cells => I ⊗ (Δ[d] : SSet.{u})) :=
    Cofan.mk (I ⊗ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d) (fun c => I ◁ c.ιSigmaStdSimplex)
  let hc : IsColimit cs :=
    isColimitOfHasCoproductOfPreservesColimit (tensorLeft I) (fun _ : Cells => (Δ[d] : SSet.{u}))
  let L : I ⊗ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d ⟶ X.toSSet :=
    hc.desc (Cofan.mk X.toSSet l)
  have hL (c : Cells) : (I ◁ c.ιSigmaStdSimplex) ≫ L = l c :=
    hc.fac (Cofan.mk X.toSSet l) (Discrete.mk c)
  let cb : Cofan (fun _ : Cells => I ⊗ (boundary.{u} d : SSet.{u})) :=
    Cofan.mk (I ⊗ SSet.relativeCellComplexOfMono.sigmaBoundary i d) (fun c => I ◁ c.ιSigmaBoundary)
  let hcb : IsColimit cb :=
    isColimitOfHasCoproductOfPreservesColimit (tensorLeft I) (fun _ : Cells => (boundary.{u} d : SSet.{u}))
  let ch : Cofan (fun _ : Cells => (H : SSet.{u}) ⊗ (Δ[d] : SSet.{u})) :=
    Cofan.mk ((H : SSet.{u}) ⊗ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d)
      (fun c => (H : SSet.{u}) ◁ c.ιSigmaStdSimplex)
  let hch : IsColimit ch :=
    isColimitOfHasCoproductOfPreservesColimit (tensorLeft (H : SSet.{u})) (fun _ : Cells => (Δ[d] : SSet.{u}))
  refine ⟨L, ?_, ?_, ?_⟩
  · change (I ◁ SSet.relativeCellComplexOfMono.t i d) ≫ a =
      (I ◁ SSet.relativeCellComplexOfMono.l i d) ≫ L
    apply hcb.hom_ext
    rintro ⟨c⟩
    have ht : (I ◁ c.ιSigmaBoundary) ≫ (I ◁ SSet.relativeCellComplexOfMono.t i d) =
        I ◁ coneRootCoordinateSkeletonBoundaryMap c := (whiskerLeft_comp I _ _).symm
    have hm : (I ◁ c.ιSigmaBoundary) ≫ (I ◁ SSet.relativeCellComplexOfMono.l i d) =
        (I ◁ (boundary.{u} d).ι) ≫ (I ◁ c.ιSigmaStdSimplex) :=
      ((whiskerLeft_comp I _ _).symm).trans
        ((congrArg (fun f => I ◁ f) c.ι_l).trans (whiskerLeft_comp I _ _))
    change (I ◁ c.ιSigmaBoundary) ≫ ((I ◁ SSet.relativeCellComplexOfMono.t i d) ≫ a) =
      (I ◁ c.ιSigmaBoundary) ≫ ((I ◁ SSet.relativeCellComplexOfMono.l i d) ≫ L)
    calc
      (I ◁ c.ιSigmaBoundary) ≫ ((I ◁ SSet.relativeCellComplexOfMono.t i d) ≫ a) =
          (I ◁ coneRootCoordinateSkeletonBoundaryMap c) ≫ a :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ a) ht)
      _ = (I ◁ (boundary.{u} d).ι) ≫ l c := (hboundary c).symm
      _ = (I ◁ (boundary.{u} d).ι) ≫ ((I ◁ c.ιSigmaStdSimplex) ≫ L) :=
        congrArg (fun f => (I ◁ (boundary.{u} d).ι) ≫ f) (hL c).symm
      _ = ((I ◁ (boundary.{u} d).ι) ≫ (I ◁ c.ιSigmaStdSimplex)) ≫ L := (Category.assoc _ _ _).symm
      _ = ((I ◁ c.ιSigmaBoundary) ≫ (I ◁ SSet.relativeCellComplexOfMono.l i d)) ≫ L :=
        congrArg (fun f => f ≫ L) hm.symm
      _ = (I ◁ c.ιSigmaBoundary) ≫ ((I ◁ SSet.relativeCellComplexOfMono.l i d) ≫ L) := Category.assoc _ _ _
  · change L ≫ p.hom = (I ◁ SSet.relativeCellComplexOfMono.b i d) ≫ b
    apply hc.hom_ext
    rintro ⟨c⟩
    have hr : l c ≫ p.hom = (I ◁ coneRootCoordinateSkeletonSuccessorMap c) ≫ b := by
      exact (hright c).trans ((Category.assoc _ _ _).trans
        (congrArg (fun f => f ≫ b) (id_tensorHom I (coneRootCoordinateSkeletonSuccessorMap c))))
    have hm : (I ◁ c.ιSigmaStdSimplex) ≫ (I ◁ SSet.relativeCellComplexOfMono.b i d) =
        I ◁ coneRootCoordinateSkeletonSuccessorMap c := (whiskerLeft_comp I _ _).symm
    change (I ◁ c.ιSigmaStdSimplex) ≫ (L ≫ p.hom) =
      (I ◁ c.ιSigmaStdSimplex) ≫ ((I ◁ SSet.relativeCellComplexOfMono.b i d) ≫ b)
    calc
      (I ◁ c.ιSigmaStdSimplex) ≫ (L ≫ p.hom) = l c ≫ p.hom :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ p.hom) (hL c))
      _ = (I ◁ coneRootCoordinateSkeletonSuccessorMap c) ≫ b := hr
      _ = ((I ◁ c.ιSigmaStdSimplex) ≫ (I ◁ SSet.relativeCellComplexOfMono.b i d)) ≫ b :=
        congrArg (fun f => f ≫ b) hm.symm
      _ = (I ◁ c.ιSigmaStdSimplex) ≫ ((I ◁ SSet.relativeCellComplexOfMono.b i d) ≫ b) := Category.assoc _ _ _
  · change (H.ι ▷ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d) ≫ L =
      ((H : SSet.{u}) ◁ (SSet.relativeCellComplexOfMono.b i d ≫
        (coneRootCoordinateScalarSkeleton n (d + 1)).ι)) ≫ e
    apply hch.hom_ext
    rintro ⟨c⟩
    have hx : ((H : SSet.{u}) ◁ c.ιSigmaStdSimplex) ≫
        (H.ι ▷ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d) =
      (H.ι ▷ (Δ[d] : SSet.{u})) ≫ (I ◁ c.ιSigmaStdSimplex) := whisker_exchange _ _
    have hm : c.ιSigmaStdSimplex ≫ (SSet.relativeCellComplexOfMono.b i d ≫
        (coneRootCoordinateScalarSkeleton n (d + 1)).ι) = c.map := c.ι_b_ι
    change ((H : SSet.{u}) ◁ c.ιSigmaStdSimplex) ≫
        ((H.ι ▷ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d) ≫ L) =
      ((H : SSet.{u}) ◁ c.ιSigmaStdSimplex) ≫
        (((H : SSet.{u}) ◁ (SSet.relativeCellComplexOfMono.b i d ≫
          (coneRootCoordinateScalarSkeleton n (d + 1)).ι)) ≫ e)
    calc
      ((H : SSet.{u}) ◁ c.ιSigmaStdSimplex) ≫
          ((H.ι ▷ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d) ≫ L) =
        (H.ι ▷ (Δ[d] : SSet.{u})) ≫ ((I ◁ c.ιSigmaStdSimplex) ≫ L) :=
          (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ L) hx).trans (Category.assoc _ _ _))
      _ = (H.ι ▷ (Δ[d] : SSet.{u})) ≫ l c := congrArg (fun f => (H.ι ▷ (Δ[d] : SSet.{u})) ≫ f) (hL c)
      _ = ((H : SSet.{u}) ◁ c.map) ≫ e := hendpoint c
      _ = ((H : SSet.{u}) ◁ (c.ιSigmaStdSimplex ≫
          (SSet.relativeCellComplexOfMono.b i d ≫ (coneRootCoordinateScalarSkeleton n (d + 1)).ι))) ≫ e :=
        congrArg (fun f => ((H : SSet.{u}) ◁ f) ≫ e) hm.symm
      _ = ((H : SSet.{u}) ◁ c.ιSigmaStdSimplex) ≫
          (((H : SSet.{u}) ◁ (SSet.relativeCellComplexOfMono.b i d ≫
            (coneRootCoordinateScalarSkeleton n (d + 1)).ι)) ≫ e) :=
        (congrArg (fun f => f ≫ e) (whiskerLeft_comp (H : SSet.{u}) _ _)).trans (Category.assoc _ _ _)

/-- The SAME original scalar pushout assembles a whole interval-prism lift against every actual coefficient
fibration, retaining the unchanged whole upper endpoint and both original skeletal maps. -/
theorem coneRootCoordinateSkeletonPrism_lift {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) {X Y : Marked.{u}} (p : X ⟶ Y) (hp : fibrations Marked.{u} p)
    (top : (coneRootCoordinateHornFiltration j hj).obj d ⟶ X)
    (bottom : (coneRootCoordinateHornFiltration j hj).obj (d + 1) ⟶ Y)
    (sq : CommSq top ((coneRootCoordinateHornFiltration j hj).map (homOfLE (Nat.le_succ d))) p bottom) :
    ∃ D : (Δ[1] : SSet.{u}) ⊗ (coneRootCoordinateScalarSkeleton n (d + 1) : SSet.{u}) ⟶ X.toSSet,
      ((Δ[1] : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.r (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι d) ≫ D =
        Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫ top.hom ∧
      D ≫ p.hom =
        Subcomplex.unionProd.ι₁ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n (d + 1)) ≫ bottom.hom ∧
      ((horn.{u} 1 (Fin.last 1)).ι ▷ (coneRootCoordinateScalarSkeleton n (d + 1) : SSet.{u})) ≫ D =
        ((horn.{u} 1 (Fin.last 1) : SSet.{u}) ◁ (coneRootCoordinateScalarSkeleton n (d + 1)).ι) ≫
          Subcomplex.unionProd.ι₂ (horn.{u} 1 (Fin.last 1)) (coneRootCoordinateScalarSkeleton n d) ≫ top.hom := by
  let I : SSet.{u} := Δ[1]
  let H : I.Subcomplex := horn.{u} 1 (Fin.last 1)
  let i := (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι
  let a := Subcomplex.unionProd.ι₁ H (coneRootCoordinateScalarSkeleton n d) ≫ top.hom
  let e := Subcomplex.unionProd.ι₂ H (coneRootCoordinateScalarSkeleton n d) ≫ top.hom
  let b := Subcomplex.unionProd.ι₁ H (coneRootCoordinateScalarSkeleton n (d + 1)) ≫ bottom.hom
  obtain ⟨L, hbc, hLp, hLe⟩ := coneRootCoordinateSkeletonCoproduct_lift j hj hj' p hp top bottom sq
  change (I ◁ SSet.relativeCellComplexOfMono.t i d) ≫ a = (I ◁ SSet.relativeCellComplexOfMono.l i d) ≫ L at hbc
  change L ≫ p.hom = (I ◁ SSet.relativeCellComplexOfMono.b i d) ≫ b at hLp
  change (H.ι ▷ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d) ≫ L =
    ((H : SSet.{u}) ◁ (SSet.relativeCellComplexOfMono.b i d ≫
      (coneRootCoordinateScalarSkeleton n (d + 1)).ι)) ≫ e at hLe
  let hpI : IsPushout (I ◁ SSet.relativeCellComplexOfMono.t i d)
      (I ◁ SSet.relativeCellComplexOfMono.l i d) (I ◁ SSet.relativeCellComplexOfMono.r i d)
      (I ◁ SSet.relativeCellComplexOfMono.b i d) :=
    (SSet.relativeCellComplexOfMono.isPushout i d).map (tensorLeft I)
  let D : I ⊗ (coneRootCoordinateScalarSkeleton n (d + 1) : SSet.{u}) ⟶ X.toSSet := hpI.desc a L hbc
  have hDa : (I ◁ SSet.relativeCellComplexOfMono.r i d) ≫ D = a := hpI.inl_desc a L hbc
  have hDL : (I ◁ SSet.relativeCellComplexOfMono.b i d) ≫ D = L := hpI.inr_desc a L hbc
  have hsq : top.hom ≫ p.hom =
      Subcomplex.homOfLE (coneRootCoordinateHornStage_mono n (Nat.le_succ d)) ≫ bottom.hom :=
    congrArg Hom.hom sq.w
  have hDp : D ≫ p.hom = b := by
    apply hpI.hom_ext
    · have h₁ : a ≫ p.hom =
          Subcomplex.unionProd.ι₁ H (coneRootCoordinateScalarSkeleton n d) ≫
            (Subcomplex.homOfLE (coneRootCoordinateHornStage_mono n (Nat.le_succ d)) ≫ bottom.hom) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun f => Subcomplex.unionProd.ι₁ H (coneRootCoordinateScalarSkeleton n d) ≫ f) hsq)
      have h₂ : Subcomplex.unionProd.ι₁ H (coneRootCoordinateScalarSkeleton n d) ≫
          (Subcomplex.homOfLE (coneRootCoordinateHornStage_mono n (Nat.le_succ d)) ≫ bottom.hom) =
          (I ◁ SSet.relativeCellComplexOfMono.r i d) ≫ b :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ bottom.hom) (coneRootCoordinateHornStage_interval_successor n d).symm).trans
            (Category.assoc _ _ _))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ p.hom) hDa).trans (h₁.trans h₂))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ p.hom) hDL).trans hLp)
  have hri : SSet.relativeCellComplexOfMono.r i d ≫ (coneRootCoordinateScalarSkeleton n (d + 1)).ι =
      (coneRootCoordinateScalarSkeleton n d).ι :=
    Subcomplex.homOfLE_ι ((SSet.skeletonOfMono i).monotone (Nat.le_succ d))
  let hpH : IsPushout ((H : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.t i d)
      ((H : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.l i d)
      ((H : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.r i d)
      ((H : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.b i d) :=
    (SSet.relativeCellComplexOfMono.isPushout i d).map (tensorLeft (H : SSet.{u}))
  have hDe : (H.ι ▷ (coneRootCoordinateScalarSkeleton n (d + 1) : SSet.{u})) ≫ D =
      ((H : SSet.{u}) ◁ (coneRootCoordinateScalarSkeleton n (d + 1)).ι) ≫ e := by
    apply hpH.hom_ext
    · have hx : ((H : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.r i d) ≫
          (H.ι ▷ (coneRootCoordinateScalarSkeleton n (d + 1) : SSet.{u})) =
        (H.ι ▷ (coneRootCoordinateScalarSkeleton n d : SSet.{u})) ≫
          (I ◁ SSet.relativeCellComplexOfMono.r i d) := whisker_exchange _ _
      have h₁ : (H.ι ▷ (coneRootCoordinateScalarSkeleton n d : SSet.{u})) ≫ a =
          ((H : SSet.{u}) ◁ (coneRootCoordinateScalarSkeleton n d).ι) ≫ e :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ top.hom)
            (Subcomplex.unionProd.isPushout H (coneRootCoordinateScalarSkeleton n d)).w).trans
              (Category.assoc _ _ _))
      have h₂ : ((H : SSet.{u}) ◁ (coneRootCoordinateScalarSkeleton n d).ι) ≫ e =
          ((H : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.r i d) ≫
            (((H : SSet.{u}) ◁ (coneRootCoordinateScalarSkeleton n (d + 1)).ι) ≫ e) :=
        (congrArg (fun f => ((H : SSet.{u}) ◁ f) ≫ e) hri.symm).trans
          ((congrArg (fun f => f ≫ e) (whiskerLeft_comp (H : SSet.{u}) _ _)).trans (Category.assoc _ _ _))
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ D) hx).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f => (H.ι ▷ (coneRootCoordinateScalarSkeleton n d : SSet.{u})) ≫ f) hDa).trans
              (h₁.trans h₂))))
    · have hx : ((H : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.b i d) ≫
          (H.ι ▷ (coneRootCoordinateScalarSkeleton n (d + 1) : SSet.{u})) =
        (H.ι ▷ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d) ≫
          (I ◁ SSet.relativeCellComplexOfMono.b i d) := whisker_exchange _ _
      calc
        ((H : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.b i d) ≫
            ((H.ι ▷ (coneRootCoordinateScalarSkeleton n (d + 1) : SSet.{u})) ≫ D) =
          (H.ι ▷ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d) ≫
            ((I ◁ SSet.relativeCellComplexOfMono.b i d) ≫ D) :=
          (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ D) hx).trans (Category.assoc _ _ _))
        _ = (H.ι ▷ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d) ≫ L :=
          congrArg (fun f => (H.ι ▷ SSet.relativeCellComplexOfMono.sigmaStdSimplex i d) ≫ f) hDL
        _ = ((H : SSet.{u}) ◁ (SSet.relativeCellComplexOfMono.b i d ≫
            (coneRootCoordinateScalarSkeleton n (d + 1)).ι)) ≫ e := hLe
        _ = ((H : SSet.{u}) ◁ SSet.relativeCellComplexOfMono.b i d) ≫
            (((H : SSet.{u}) ◁ (coneRootCoordinateScalarSkeleton n (d + 1)).ι) ≫ e) :=
          (congrArg (fun f => f ≫ e) (whiskerLeft_comp (H : SSet.{u}) _ _)).trans (Category.assoc _ _ _)
  exact ⟨D, hDa, hDp, hDe⟩

end SSet.Marked.CoherentWeight
