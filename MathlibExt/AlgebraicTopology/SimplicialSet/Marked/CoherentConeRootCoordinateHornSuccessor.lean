/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateSkeletonPrismLifting

/-!
# Genuine coefficient weakness of the original whole marked horn successors

The original scalar lifts assemble through their actual native coproduct
and scalar pushout. The unchanged upper endpoint then gives the genuine
whole successor diagonal through the original endpoint/scalar union
pushout. Original marking coverage retains that same entire diagonal as
a marked map. The full actual coefficient WFS proves each same original
whole marked skeletal successor a trivial cofibration.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq coefficientMarkedModelCategory

/-- Every SAME original whole marked root-horn skeletal successor is a genuine trivial cofibration in the actual
coefficient model, through its original scalar coproduct, scalar pushout and whole-endpoint pushout. -/
theorem coneRootCoordinateHornFiltration_step_trivialCofibration {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (hj' : j < Fin.last (n + 1)) (d : ℕ) :
    trivialCofibrations Marked.{u}
      ((coneRootCoordinateHornFiltration j hj).map (homOfLE (Nat.le_succ d))) := by
  rw [← llp_eq_of_wfs (trivialCofibrations Marked.{u}) (fibrations Marked.{u})]
  intro X Y p hp
  refine ⟨fun {top bottom} sq => ?_⟩
  let I : SSet.{u} := Δ[1]
  let H : I.Subcomplex := horn.{u} 1 (Fin.last 1)
  let i := (coneCoordinateBoundary (⊥ : Vertex.{u} n)).ι
  let g := Subcomplex.homOfLE (coneRootCoordinateHornStage_mono n (Nat.le_succ d))
  let e := Subcomplex.unionProd.ι₂ H (coneRootCoordinateScalarSkeleton n d) ≫ top.hom
  obtain ⟨D, hDa, hDp, hDe⟩ := coneRootCoordinateSkeletonPrism_lift j hj hj' p hp top bottom sq
  change (I ◁ SSet.relativeCellComplexOfMono.r i d) ≫ D =
    Subcomplex.unionProd.ι₁ H (coneRootCoordinateScalarSkeleton n d) ≫ top.hom at hDa
  change D ≫ p.hom = Subcomplex.unionProd.ι₁ H (coneRootCoordinateScalarSkeleton n (d + 1)) ≫ bottom.hom at hDp
  change (H.ι ▷ (coneRootCoordinateScalarSkeleton n (d + 1) : SSet.{u})) ≫ D =
    ((H : SSet.{u}) ◁ (coneRootCoordinateScalarSkeleton n (d + 1)).ι) ≫ e at hDe
  let hpNext := Subcomplex.unionProd.isPushout H (coneRootCoordinateScalarSkeleton n (d + 1))
  let hpOld := Subcomplex.unionProd.isPushout H (coneRootCoordinateScalarSkeleton n d)
  let G : (coneRootCoordinateHornStage n (d + 1) : SSet.{u}) ⟶ X.toSSet := hpNext.desc D e hDe
  have hG₁ : Subcomplex.unionProd.ι₁ H (coneRootCoordinateScalarSkeleton n (d + 1)) ≫ G = D :=
    hpNext.inl_desc D e hDe
  have hG₂ : Subcomplex.unionProd.ι₂ H (coneRootCoordinateScalarSkeleton n (d + 1)) ≫ G = e :=
    hpNext.inr_desc D e hDe
  have hsq : top.hom ≫ p.hom = g ≫ bottom.hom := congrArg Hom.hom sq.w
  have hGt : g ≫ G = top.hom := by
    apply hpOld.hom_ext
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ G) (coneRootCoordinateHornStage_interval_successor n d).symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun f => (I ◁ SSet.relativeCellComplexOfMono.r i d) ≫ f) hG₁).trans hDa)))
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ G) (coneRootCoordinateHornStage_endpoint_successor n d)).trans hG₂)
  have hGp : G ≫ p.hom = bottom.hom := by
    apply hpNext.hom_ext
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ p.hom) hG₁).trans hDp)
    · have he : e ≫ p.hom =
          Subcomplex.unionProd.ι₂ H (coneRootCoordinateScalarSkeleton n (d + 1)) ≫ bottom.hom :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun f => Subcomplex.unionProd.ι₂ H (coneRootCoordinateScalarSkeleton n d) ≫ f) hsq).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun f => f ≫ bottom.hom) (coneRootCoordinateHornStage_endpoint_successor n d))))
      exact (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ p.hom) hG₂).trans he)
  have hcov := coneRootCoordinateHornFiltration_step_markingSurjective j hj hj' d
  let diagonal : (coneRootCoordinateHornFiltration j hj).obj (d + 1) ⟶ X :=
    { hom := G
      preserve {z} hz := by
        obtain ⟨a, ha, hae⟩ := hcov z hz
        have hGa : G.app (op ⦋1⦌) z = top.hom.app (op ⦋1⦌) a :=
          (congrArg (G.app (op ⦋1⦌)) hae).symm.trans
            (ConcreteCategory.congr_hom (congr_app hGt (op ⦋1⦌)) a)
        exact hGa.symm ▸ top.preserve ha }
  exact CommSq.HasLift.mk' ⟨diagonal, Hom.ext hGt, Hom.ext hGp⟩

end SSet.Marked.CoherentWeight
