/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereOneBoundaryComplement
public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.OnePointAction
public import MathlibExt.Topology.Category.TopCat.PointQuotientOnePoint

/-!
# The original native one-sphere and the Euclidean representation 1-sphere

The original realized one-simplex boundary quotient is identified with the
original one-point compactification of the lifted Euclidean line. The actual
collapsed basepoint is preserved. No sphere equivalence is supplied as input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Set Topology
open scoped Simplicial

namespace CategoryTheory.Spectra

/-- The boundary inclusion used in the original one-dimensional sphere presentation. -/
abbrev originalBoundary := sphereOneBoundaryArrow.{u, v}.hom
/-- The terminal map collapsing the original sphere boundary to the CGWH point. -/
abbrev originalCollapse : sphereOneBoundaryArrow.{u, v}.left ⟶ CGWH.point.{u, v} :=
  CGWH.point_isTerminal.from _

private theorem originalBoundary_nonempty : Nonempty sphereOneBoundaryArrow.{u, v}.left := by
  let z : SSet.toCGWH.{u, v}.obj (Δ[0] : SSet.{v}) :=
    (SSet.toCGWHOfFinite_stdSimplex_zero_iso_point.{u, v}).inv PUnit.unit
  exact ⟨SSet.toCGWH.{u, v}.map (SSet.boundary.ι (0 : Fin 2)) z⟩

/-- The topological isomorphism identifying the underlying CGWH point with a singleton. -/
def originalRawPointIso : TopCat.of PUnit.{v + 1} ≅ CGWH.cgwhToTop.obj CGWH.point.{u, v} :=
  TopCat.isoOfHomeo
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }

/-- The isomorphism from the original point quotient to its boundary-collapse pushout. -/
def originalRawQuotientIso :
    TopCat.pointQuotient (Arrow.mk (CGWH.cgwhToTop.map originalBoundary.{u, v})) ≅
      (pushout (CGWH.cgwhToTop.map originalBoundary.{u, v})
        (CGWH.cgwhToTop.map originalCollapse.{u, v}) : TopCat.{v}) := by
  let i : CGWH.cgwhToTop.obj sphereOneBoundaryArrow.{u, v}.left ⟶
      CGWH.cgwhToTop.obj sphereOneBoundaryArrow.{u, v}.right :=
    CGWH.cgwhToTop.map originalBoundary.{u, v}
  let c : CGWH.cgwhToTop.obj sphereOneBoundaryArrow.{u, v}.left ⟶
      CGWH.cgwhToTop.obj CGWH.point.{u, v} := CGWH.cgwhToTop.map originalCollapse.{u, v}
  let q := TopCat.isTerminalPUnit.from (CGWH.cgwhToTop.obj sphereOneBoundaryArrow.{u, v}.left)
  let _ : IsIso originalRawPointIso.{u, v}.hom := inferInstance
  exact asIso (pushout.map i q i c (𝟙 _) originalRawPointIso.{u, v}.hom (𝟙 _)
    (by simp) (by
      apply ConcreteCategory.hom_ext
      intro x
      change @Eq PUnit _ _
      exact Subsingleton.elim _ _))

/-- The original boundary collapse in TopCat is the actual point quotient. -/
def sphereOneRawQuotientHomeomorph :
    OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin 1))) ≃ₜ
      (pushout (CGWH.cgwhToTop.map originalBoundary.{u, v})
        (CGWH.cgwhToTop.map originalCollapse.{u, v}) : TopCat.{v}) := by
  let _ : CompactSpace TopCat.I.{v} := TopCat.I.homeomorph.symm.compactSpace
  let _ : T2Space TopCat.I.{v} := TopCat.I.homeomorph.symm.t2Space
  let _ : Nonempty sphereOneBoundaryArrow.{u, v}.left := by exact originalBoundary_nonempty.{u, v}
  let _ : CompactSpace sphereOneBoundaryArrow.{u, v}.right :=
    sphereOneIntervalHomeomorph.{u, v}.symm.compactSpace
  let _ : T2Space sphereOneBoundaryArrow.{u, v}.right :=
    sphereOneIntervalHomeomorph.{u, v}.symm.t2Space
  let f : Arrow TopCat.{v} := Arrow.mk (CGWH.cgwhToTop.map originalBoundary.{u, v})
  let _ : Nonempty f.left := by exact originalBoundary_nonempty.{u, v}
  let _ : CompactSpace f.right := sphereOneIntervalHomeomorph.{u, v}.symm.compactSpace
  let _ : T2Space f.right := sphereOneIntervalHomeomorph.{u, v}.symm.t2Space
  let e : OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin 1))) ≃ₜ TopCat.pointQuotient f :=
    TopCat.onePointHomeomorphPointQuotient
    (f := f) sphereOneBoundaryArrow_closedEmbedding.{u, v}.isClosed_range
      sphereOneBoundaryComplement.{u, v}
  exact e.trans (TopCat.homeoOfIso originalRawQuotientIso.{u, v})

/-- The native closed-pushout comparison yields the whole original one-sphere carrier. -/
def sphereOneCarrierHomeomorph :
    OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin 1))) ≃ₜ
      PointedCGWH.sphereOne.{u, v}.right :=
  sphereOneRawQuotientHomeomorph.{u, v}.trans
    (TopCat.homeoOfIso (CGWH.pushoutClosedComparisonIso originalBoundary.{u, v}
      originalCollapse.{u, v} sphereOneBoundaryArrow_closedEmbedding.{u, v}))

/-- The constructed homeomorphism preserves the original collapsed basepoint. -/
theorem sphereOneCarrierHomeomorph_infty :
    sphereOneCarrierHomeomorph.{u, v} OnePoint.infty =
      PointedCGWH.sphereOne.{u, v}.hom PUnit.unit := by
  change (CGWH.pushoutClosedComparisonIso originalBoundary.{u, v} originalCollapse.{u, v}
    sphereOneBoundaryArrow_closedEmbedding.{u, v}).hom
      (sphereOneRawQuotientHomeomorph.{u, v} OnePoint.infty) = _
  have hPoint : sphereOneRawQuotientHomeomorph.{u, v} OnePoint.infty =
      pushout.inr (CGWH.cgwhToTop.map originalBoundary.{u, v})
        (CGWH.cgwhToTop.map originalCollapse.{u, v}) PUnit.unit := by
    let _ : CompactSpace TopCat.I.{v} := TopCat.I.homeomorph.symm.compactSpace
    let _ : T2Space TopCat.I.{v} := TopCat.I.homeomorph.symm.t2Space
    let _ : Nonempty (Arrow.mk (CGWH.cgwhToTop.map originalBoundary.{u, v})).left :=
      originalBoundary_nonempty.{u, v}
    let _ : CompactSpace (Arrow.mk (CGWH.cgwhToTop.map originalBoundary.{u, v})).right :=
      sphereOneIntervalHomeomorph.{u, v}.symm.compactSpace
    let _ : T2Space (Arrow.mk (CGWH.cgwhToTop.map originalBoundary.{u, v})).right :=
      sphereOneIntervalHomeomorph.{u, v}.symm.t2Space
    unfold sphereOneRawQuotientHomeomorph
    rw [Homeomorph.trans_apply]
    have hSeed : (TopCat.onePointHomeomorphPointQuotient
      (f := Arrow.mk (CGWH.cgwhToTop.map originalBoundary.{u, v}))
      sphereOneBoundaryArrow_closedEmbedding.{u, v}.isClosed_range
      sphereOneBoundaryComplement.{u, v}) OnePoint.infty =
        TopCat.pointQuotientPoint
          (Arrow.mk (CGWH.cgwhToTop.map originalBoundary.{u, v})) PUnit.unit :=
      TopCat.onePointHomeomorphPointQuotient_apply_infty _ _
    rw [hSeed]
    let i := CGWH.cgwhToTop.map originalBoundary.{u, v}
    let c := CGWH.cgwhToTop.map originalCollapse.{u, v}
    let q := TopCat.isTerminalPUnit.from
      (CGWH.cgwhToTop.obj sphereOneBoundaryArrow.{u, v}.left)
    let j : TopCat.of PUnit.{v + 1} ⟶ TopCat.pointQuotient (Arrow.mk i) :=
      pushout.inr i q
    change originalRawQuotientIso.{u, v}.hom
      (j PUnit.unit) = _
    have h : j ≫ originalRawQuotientIso.{u, v}.hom =
        originalRawPointIso.{u, v}.hom ≫
        pushout.inr i c := by
      exact pushout.inr_desc _ _ _
    exact ConcreteCategory.congr_hom h PUnit.unit
  rw [hPoint]
  exact ConcreteCategory.congr_hom
    (CGWH.pushoutClosedComparisonIso_hom_inr originalBoundary.{u, v} originalCollapse.{u, v}
      sphereOneBoundaryArrow_closedEmbedding.{u, v}) PUnit.unit

/-- The original compactification is identified with the original pointed native one-sphere. -/
def orthogonalOneSphereIsoSphereOne :
    PointedCGWH.orthogonalSphere.{u, v} 1 ≅ PointedCGWH.sphereOne.{u, v} := by
  let eLift := Homeomorph.onePointCongr
    (Homeomorph.ulift (X := EuclideanSpace ℝ (Fin 1)))
  let eSphere := onePointEquivSphereOfFinrankEq
    (V := EuclideanSpace ℝ (Fin 1)) (ι := Fin 2) (by simp)
  let hCG : UCompactlyGeneratedSpace.{u}
      (OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin 1)))) := by
    let _ : SequentialSpace (OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin 1)))) :=
      (eLift.trans eSphere).symm.isQuotientMap.sequentialSpace
    infer_instance
  let _ : UCompactlyGeneratedSpace.{u}
      (OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin 1)))) := hCG
  let h := CompactlyGenerated.coreflectionCounitHomeoData.{u, v}
    (OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin 1))))
  let e : (PointedCGWH.orthogonalSphere.{u, v} 1).right ≃ₜ
      PointedCGWH.sphereOne.{u, v}.right := by
    change TopCat.toCompactlyGenerated.{u, v}.obj
      (TopCat.of (OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin 1))))) ≃ₜ _
    exact h.1.trans sphereOneCarrierHomeomorph
  exact Under.isoMk (CGWH.isoOfHomeo e) (by
    apply ConcreteCategory.hom_ext
    intro z
    change sphereOneCarrierHomeomorph.{u, v} (h.1 OnePoint.infty) =
      PointedCGWH.sphereOne.{u, v}.hom z
    have hh : h.1 (show (TopCat.toCompactlyGenerated.{u, v}.obj
      (TopCat.of (OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin 1)))))) from
        OnePoint.infty) = OnePoint.infty := h.2 _
    have hz : z = (PUnit.unit : CGWH.point.{u, v}) := by
      change @Eq PUnit _ _
      exact Subsingleton.elim _ _
    exact (congrArg sphereOneCarrierHomeomorph.{u, v} hh).trans
      (sphereOneCarrierHomeomorph_infty.trans
        (congrArg PointedCGWH.sphereOne.{u, v}.hom hz.symm)))

end CategoryTheory.Spectra
