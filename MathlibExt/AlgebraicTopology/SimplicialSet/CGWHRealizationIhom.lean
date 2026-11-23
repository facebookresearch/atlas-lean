/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealizationTensor
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationHausdorff
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyIhom
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism
public import MathlibExt.Topology.Category.CGWH.GeneratedHomCompactOpen
public import MathlibExt.Topology.Category.CGWH.CartesianClosedComputations
public import MathlibExt.Topology.Category.CGWH.InternalHomCompactOpen

/-!
# Actual realization of the simplicial mapping-space prism

Realization of the ORIGINAL simplicial internal Hom maps to the native
internal Hom by the existing tensor comparison and the ORIGINAL evaluation.
The map to RAW compact-open functions uses only the forward compact-generation
counit. Every prism evaluates to its SAME original realized whole map.
No ordinary product inverse, homotopy, or weak comparison witness is assumed.
-/

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Topology
open scoped Simplicial

universe u v

namespace SSet

/-- The actual native realization-to-internal-Hom comparison, constructed
from the ORIGINAL evaluation and existing native tensor comparison. -/
public def realizationIhomToCGWH (X Y : SSet.{v}) :
    SSet.toCGWH.{u, v}.obj ((ihom X).obj Y) ⟶
      (ihom (SSet.toCGWH.{u, v}.obj X)).obj (SSet.toCGWH.{u, v}.obj Y) :=
  MonoidalClosed.curry
    ((realizationTensorIsoCGWH.{u, v} X ((ihom X).obj Y)).inv ≫
      SSet.toCGWH.{u, v}.map ((ihom.ev X).app Y))

private theorem realizationIhomToCGWH_uncurry_computed (X Y : SSet.{v}) :
    MonoidalClosed.uncurry (realizationIhomToCGWH.{u, v} X Y) =
      (realizationTensorIsoCGWH.{u, v} X ((ihom X).obj Y)).inv ≫
        SSet.toCGWH.{u, v}.map ((ihom.ev X).app Y) := by
  unfold realizationIhomToCGWH
  exact MonoidalClosed.uncurry_curry _

/-- The entire original evaluation is retained by the derived comparison. -/
public theorem realizationIhomToCGWH_uncurry (X Y : SSet.{v}) :
    MonoidalClosed.uncurry (realizationIhomToCGWH.{u, v} X Y) =
      (realizationTensorIsoCGWH.{u, v} X ((ihom X).obj Y)).inv ≫
        SSet.toCGWH.{u, v}.map ((ihom.ev X).app Y) :=
  realizationIhomToCGWH_uncurry_computed X Y

/-- Every original simplex prism has its SAME original realized whole
map after the mapping-space comparison and actual native uncurrying. -/
public theorem realizationIhomToCGWH_uncurry_prism
    {X Y : SSet.{v}} {n : ℕ} (H : X ⊗ (Δ[n] : SSet.{v}) ⟶ Y) :
    MonoidalClosed.uncurry
        (SSet.toCGWH.{u, v}.map (MonoidalClosed.curry H) ≫ realizationIhomToCGWH X Y) =
      (realizationTensorIsoCGWH.{u, v} X (Δ[n] : SSet.{v})).inv ≫
        SSet.toCGWH.{u, v}.map H := by
  have hev : (X ◁ MonoidalClosed.curry H) ≫ (ihom.ev X).app Y = H :=
    (MonoidalClosed.uncurry_eq (MonoidalClosed.curry H)).symm.trans
      (MonoidalClosed.uncurry_curry H)
  have ht := realizationTensorIsoCGWH_inv_whiskerLeft.{u, v} X (MonoidalClosed.curry H)
  calc
    MonoidalClosed.uncurry
        (SSet.toCGWH.{u, v}.map (MonoidalClosed.curry H) ≫ realizationIhomToCGWH X Y) =
      (SSet.toCGWH.{u, v}.obj X ◁ SSet.toCGWH.{u, v}.map (MonoidalClosed.curry H)) ≫
        MonoidalClosed.uncurry (realizationIhomToCGWH X Y) :=
      MonoidalClosed.uncurry_natural_left _ _
    _ = (SSet.toCGWH.{u, v}.obj X ◁ SSet.toCGWH.{u, v}.map (MonoidalClosed.curry H)) ≫
        (realizationTensorIsoCGWH.{u, v} X ((ihom X).obj Y)).inv ≫
          SSet.toCGWH.{u, v}.map ((ihom.ev X).app Y) := by
      rw [realizationIhomToCGWH_uncurry]
    _ = (realizationTensorIsoCGWH.{u, v} X (Δ[n] : SSet.{v})).inv ≫
        SSet.toCGWH.{u, v}.map (X ◁ MonoidalClosed.curry H) ≫
          SSet.toCGWH.{u, v}.map ((ihom.ev X).app Y) :=
      (congrArg (fun f => f ≫ SSet.toCGWH.{u, v}.map ((ihom.ev X).app Y)) ht.symm).trans
        (by simp only [Category.assoc])
    _ = (realizationTensorIsoCGWH.{u, v} X (Δ[n] : SSet.{v})).inv ≫
        SSet.toCGWH.{u, v}.map H := by
      rw [← Functor.map_comp, hev]

/-- The RAW compact-open mapping-space map of the ORIGINAL simplicial
internal Hom realization. Hausdorffness of the source is derived from its
actual realization; only the forward compact-generation map is used. -/
public def realizationIhomToCompactOpen (X Y : SSet.{u}) :
    C(SSet.toTop.obj ((ihom X).obj Y),
      C(SSet.toCGWH.{u, u}.obj X, SSet.toCGWH.{u, u}.obj Y)) := by
  let A : CGWH.{u, u} := SSet.toCGWH.{u, u}.obj X
  let B : CGWH.{u, u} := SSet.toCGWH.{u, u}.obj Y
  let _ : T2Space (SSet.toTop.obj X) := SSet.realization_t2Space X
  let e : A.toTop ≅ SSet.toTop.obj X := SSet.realizationToTopIso.{u, u}.app X
  let _ : T2Space A := (TopCat.homeoOfIso e).symm.t2Space
  exact (CGWH.internalHomToCompactOpen A B).comp
    (ConcreteCategory.hom (C := CGWH.{u, u}) (realizationIhomToCGWH.{u, u} X Y))

private theorem realizationIhomToCompactOpen_apply_computed
    (X Y : SSet.{u}) (z : SSet.toTop.obj ((ihom X).obj Y))
    (a : SSet.toCGWH.{u, u}.obj X) :
    realizationIhomToCompactOpen X Y z a =
      (WithGeneratedByTopology.equiv
        (X := CompactlyGenerated.compactHausProbes.{u})
        (Y := ContinuousMapGeneratedBy CompactlyGenerated.compactHausProbes.{u}
          (SSet.toCGWH.{u, u}.obj X) (SSet.toCGWH.{u, u}.obj Y))
          (realizationIhomToCGWH X Y z) :
        ContinuousMapGeneratedBy CompactlyGenerated.compactHausProbes.{u}
          (SSet.toCGWH.{u, u}.obj X) (SSet.toCGWH.{u, u}.obj Y)) a := by
  let A : CGWH.{u, u} := SSet.toCGWH.{u, u}.obj X
  let B : CGWH.{u, u} := SSet.toCGWH.{u, u}.obj Y
  let _ : T2Space (SSet.toTop.obj X) := SSet.realization_t2Space X
  let e : A.toTop ≅ SSet.toTop.obj X := SSet.realizationToTopIso.{u, u}.app X
  let _ : T2Space A := (TopCat.homeoOfIso e).symm.t2Space
  let k : C(SSet.toTop.obj ((ihom X).obj Y), CGWH.internalHom A B) :=
    ConcreteCategory.hom (C := CGWH.{u, u}) (realizationIhomToCGWH.{u, u} X Y)
  have hcomp : ((CGWH.internalHomToCompactOpen A B).comp k) z =
      CGWH.internalHomToCompactOpen A B (k z) :=
    ContinuousMap.comp_apply (CGWH.internalHomToCompactOpen A B) k z
  have he : realizationIhomToCompactOpen X Y z a =
      ((CGWH.internalHomToCompactOpen A B).comp k) z a := rfl
  exact he.trans
    ((congrArg (fun h : C(A, B) => h a) hcomp).trans
      (CGWH.internalHomToCompactOpen_apply A B (k z) a))

/-- The comparison uses the original underlying mapping-space function. -/
public theorem realizationIhomToCompactOpen_apply
    (X Y : SSet.{u}) (z : SSet.toTop.obj ((ihom X).obj Y))
    (a : SSet.toCGWH.{u, u}.obj X) :
    realizationIhomToCompactOpen X Y z a =
      (WithGeneratedByTopology.equiv
        (X := CompactlyGenerated.compactHausProbes.{u})
        (Y := ContinuousMapGeneratedBy CompactlyGenerated.compactHausProbes.{u}
          (SSet.toCGWH.{u, u}.obj X) (SSet.toCGWH.{u, u}.obj Y))
          (realizationIhomToCGWH X Y z) :
        ContinuousMapGeneratedBy CompactlyGenerated.compactHausProbes.{u}
          (SSet.toCGWH.{u, u}.obj X) (SSet.toCGWH.{u, u}.obj Y)) a :=
  realizationIhomToCompactOpen_apply_computed X Y z a

/-- Every whole original simplex prism evaluates on every active point
in the RAW mapping space by its SAME original native realized map. -/
public theorem realizationIhomToCompactOpen_prism_apply
    {X Y : SSet.{u}} {n : ℕ} (H : X ⊗ (Δ[n] : SSet.{u}) ⟶ Y)
    (z : SSet.toCGWH.{u, u}.obj (Δ[n] : SSet.{u}))
    (a : SSet.toCGWH.{u, u}.obj X) :
    realizationIhomToCompactOpen X Y (SSet.toCGWH.{u, u}.map (MonoidalClosed.curry H) z) a =
      ((realizationTensorIsoCGWH.{u, u} X (Δ[n] : SSet.{u})).inv ≫
        SSet.toCGWH.{u, u}.map H) (CGWH.tensorMk a z) := by
  have he := realizationIhomToCGWH_uncurry_prism.{u, u} H
  have hv := CGWH.internalHom_uncurry_apply
    (SSet.toCGWH.{u, u}.map (MonoidalClosed.curry H) ≫ realizationIhomToCGWH X Y)
    (CGWH.tensorMk a z)
  rw [CGWH.tensorMk_fst, CGWH.tensorMk_snd] at hv
  exact (realizationIhomToCompactOpen_apply X Y _ a).trans
    (hv.symm.trans (ConcreteCategory.congr_hom he (CGWH.tensorMk a z)))

end SSet

end
