/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveIhomComposition
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHHomotopyMappingPath
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Whole nerve prisms in the original compact-open mapping space

Natural transformations and their actual chain classifiers give paths and
composition homotopies in the compact-open space on the ENTIRE native
classifying source. Postcomposition retains the original target map.
Cancellation is in this one mapping space; a pointwise collection of
nullhomotopies is never used in its place.
-/

noncomputable section

open CategoryTheory MonoidalCategory
open scoped Simplicial

universe u v

namespace CategoryTheory.NatTrans

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F G H : C ⥤ D}

/-- The actual whole native nerve prism as a path between the ORIGINAL
functor maps in their RAW compact-open space. -/
public abbrev nativeNerveMappingPath (α : F ⟶ G) :
    Path
      (ConcreteCategory.hom (C := CGWH.{max u v, max u v})
        (SSet.toCGWH.{max u v, max u v}.map (nerveMap F)))
      (ConcreteCategory.hom (C := CGWH.{max u v, max u v})
        (SSet.toCGWH.{max u v, max u v}.map (nerveMap G))) :=
  SSet.nativeHomotopyMappingPath (nerveHomotopy α)

/-- The path evaluates to the WHOLE original nerve cylinder, at every
original interval and native active-source point. -/
public theorem nativeNerveMappingPath_apply (α : F ⟶ G)
    (t : unitInterval) (a : SSet.toCGWH.{max u v, max u v}.obj (nerve C)) :
    nativeNerveMappingPath α t a =
      ((SSet.realizationTensorIsoCGWH.{max u v, max u v}
        (nerve C) (Δ[1] : SSet.{max u v})).inv ≫
          SSet.toCGWH.{max u v, max u v}.map (nerveHomotopyMap α))
            (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{max u v, max u v}.symm t)) :=
  SSet.nativeHomotopyMappingPath_apply (nerveHomotopy α) t a

/-- The actual original two-simplex proves concatenation for the whole
mapping-space paths of two composable natural transformations. -/
public theorem nativeNerveMappingPath_comp_homotopic (α : F ⟶ G) (β : G ⟶ H) :
    (nativeNerveMappingPath (α ≫ β)).Homotopic
      ((nativeNerveMappingPath α).trans (nativeNerveMappingPath β)) :=
  SSet.nativeHomotopyMappingPath_comp_homotopic
    (nerveHomotopy α) (nerveHomotopy β) (nerveHomotopy (α ≫ β))
    (nerveIhomCompStruct α β)

/-- The identity comparison is endpoint-fixed homotopic to the constant
path at the original realized functor map. -/
public theorem nativeNerveMappingPath_id_homotopic (F : C ⥤ D) :
    (nativeNerveMappingPath (𝟙 F)).Homotopic
      (Path.refl (ConcreteCategory.hom (C := CGWH.{max u v, max u v})
        (SSet.toCGWH.{max u v, max u v}.map (nerveMap F)))) := by
  change (SSet.nativeHomotopyMappingPath (nerveHomotopy (𝟙 F))).Homotopic _
  rw [nerveHomotopy_id_reflH]
  exact SSet.nativeHomotopyMappingPath_reflH_homotopic (nerveMap F)

variable {M : CGWH.{max u v, max u v}}

private def nativeMappingPostcomp (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M) :
    C(C(SSet.toCGWH.{max u v, max u v}.obj (nerve C),
          SSet.toCGWH.{max u v, max u v}.obj (nerve D)),
      C(SSet.toCGWH.{max u v, max u v}.obj (nerve C), M)) :=
  ⟨fun f => (ConcreteCategory.hom (C := CGWH.{max u v, max u v}) q).comp f,
    ContinuousMap.continuous_postcomp _⟩

/-- Postcomposition sends the entire original family to the SAME chosen
target by its ORIGINAL map, using only forward compact-open continuity. -/
public def nativeNerveMappingPathPostcomp (α : F ⟶ G)
    (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M) :
    Path
      ((ConcreteCategory.hom (C := CGWH.{max u v, max u v}) q).comp
        (ConcreteCategory.hom (C := CGWH.{max u v, max u v})
          (SSet.toCGWH.{max u v, max u v}.map (nerveMap F))))
      ((ConcreteCategory.hom (C := CGWH.{max u v, max u v}) q).comp
        (ConcreteCategory.hom (C := CGWH.{max u v, max u v})
          (SSet.toCGWH.{max u v, max u v}.map (nerveMap G)))) :=
  (nativeNerveMappingPath α).map (nativeMappingPostcomp q).continuous

private theorem nativeNerveMappingPathPostcomp_apply_computed
    (α : F ⟶ G) (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M)
    (t : unitInterval) (a : SSet.toCGWH.{max u v, max u v}.obj (nerve C)) :
    nativeNerveMappingPathPostcomp α q t a =
      q (((SSet.realizationTensorIsoCGWH.{max u v, max u v}
        (nerve C) (Δ[1] : SSet.{max u v})).inv ≫
          SSet.toCGWH.{max u v, max u v}.map (nerveHomotopyMap α))
            (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{max u v, max u v}.symm t))) := by
  change q (nativeNerveMappingPath α t a) = _
  rw [nativeNerveMappingPath_apply]

/-- Every original parameter value is retained after postcomposition. -/
public theorem nativeNerveMappingPathPostcomp_apply
    (α : F ⟶ G) (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M)
    (t : unitInterval) (a : SSet.toCGWH.{max u v, max u v}.obj (nerve C)) :
    nativeNerveMappingPathPostcomp α q t a =
      q (((SSet.realizationTensorIsoCGWH.{max u v, max u v}
        (nerve C) (Δ[1] : SSet.{max u v})).inv ≫
          SSet.toCGWH.{max u v, max u v}.map (nerveHomotopyMap α))
            (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{max u v, max u v}.symm t))) :=
  nativeNerveMappingPathPostcomp_apply_computed.{u, v} α q t a

/-- A proved constant ORIGINAL cylinder has constant whole mapping-space
values at every time and every active point, with its original source map. -/
public theorem nativeNerveMappingPathPostcomp_apply_of_fst_cylinder
    (α : F ⟶ G)
    (hcylinder : nerveHomotopyMap α =
      CartesianMonoidalCategory.fst (nerve C) (Δ[1] : SSet.{max u v}) ≫ nerveMap F)
    (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M)
    (t : unitInterval) (a : SSet.toCGWH.{max u v, max u v}.obj (nerve C)) :
    nativeNerveMappingPathPostcomp α q t a = q (SSet.toCGWH.{max u v, max u v}.map (nerveMap F) a) := by
  have he : (SSet.realizationTensorIsoCGWH.{max u v, max u v}
      (nerve C) (Δ[1] : SSet.{max u v})).inv ≫ SSet.toCGWH.{max u v, max u v}.map (nerveHomotopyMap α) =
      CartesianMonoidalCategory.fst
        (SSet.toCGWH.{max u v, max u v}.obj (nerve C))
        (SSet.toCGWH.{max u v, max u v}.obj (Δ[1] : SSet.{max u v})) ≫
          SSet.toCGWH.{max u v, max u v}.map (nerveMap F) := by
    rw [hcylinder, Functor.map_comp, ← Category.assoc,
      SSet.realizationTensorIsoCGWH_inv_fst]
  have hv := ConcreteCategory.congr_hom he
    (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{max u v, max u v}.symm t))
  rw [nativeNerveMappingPathPostcomp_apply]
  apply congrArg q
  exact hv.trans (by
    rw [ConcreteCategory.comp_apply, CGWH.tensorMk_fst])

/-- Equality of ENTIRE original nerve cylinders preserves every original
mapping-space path value, even when the endpoint functors are transported. -/
public theorem nativeNerveMappingPathPostcomp_congr_apply
    {F' G' : C ⥤ D} (α : F ⟶ G) (α' : F' ⟶ G')
    (hcylinder : nerveHomotopyMap α = nerveHomotopyMap α')
    (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M)
    (t : unitInterval) (a : SSet.toCGWH.{max u v, max u v}.obj (nerve C)) :
    nativeNerveMappingPathPostcomp α q t a = nativeNerveMappingPathPostcomp α' q t a := by
  rw [nativeNerveMappingPathPostcomp_apply, nativeNerveMappingPathPostcomp_apply, hcylinder]

/-- The whole original index functor restricts the mapping-space family
by its SAME native realized map, without an ordinary-product inverse. -/
public theorem nativeNerveMappingPathPostcomp_precomp_apply
    {B : Type u} [Category.{v} B] (K : B ⥤ C) (α : F ⟶ G)
    (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M)
    (t : unitInterval) (a : SSet.toCGWH.{max u v, max u v}.obj (nerve B)) :
    nativeNerveMappingPathPostcomp (Functor.whiskerLeft K α) q t a =
      nativeNerveMappingPathPostcomp α q t (SSet.toCGWH.{max u v, max u v}.map (nerveMap K) a) := by
  let j := nerveMap K
  let e := (SSet.realizationTensorIsoCGWH.{max u v, max u v}
    (nerve B) (Δ[1] : SSet.{max u v})).inv
  let e' := (SSet.realizationTensorIsoCGWH.{max u v, max u v}
    (nerve C) (Δ[1] : SSet.{max u v})).inv
  let r := SSet.toCGWH.{max u v, max u v}.map (nerveHomotopyMap α)
  have he : e ≫ SSet.toCGWH.{max u v, max u v}.map (nerveHomotopyMap (Functor.whiskerLeft K α)) =
      (SSet.toCGWH.{max u v, max u v}.map j ▷ SSet.toCGWH.{max u v, max u v}.obj (Δ[1] : SSet.{max u v})) ≫ e' ≫ r := by
    rw [← nerveHomotopyMap_precomp K α, Functor.map_comp, ← Category.assoc]
    exact (congrArg (fun f => f ≫ r)
      (SSet.realizationTensorIsoCGWH_inv_whiskerRight j (Δ[1] : SSet.{max u v}))).trans
        (Category.assoc _ _ _)
  let z := CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{max u v, max u v}.symm t)
  calc
    nativeNerveMappingPathPostcomp (Functor.whiskerLeft K α) q t a =
        q ((e ≫ SSet.toCGWH.{max u v, max u v}.map (nerveHomotopyMap (Functor.whiskerLeft K α))) z) :=
      nativeNerveMappingPathPostcomp_apply (Functor.whiskerLeft K α) q t a
    _ = q (((SSet.toCGWH.{max u v, max u v}.map j ▷ SSet.toCGWH.{max u v, max u v}.obj (Δ[1] : SSet.{max u v})) ≫
        e' ≫ r) z) := congrArg (fun f => q (f z)) he
    _ = q ((e' ≫ r) (CGWH.tensorMk (SSet.toCGWH.{max u v, max u v}.map j a)
        (CGWH.nativeIntervalHomeomorph.{max u v, max u v}.symm t))) := by
      rw [ConcreteCategory.comp_apply, CGWH.tensorMk_whiskerRight]
    _ = nativeNerveMappingPathPostcomp α q t (SSet.toCGWH.{max u v, max u v}.map j a) :=
      (nativeNerveMappingPathPostcomp_apply α q t (SSet.toCGWH.{max u v, max u v}.map j a)).symm

private theorem nativeNerveMappingPathPostcomp_comp_homotopic_computed
    (α : F ⟶ G) (β : G ⟶ H) (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M) :
    (nativeNerveMappingPathPostcomp (α ≫ β) q).Homotopic
      ((nativeNerveMappingPathPostcomp α q).trans (nativeNerveMappingPathPostcomp β q)) := by
  have hc := (nativeNerveMappingPath_comp_homotopic α β).map (nativeMappingPostcomp q)
  rw [Path.map_trans] at hc
  exact hc

/-- The same computed two-simplex retains the whole composition homotopy
after the ORIGINAL target map. -/
public theorem nativeNerveMappingPathPostcomp_comp_homotopic
    (α : F ⟶ G) (β : G ⟶ H) (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M) :
    (nativeNerveMappingPathPostcomp (α ≫ β) q).Homotopic
      ((nativeNerveMappingPathPostcomp α q).trans (nativeNerveMappingPathPostcomp β q)) :=
  nativeNerveMappingPathPostcomp_comp_homotopic_computed α β q

private theorem nativeNerveMappingPathPostcomp_id_homotopic_computed
    (F : C ⥤ D) (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M) :
    (nativeNerveMappingPathPostcomp (𝟙 F) q).Homotopic
      (Path.refl ((ConcreteCategory.hom (C := CGWH.{max u v, max u v}) q).comp
        (ConcreteCategory.hom (C := CGWH.{max u v, max u v})
          (SSet.toCGWH.{max u v, max u v}.map (nerveMap F))))) := by
  have hc := (nativeNerveMappingPath_id_homotopic F).map (nativeMappingPostcomp q)
  have hr :
      (Path.refl (ConcreteCategory.hom (C := CGWH.{max u v, max u v})
        (SSet.toCGWH.{max u v, max u v}.map (nerveMap F)))).map (nativeMappingPostcomp q).continuous =
      Path.refl ((ConcreteCategory.hom (C := CGWH.{max u v, max u v}) q).comp
        (ConcreteCategory.hom (C := CGWH.{max u v, max u v})
          (SSet.toCGWH.{max u v, max u v}.map (nerveMap F)))) := by
    ext t
    rfl
  rw [hr] at hc
  exact hc

/-- The original identity family stays null as ONE whole mapping-space
path after the original target map. -/
public theorem nativeNerveMappingPathPostcomp_id_homotopic
    (F : C ⥤ D) (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M) :
    (nativeNerveMappingPathPostcomp (𝟙 F) q).Homotopic
      (Path.refl ((ConcreteCategory.hom (C := CGWH.{max u v, max u v}) q).comp
        (ConcreteCategory.hom (C := CGWH.{max u v, max u v})
          (SSet.toCGWH.{max u v, max u v}.map (nerveMap F))))) :=
  nativeNerveMappingPathPostcomp_id_homotopic_computed F q

private theorem cancel_right_whole_mapping_path
    {Z : Type*} [TopologicalSpace Z] {a b : Z}
    (p q : Path a b) (r : Path b a)
    (hp : (p.trans r).Homotopic (Path.refl a))
    (hq : (q.trans r).Homotopic (Path.refl a)) : p.Homotopic q := by
  have ht :
      Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk p)
          (Path.Homotopic.Quotient.mk r) =
        Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk q)
          (Path.Homotopic.Quotient.mk r) :=
    (Path.Homotopic.Quotient.eq.mpr hp).trans (Path.Homotopic.Quotient.eq.mpr hq).symm
  have hc := congrArg (fun z : Path.Homotopic.Quotient a a =>
    Path.Homotopic.Quotient.trans z
      (Path.Homotopic.Quotient.symm (Path.Homotopic.Quotient.mk r))) ht
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl] at hc
  exact Path.Homotopic.Quotient.exact hc

/-- A filled WHOLE original comparison difference identifies the two
whole paths. The inverse comparison and both chain triangles are derived
from the actual natural isomorphism and original nerve prisms. -/
public theorem nativeNerveMappingPathPostcomp_homotopic_of_difference_null
    (α : F ⟶ G) (ν : F ≅ G) (q : SSet.toCGWH.{max u v, max u v}.obj (nerve D) ⟶ M)
    (hnull : (nativeNerveMappingPathPostcomp (α ≫ ν.inv) q).Homotopic
      (Path.refl ((ConcreteCategory.hom (C := CGWH.{max u v, max u v}) q).comp
        (ConcreteCategory.hom (C := CGWH.{max u v, max u v})
          (SSet.toCGWH.{max u v, max u v}.map (nerveMap F)))))) :
    (nativeNerveMappingPathPostcomp α q).Homotopic
      (nativeNerveMappingPathPostcomp ν.hom q) := by
  have hp := (nativeNerveMappingPathPostcomp_comp_homotopic α ν.inv q).symm.trans hnull
  have hi : (nativeNerveMappingPathPostcomp (ν.hom ≫ ν.inv) q).Homotopic
      (Path.refl ((ConcreteCategory.hom (C := CGWH.{max u v, max u v}) q).comp
        (ConcreteCategory.hom (C := CGWH.{max u v, max u v})
          (SSet.toCGWH.{max u v, max u v}.map (nerveMap F))))) := by
    rw [ν.hom_inv_id]
    exact nativeNerveMappingPathPostcomp_id_homotopic F q
  have hq := (nativeNerveMappingPathPostcomp_comp_homotopic ν.hom ν.inv q).symm.trans hi
  exact cancel_right_whole_mapping_path (nativeNerveMappingPathPostcomp α q)
    (nativeNerveMappingPathPostcomp ν.hom q) (nativeNerveMappingPathPostcomp ν.inv q) hp hq

end CategoryTheory.NatTrans

end
