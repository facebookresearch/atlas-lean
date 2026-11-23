/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.CGWHWeakHSpaceFundamentalGroup
public import MathlibExt.CategoryTheory.ClassifyingSpace.PointedCGWH
public import MathlibExt.CategoryTheory.NerveProduct
public import MathlibExt.CategoryTheory.NerveHomotopyRealization
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedProductPoint

/-!
# Weak H-space structure on categorical classifying spaces

A multiplication functor with left and right unit natural isomorphisms gives
the native CGWH classifying space a weak H-space structure.  The two unitor
components at the selected object are required to agree explicitly; their
common realized edge is the chosen root path from the product of the unit
with itself to the selected unit.

The multiplication is defined on the categorical CGWH product.  No raw
product identification, strict unit equality, classifying-space equivalence,
homology statement, plus construction, or Q-comparison is asserted.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory.Limits Opposite Simplicial
open scoped Simplicial

universe w u v

namespace CategoryTheory

/-- Left multiplication by a selected categorical object. -/
def categoricalLeftUnitFunctor
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (e : D) : D ⥤ D :=
  ((Functor.const D).obj e).prod' (𝟭 D) ⋙ mu

/-- Right multiplication by a selected categorical object. -/
def categoricalRightUnitFunctor
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (e : D) : D ⥤ D :=
  (𝟭 D).prod' ((Functor.const D).obj e) ⋙ mu

/-- Native multiplication on the CGWH classifying space induced by a
categorical multiplication functor. -/
noncomputable def categoricalClassifyingSpaceMul
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) :
    classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D) ⨯
        classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D) ⟶
      classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D) :=
  (SSet.realizationProdIsoCGWH
      (nerve D) (nerve D)).inv ≫
    SSet.toCGWH.map (nerveProdIso D D).inv ≫
      classifyingSpaceCGWH.map mu.toCatHom

set_option backward.isDefEq.respectTransparency false in
/-- The categorical multiplication sends a pair of realized object vertices
to the realized vertex of their categorical product. -/
@[simp]
theorem categoricalClassifyingSpaceMul_prodPoint
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (x y : D) :
    categoricalClassifyingSpaceMul.{w} D mu
        (CGWH.prodPoint _ _
          (classifyingSpaceCGWHPoint.{w} x)
          (classifyingSpaceCGWHPoint.{w} y)) =
      classifyingSpaceCGWHPoint.{w} (mu.obj (x, y)) := by
  unfold categoricalClassifyingSpaceMul
  change SSet.toTop.map (nerveMap mu)
      (SSet.toTop.map (nerveProdIso D D).inv
        ((SSet.realizationProdIsoCGWH.{w, max u v}
          (nerve D) (nerve D)).inv
          (CGWH.prodPoint _ _
            (SSet.realizedVertex (ComposableArrows.mk₀ x))
            (SSet.realizedVertex (ComposableArrows.mk₀ y))))) =
    SSet.realizedVertex (ComposableArrows.mk₀ (mu.obj (x, y)))
  rw [realizationProdIsoCGWH_inv_prodPoint_realizedVertex]
  rw [← SSet.realizedVertex_naturality,
    nerveProdIso_inv_app_pair_mk₀,
    ← SSet.realizedVertex_naturality,
    nerveMap_app_mk₀]

/-- The nerve of a constant functor is the constant simplicial map at its
selected vertex. -/
@[simp]
theorem nerveMap_constFunctor
    (C D : Type u) [Category.{v} C] [Category.{v} D] (d : D) :
    nerveMap ((Functor.const C).obj d) =
      SSet.const (X := nerve C) (ComposableArrows.mk₀ d) := by
  ext n z
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The native classifying-space map of a constant functor is the literal
constant CGWH morphism at the corresponding realized vertex. -/
theorem classifyingSpaceCGWH_map_constFunctor
    (D : Type u) [Category.{v} D] (e : D) :
    classifyingSpaceCGWH.{w, v, u}.map
        ((Functor.const D).obj e).toCatHom =
      CGWH.constMap
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))
        (classifyingSpaceCGWHPoint.{w} e) := by
  apply ConcreteCategory.hom_ext
  intro z
  change SSet.toTop.map (nerveMap ((Functor.const D).obj e)) z =
    SSet.realizedVertex (ComposableArrows.mk₀ e)
  rw [nerveMap_constFunctor]
  let q := IsTerminal.from SSet.stdSimplex.isTerminalObj₀ (nerve D)
  have hfac :
      (SSet.const (X := nerve D) (ComposableArrows.mk₀ e)) =
        q ≫ (SSet.const (X := (Δ[0] : SSet.{max u v}))
          (Y := nerve D) (ComposableArrows.mk₀ e)) := by
    rw [SSet.comp_const]
  rw [hfac, Functor.map_comp, SSet.realizedVertex_eq_const]
  exact congrArg
    (SSet.toTop.map (SSet.const (X := (Δ[0] : SSet.{max u v}))
      (Y := nerve D) (ComposableArrows.mk₀ e)))
    (Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Pairing two native classifying-space maps and passing through the
realization and nerve product isomorphisms gives the classifying-space map
of the paired functor. -/
theorem classifyingSpaceCGWH_prodLift
    {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
    (F : C ⥤ D) (G : C ⥤ E) :
    Limits.prod.lift
        (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom)
        (classifyingSpaceCGWH.{w, v, u}.map G.toCatHom) ≫
        (SSet.realizationProdIsoCGWH
          (nerve D) (nerve E)).inv ≫
        SSet.toCGWH.map (nerveProdIso D E).inv =
      classifyingSpaceCGWH.{w, v, u}.map (F.prod' G).toCatHom := by
  have hReal :
      Limits.prod.lift
          (SSet.toCGWH.{w, max u v}.map (nerveMap F))
          (SSet.toCGWH.{w, max u v}.map (nerveMap G)) ≫
          (SSet.realizationProdIsoCGWH
            (nerve D) (nerve E)).inv =
        SSet.toCGWH.{w, max u v}.map
          (Limits.prod.lift (nerveMap F) (nerveMap G)) := by
    apply (cancel_mono
      (SSet.realizationProdIsoCGWH.{w, max u v}
        (nerve D) (nerve E)).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Limits.prod.hom_ext
    · rw [Category.assoc, SSet.realizationProdIsoCGWH_hom_fst,
        ← Functor.map_comp, Limits.prod.lift_fst,
        Limits.prod.lift_fst]
    · rw [Category.assoc, SSet.realizationProdIsoCGWH_hom_snd,
        ← Functor.map_comp, Limits.prod.lift_snd,
        Limits.prod.lift_snd]
  have hNerve :
      Limits.prod.lift (nerveMap F) (nerveMap G) ≫
          (nerveProdIso D E).inv =
        nerveMap (F.prod' G) := by
    apply (cancel_mono (nerveProdIso D E).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply Limits.prod.hom_ext
    · rw [Category.assoc, nerveProdIso_hom_comp_fst,
        Limits.prod.lift_fst, nerveMap_comp]
      rfl
    · rw [Category.assoc, nerveProdIso_hom_comp_snd,
        Limits.prod.lift_snd, nerveMap_comp]
      rfl
  change Limits.prod.lift
      (SSet.toCGWH.map (nerveMap F))
      (SSet.toCGWH.map (nerveMap G)) ≫
      (SSet.realizationProdIsoCGWH (nerve D) (nerve E)).inv ≫
      SSet.toCGWH.map (nerveProdIso D E).inv =
    SSet.toCGWH.map (nerveMap (F.prod' G))
  rw [← Category.assoc, hReal, ← Functor.map_comp, hNerve]

set_option backward.isDefEq.respectTransparency false in
/-- The left restriction of the categorical classifying-space multiplication
is the classifying-space map of the categorical left-unit functor. -/
theorem categoricalClassifyingSpaceMul_leftUnitMap
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (e : D) :
    CGWH.hspaceLeftUnitMap
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))
        (categoricalClassifyingSpaceMul.{w} D mu)
        (classifyingSpaceCGWHPoint.{w} e) =
      classifyingSpaceCGWH.{w, v, u}.map
        (categoricalLeftUnitFunctor D mu e).toCatHom := by
  unfold CGWH.hspaceLeftUnitMap categoricalClassifyingSpaceMul
  rw [← classifyingSpaceCGWH_map_constFunctor]
  rw [← classifyingSpaceCGWH.map_id]
  calc
    ((Limits.prod.lift
        (classifyingSpaceCGWH.{w, v, u}.map
          ((Functor.const D).obj e).toCatHom)
        (classifyingSpaceCGWH.{w, v, u}.map (𝟙 (Cat.of D))) ≫
          (SSet.realizationProdIsoCGWH
            (nerve D) (nerve D)).inv) ≫
          SSet.toCGWH.map (nerveProdIso D D).inv) ≫
        classifyingSpaceCGWH.{w, v, u}.map mu.toCatHom =
      (Limits.prod.lift
        (classifyingSpaceCGWH.{w, v, u}.map
          ((Functor.const D).obj e).toCatHom)
        (classifyingSpaceCGWH.{w, v, u}.map (𝟙 (Cat.of D))) ≫
          ((SSet.realizationProdIsoCGWH
            (nerve D) (nerve D)).inv ≫
            SSet.toCGWH.map (nerveProdIso D D).inv)) ≫
        classifyingSpaceCGWH.{w, v, u}.map mu.toCatHom := by
          exact Category.assoc _ _ _
    _ = classifyingSpaceCGWH.{w, v, u}.map
          (((Functor.const D).obj e).prod' (𝟭 D)).toCatHom ≫
        classifyingSpaceCGWH.{w, v, u}.map mu.toCatHom := by
          exact congrArg
            (fun k ↦ k ≫
              classifyingSpaceCGWH.{w, v, u}.map mu.toCatHom)
            (classifyingSpaceCGWH_prodLift.{w}
              ((Functor.const D).obj e) (𝟭 D))
    _ = classifyingSpaceCGWH.{w, v, u}.map
        ((((Functor.const D).obj e).prod' (𝟭 D)) ⋙ mu).toCatHom := by
          rw [← classifyingSpaceCGWH.map_comp]
          rfl
    _ = _ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The right restriction of the categorical classifying-space multiplication
is the classifying-space map of the categorical right-unit functor. -/
theorem categoricalClassifyingSpaceMul_rightUnitMap
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (e : D) :
    CGWH.hspaceRightUnitMap
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))
        (categoricalClassifyingSpaceMul.{w} D mu)
        (classifyingSpaceCGWHPoint.{w} e) =
      classifyingSpaceCGWH.{w, v, u}.map
        (categoricalRightUnitFunctor D mu e).toCatHom := by
  unfold CGWH.hspaceRightUnitMap categoricalClassifyingSpaceMul
  rw [← classifyingSpaceCGWH.map_id]
  rw [← classifyingSpaceCGWH_map_constFunctor]
  calc
    ((Limits.prod.lift
        (classifyingSpaceCGWH.{w, v, u}.map (𝟙 (Cat.of D)))
        (classifyingSpaceCGWH.{w, v, u}.map
          ((Functor.const D).obj e).toCatHom) ≫
          (SSet.realizationProdIsoCGWH
            (nerve D) (nerve D)).inv) ≫
          SSet.toCGWH.map (nerveProdIso D D).inv) ≫
        classifyingSpaceCGWH.{w, v, u}.map mu.toCatHom =
      (Limits.prod.lift
        (classifyingSpaceCGWH.{w, v, u}.map (𝟙 (Cat.of D)))
        (classifyingSpaceCGWH.{w, v, u}.map
          ((Functor.const D).obj e).toCatHom) ≫
          ((SSet.realizationProdIsoCGWH
            (nerve D) (nerve D)).inv ≫
            SSet.toCGWH.map (nerveProdIso D D).inv)) ≫
        classifyingSpaceCGWH.{w, v, u}.map mu.toCatHom := by
          exact Category.assoc _ _ _
    _ = classifyingSpaceCGWH.{w, v, u}.map
          ((𝟭 D).prod' ((Functor.const D).obj e)).toCatHom ≫
        classifyingSpaceCGWH.{w, v, u}.map mu.toCatHom := by
          exact congrArg
            (fun k ↦ k ≫
              classifyingSpaceCGWH.{w, v, u}.map mu.toCatHom)
            (classifyingSpaceCGWH_prodLift.{w}
              (𝟭 D) ((Functor.const D).obj e))
    _ = classifyingSpaceCGWH.{w, v, u}.map
        (((𝟭 D).prod' ((Functor.const D).obj e)) ⋙ mu).toCatHom := by
          rw [← classifyingSpaceCGWH.map_comp]
          rfl
    _ = _ := rfl

/-- The original native classifying map is the exact underlying-Top conjugate. -/
theorem classifyingSpaceCGWH_map_toTopIso
    {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    (classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of C)).hom ≫
        SSet.toTop.map (nerveMap F) ≫
        (classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of D)).inv =
      CGWH.cgwhToTop.map (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom) := by
  let eC := classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of C)
  let eD := classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of D)
  have h := (classifyingSpaceCGWHToTopIso.{w, v, u}).hom.naturality F.toCatHom
  change CGWH.cgwhToTop.map (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom) ≫ eD.hom =
    eC.hom ≫ SSet.toTop.map (nerveMap F) at h
  calc
    eC.hom ≫ SSet.toTop.map (nerveMap F) ≫ eD.inv =
        (eC.hom ≫ SSet.toTop.map (nerveMap F)) ≫ eD.inv :=
      (Category.assoc _ _ _).symm
    _ = (CGWH.cgwhToTop.map (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom) ≫
        eD.hom) ≫ eD.inv := congrArg (· ≫ eD.inv) h.symm
    _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- A selected native classifying-space point is the inverse image of its
direct-realization vertex under the underlying-Top comparison. -/
theorem classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex
    {D : Type u} [Category.{v} D] (d : D) :
    classifyingSpaceCGWHPoint.{w} d =
      (classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of D)).inv
        (SSet.realizedVertex (ComposableArrows.mk₀ d)) := by
  let delta := classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of D)
  apply (ConcreteCategory.bijective_of_isIso delta.hom).1
  rw [Iso.inv_hom_id_apply]
  exact classifyingSpaceCGWHPoint_toTop.{w, v, u} d

set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation realizes to a homotopy between the corresponding
native CGWH classifying-space maps. -/
noncomputable def classifyingSpaceCGWHNatTransHomotopy
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) :
    ContinuousMap.Homotopy
      (CGWH.cgwhToTop.map (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom)).hom
      (CGWH.cgwhToTop.map (classifyingSpaceCGWH.{w, v, u}.map G.toCatHom)).hom := by
  let eC := classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of C)
  let eD := classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of D)
  let H := SSet.realizeHomotopy (nerve C) (nerve D)
    (nerveMap F) (nerveMap G) (NatTrans.nerveHomotopy alpha)
  let raw := (ContinuousMap.Homotopy.refl eD.inv.hom).comp
    (H.compContinuousMap eC.hom.hom)
  have hF : eD.inv.hom.comp
      ((SSet.toTop.map (nerveMap F)).hom.comp eC.hom.hom) =
    (CGWH.cgwhToTop.map (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom)).hom := by
    change ConcreteCategory.hom
      (eC.hom ≫ SSet.toTop.map (nerveMap F) ≫ eD.inv) = _
    exact congrArg ConcreteCategory.hom (classifyingSpaceCGWH_map_toTopIso.{w} F)
  have hG : eD.inv.hom.comp
      ((SSet.toTop.map (nerveMap G)).hom.comp eC.hom.hom) =
    (CGWH.cgwhToTop.map (classifyingSpaceCGWH.{w, v, u}.map G.toCatHom)).hom := by
    change ConcreteCategory.hom
      (eC.hom ≫ SSet.toTop.map (nerveMap G) ≫ eD.inv) = _
    exact congrArg ConcreteCategory.hom (classifyingSpaceCGWH_map_toTopIso.{w} G)
  exact raw.cast hF hG

/-- Every time and source point keeps the original realized natural-transformation family. -/
theorem classifyingSpaceCGWHNatTransHomotopy_value
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (t : unitInterval)
    (z : classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C)) :
    classifyingSpaceCGWHNatTransHomotopy.{w} alpha (t, z) =
      (classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of D)).inv
        (SSet.realizeHomotopy (nerve C) (nerve D) (nerveMap F) (nerveMap G)
          (NatTrans.nerveHomotopy alpha)
          (t, (classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of C)).hom z)) := rfl

/-- At a selected object, the native classifying-space homotopy of a natural
transformation traces the inverse image of the realized component edge. -/
theorem classifyingSpaceCGWHNatTransHomotopy_evalAt
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (alpha : F ⟶ G) (c : C) :
    (classifyingSpaceCGWHNatTransHomotopy.{w} alpha).evalAt
        (classifyingSpaceCGWHPoint.{w} c) =
      ((TopCat.pathEquiv
        (SSet.realizedEdgePath
          (CategoryTheory.nerve.edgeMk (alpha.app c)))).map
            (classifyingSpaceCGWHToTopIso.{w, v, u}.app
              (Cat.of D)).inv.hom.continuous).cast
        ((classifyingSpaceCGWH_map_point.{w} F c).trans
          (classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex
            (F.obj c)))
        ((classifyingSpaceCGWH_map_point.{w} G c).trans
          (classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex
            (G.obj c))) := by
  apply Path.ext
  funext t
  change (classifyingSpaceCGWHToTopIso.{w, v, u}.app
      (Cat.of D)).inv
      (SSet.realizeHomotopy (nerve C) (nerve D)
        (nerveMap F) (nerveMap G)
        (NatTrans.nerveHomotopy alpha)
        (t, (classifyingSpaceCGWHToTopIso.{w, v, u}.app
          (Cat.of C)).hom (classifyingSpaceCGWHPoint.{w} c))) =
    (classifyingSpaceCGWHToTopIso.{w, v, u}.app
      (Cat.of D)).inv
      ((SSet.realizedEdgePath
        (CategoryTheory.nerve.edgeMk (alpha.app c))).hom
          (TopCat.I.homeomorph.symm t))
  rw [classifyingSpaceCGWHPoint_toTop]
  exact congrArg
    (classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of D)).inv
    (congrArg (fun p ↦ p t)
      (SSet.realizeHomotopy_nerveHomotopy_evalAt_polymorphic alpha c))

/-- The common left-unitor component realizes to the chosen root path from
the product of the selected unit with itself to the selected unit. -/
noncomputable def categoricalClassifyingSpaceRootPath
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (e : D)
    (leftUnit : categoricalLeftUnitFunctor D mu e ≅ 𝟭 D) :
    Path
      (categoricalClassifyingSpaceMul.{w} D mu
        (CGWH.prodPoint _ _
          (classifyingSpaceCGWHPoint.{w} e)
          (classifyingSpaceCGWHPoint.{w} e)))
      (classifyingSpaceCGWHPoint.{w} e) := by
  let delta := classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of D)
  let p := TopCat.pathEquiv (SSet.realizedEdgePath
    (CategoryTheory.nerve.edgeMk (leftUnit.hom.app e)))
  have hSource :
      categoricalClassifyingSpaceMul.{w} D mu
          (CGWH.prodPoint _ _
            (classifyingSpaceCGWHPoint.{w} e)
            (classifyingSpaceCGWHPoint.{w} e)) =
        delta.inv (SSet.realizedVertex
          (ComposableArrows.mk₀ (mu.obj (e, e)))) :=
    (categoricalClassifyingSpaceMul_prodPoint.{w} D mu e e).trans
      (classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex
        (mu.obj (e, e)))
  have hTarget :
      classifyingSpaceCGWHPoint.{w} e =
        delta.inv (SSet.realizedVertex (ComposableArrows.mk₀ e)) :=
    classifyingSpaceCGWHPoint_eq_toTopIso_inv_realizedVertex e
  exact (p.map delta.inv.hom.continuous).cast hSource hTarget

set_option backward.isDefEq.respectTransparency false in
/-- The realized categorical left unitor, transported to the native CGWH
classifying space and expressed as a homotopy from left multiplication. -/
noncomputable def categoricalClassifyingSpaceLeftUnitHomotopy
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (e : D)
    (leftUnit : categoricalLeftUnitFunctor D mu e ≅ 𝟭 D) :
    ContinuousMap.Homotopy
      (CGWH.cgwhToTop.map
        (CGWH.hspaceLeftUnitMap
          (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))
          (categoricalClassifyingSpaceMul.{w} D mu)
          (classifyingSpaceCGWHPoint.{w} e))).hom
      (ContinuousMap.id
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))) := by
  let H := classifyingSpaceCGWHNatTransHomotopy.{w} leftUnit.hom
  have hZero :
      (CGWH.cgwhToTop.map
        (classifyingSpaceCGWH.{w, v, u}.map
          (categoricalLeftUnitFunctor D mu e).toCatHom)).hom =
        (CGWH.cgwhToTop.map
          (CGWH.hspaceLeftUnitMap
            (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))
            (categoricalClassifyingSpaceMul.{w} D mu)
            (classifyingSpaceCGWHPoint.{w} e))).hom :=
    congrArg (fun k ↦ (CGWH.cgwhToTop.map k).hom)
      (categoricalClassifyingSpaceMul_leftUnitMap.{w} D mu e).symm
  have hOne :
      (CGWH.cgwhToTop.map
        (classifyingSpaceCGWH.{w, v, u}.map
          (𝟭 D).toCatHom)).hom =
        ContinuousMap.id
          (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D)) := by
    apply ContinuousMap.ext
    intro x
    change (classifyingSpaceCGWH.{w, v, u}.map (𝟙 (Cat.of D))) x = x
    rw [classifyingSpaceCGWH.map_id]
    rfl
  exact H.cast hZero hOne

set_option backward.isDefEq.respectTransparency false in
/-- The realized categorical right unitor, transported to the native CGWH
classifying space and expressed as a homotopy from right multiplication. -/
noncomputable def categoricalClassifyingSpaceRightUnitHomotopy
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (e : D)
    (rightUnit : categoricalRightUnitFunctor D mu e ≅ 𝟭 D) :
    ContinuousMap.Homotopy
      (CGWH.cgwhToTop.map
        (CGWH.hspaceRightUnitMap
          (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))
          (categoricalClassifyingSpaceMul.{w} D mu)
          (classifyingSpaceCGWHPoint.{w} e))).hom
      (ContinuousMap.id
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))) := by
  let H := classifyingSpaceCGWHNatTransHomotopy.{w} rightUnit.hom
  have hZero :
      (CGWH.cgwhToTop.map
        (classifyingSpaceCGWH.{w, v, u}.map
          (categoricalRightUnitFunctor D mu e).toCatHom)).hom =
        (CGWH.cgwhToTop.map
          (CGWH.hspaceRightUnitMap
            (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))
            (categoricalClassifyingSpaceMul.{w} D mu)
            (classifyingSpaceCGWHPoint.{w} e))).hom :=
    congrArg (fun k ↦ (CGWH.cgwhToTop.map k).hom)
      (categoricalClassifyingSpaceMul_rightUnitMap.{w} D mu e).symm
  have hOne :
      (CGWH.cgwhToTop.map
        (classifyingSpaceCGWH.{w, v, u}.map
          (𝟭 D).toCatHom)).hom =
        ContinuousMap.id
          (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D)) := by
    apply ContinuousMap.ext
    intro x
    change (classifyingSpaceCGWH.{w, v, u}.map (𝟙 (Cat.of D))) x = x
    rw [classifyingSpaceCGWH.map_id]
    rfl
  exact H.cast hZero hOne

/-- The left-unit homotopy traces the chosen realized unitor edge at the
selected object. -/
theorem categoricalClassifyingSpaceLeftUnitPath_eq_rootPath
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (e : D)
    (leftUnit : categoricalLeftUnitFunctor D mu e ≅ 𝟭 D) :
    CGWH.hspaceLeftUnitPath
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))
        (categoricalClassifyingSpaceMul.{w} D mu)
        (classifyingSpaceCGWHPoint.{w} e)
        (categoricalClassifyingSpaceLeftUnitHomotopy.{w}
          D mu e leftUnit) =
      categoricalClassifyingSpaceRootPath.{w} D mu e leftUnit := by
  apply Path.ext
  funext t
  change (classifyingSpaceCGWHNatTransHomotopy.{w}
      leftUnit.hom).evalAt (classifyingSpaceCGWHPoint.{w} e) t =
    ((TopCat.pathEquiv (SSet.realizedEdgePath
      (CategoryTheory.nerve.edgeMk (leftUnit.hom.app e)))).map
        (classifyingSpaceCGWHToTopIso.{w, v, u}.app
          (Cat.of D)).inv.hom.continuous) t
  exact congrArg (fun p ↦ p t)
    (classifyingSpaceCGWHNatTransHomotopy_evalAt.{w}
      leftUnit.hom e)

/-- If the left and right unitor components agree at the selected object,
the right-unit homotopy traces the same chosen root path. -/
theorem categoricalClassifyingSpaceRightUnitPath_eq_rootPath
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (e : D)
    (leftUnit : categoricalLeftUnitFunctor D mu e ≅ 𝟭 D)
    (rightUnit : categoricalRightUnitFunctor D mu e ≅ 𝟭 D)
    (unit_app_eq : leftUnit.hom.app e = rightUnit.hom.app e) :
    CGWH.hspaceRightUnitPath
        (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))
        (categoricalClassifyingSpaceMul.{w} D mu)
        (classifyingSpaceCGWHPoint.{w} e)
        (categoricalClassifyingSpaceRightUnitHomotopy.{w}
          D mu e rightUnit) =
      categoricalClassifyingSpaceRootPath.{w} D mu e leftUnit := by
  apply Path.ext
  funext t
  change (classifyingSpaceCGWHNatTransHomotopy.{w}
      rightUnit.hom).evalAt (classifyingSpaceCGWHPoint.{w} e) t =
    ((TopCat.pathEquiv (SSet.realizedEdgePath
      (CategoryTheory.nerve.edgeMk (leftUnit.hom.app e)))).map
        (classifyingSpaceCGWHToTopIso.{w, v, u}.app
          (Cat.of D)).inv.hom.continuous) t
  have h := congrArg (fun p ↦ p t)
    (classifyingSpaceCGWHNatTransHomotopy_evalAt.{w}
      rightUnit.hom e)
  rw [← unit_app_eq] at h
  exact h

/-- Weak-unit native CGWH H-space data on the classifying space of a
category with a multiplication and coherent left/right unitors. -/
noncomputable def categoricalClassifyingSpaceWeakHSpaceData
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (e : D)
    (leftUnit : categoricalLeftUnitFunctor D mu e ≅ 𝟭 D)
    (rightUnit : categoricalRightUnitFunctor D mu e ≅ 𝟭 D)
    (unit_app_eq : leftUnit.hom.app e = rightUnit.hom.app e) :
    CGWH.WeakHSpaceData
      (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D)) where
  mul := categoricalClassifyingSpaceMul.{w} D mu
  e := classifyingSpaceCGWHPoint.{w} e
  rootPath := categoricalClassifyingSpaceRootPath.{w} D mu e leftUnit
  leftUnit := categoricalClassifyingSpaceLeftUnitHomotopy.{w}
    D mu e leftUnit
  rightUnit := categoricalClassifyingSpaceRightUnitHomotopy.{w}
    D mu e rightUnit
  leftUnit_root := by
    rw [categoricalClassifyingSpaceLeftUnitPath_eq_rootPath]
  rightUnit_root := by
    rw [categoricalClassifyingSpaceRightUnitPath_eq_rootPath
      D mu e leftUnit rightUnit unit_app_eq]

/-- The fundamental group of the categorical classifying space at the
selected weak unit is commutative. -/
theorem categoricalClassifyingSpace_fundamentalGroup_mul_comm
    (D : Type u) [Category.{v} D] (mu : D × D ⥤ D) (e : D)
    (leftUnit : categoricalLeftUnitFunctor D mu e ≅ 𝟭 D)
    (rightUnit : categoricalRightUnitFunctor D mu e ≅ 𝟭 D)
    (unit_app_eq : leftUnit.hom.app e = rightUnit.hom.app e)
    (p q : FundamentalGroup
      (classifyingSpaceCGWH.{w, v, u}.obj (Cat.of D))
      (classifyingSpaceCGWHPoint.{w} e)) :
    p * q = q * p :=
  (categoricalClassifyingSpaceWeakHSpaceData.{w}
    D mu e leftUnit rightUnit unit_app_eq).fundamentalGroup_mul_comm p q

end CategoryTheory

end
