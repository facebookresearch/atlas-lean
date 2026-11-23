/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveLiftRealization
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import Mathlib.CategoryTheory.Category.ULift
public import MathlibExt.CategoryTheory.NerveHomotopyRealization

/-!
# Actual functor maps on original realizations in independent universes

The existing object/Hom lifts place only the intermediate categories in one
working universe. The original functor is transported through the existing
category equivalences and realized, then returned to the original spaces by
the existing realization homeomorphisms. The original vertex is retained.
No category equivalence or space-map comparison is a premise.
-/

noncomputable section

open scoped ContinuousMap Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe uC vC uD vD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

/-- The canonical four-universe envelope of the original functor, used by its
realized nerve map and the independent comma comparisons. -/
@[expose] public def liftedFunctor (F : C ⥤ D) :
    ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C) ⥤
      ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D) :=
  (ULiftHomULiftCategory.equiv.{max uC vC uD vD, max uC vC uD vD, vC, uC} C).inverse ⋙
    F ⋙
      (ULiftHomULiftCategory.equiv.{max uC vC uD vD, max uC vC uD vD, vD, uD} D).functor

private theorem liftedFunctor_obj_computed (F : C ⥤ D) (c : C) :
    (liftedFunctor F).obj
        (ULiftHom.objUp (ULift.up c) :
          ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C)) =
      (ULiftHom.objUp (ULift.up (F.obj c)) :
        ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D)) := rfl

private def realizedFunctorMapRecipe (F : C ⥤ D) :
    C(SSet.toTop.obj (nerve C), SSet.toTop.obj (nerve D)) :=
  (SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD} D).toHomotopyEquiv.toFun.comp
    ((SSet.toTop.map (nerveMap (liftedFunctor F))).hom.comp
      (SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD} C).symm.toHomotopyEquiv.toFun)

/-- The actual continuous realization map of an arbitrary functor, retaining
both original category object/Hom universes and both original spaces. -/
public def realizedNerveFunctorMap (F : C ⥤ D) :
    C(SSet.toTop.obj (nerve C), SSet.toTop.obj (nerve D)) :=
  realizedFunctorMapRecipe F

private theorem realizedNerveFunctorMap_vertex_computed (F : C ⥤ D) (c : C) :
    realizedNerveFunctorMap F
        (SSet.realizedVertex (X := nerve C) (ComposableArrows.mk₀ c)) =
      SSet.realizedVertex (X := nerve D) (ComposableArrows.mk₀ (F.obj c)) := by
  let HC := SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD} C
  let HD := SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD} D
  let L := liftedFunctor F
  let x : ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C) :=
    ULiftHom.objUp (ULift.up c)
  have hC := SSet.realizedNerveLiftHomeomorph_symm_vertex.{uC, vC, max uC vC uD vD} C c
  have hMiddle : SSet.toTop.map (nerveMap L)
      (SSet.realizedVertex
        (X := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C)))
        (ComposableArrows.mk₀ x)) =
      SSet.realizedVertex
        (X := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D)))
        (ComposableArrows.mk₀ (L.obj x)) :=
    (SSet.realizedVertex_naturality
      (X := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C)))
      (Y := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D)))
      (nerveMap L) (ComposableArrows.mk₀ x)).symm.trans
        (congrArg (fun q => SSet.realizedVertex
          (X := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D))) q)
          (nerveMap_app_mk₀ L x))
  have hObject := liftedFunctor_obj_computed F c
  change HD (SSet.toTop.map (nerveMap L)
    (HC.symm (SSet.realizedVertex (X := nerve C) (ComposableArrows.mk₀ c)))) = _
  exact (congrArg (fun y => HD (SSet.toTop.map (nerveMap L) y)) hC).trans
    ((congrArg HD (hMiddle.trans (congrArg
      (fun y => SSet.realizedVertex
        (X := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D)))
        (ComposableArrows.mk₀ y)) hObject))).trans
      (SSet.realizedNerveLiftHomeomorph_vertex.{uD, vD, max uC vC uD vD} D (F.obj c)))

/-- Every original vertex maps to the vertex of the actual functor image. -/
public theorem realizedNerveFunctorMap_vertex (F : C ⥤ D) (c : C) :
    realizedNerveFunctorMap F
        (SSet.realizedVertex (X := nerve C) (ComposableArrows.mk₀ c)) =
      SSet.realizedVertex (X := nerve D) (ComposableArrows.mk₀ (F.obj c)) :=
  realizedNerveFunctorMap_vertex_computed F c

private theorem realizedNerveFunctorMap_edge_homotopic_computed
    (F : C ⥤ D) {x y : C} (k : x ⟶ y) :
    (((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := C) (x := x) (y := y) k))).map
          (realizedNerveFunctorMap F).continuous).cast
            (realizedNerveFunctorMap_vertex F x).symm
            (realizedNerveFunctorMap_vertex F y).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := D) (x := F.obj x) (y := F.obj y) (F.map k)))) := by
  let HC := SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD} C
  let HD := SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD} D
  let L := liftedFunctor F
  let K := (SSet.toTop.map (nerveMap L)).hom
  let M := HD.toHomotopyEquiv.toFun.comp K
  let xc : ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C) :=
    ULiftHom.objUp (ULift.up x)
  let yc : ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C) :=
    ULiftHom.objUp (ULift.up y)
  let xd : ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D) :=
    ULiftHom.objUp (ULift.up (F.obj x))
  let yd : ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D) :=
    ULiftHom.objUp (ULift.up (F.obj y))
  let kc : xc ⟶ yc := ULiftHom.up.map (ULift.upFunctor.map k)
  let kd : xd ⟶ yd := ULiftHom.up.map (ULift.upFunctor.map (F.map k))
  let pc := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (x := xc) (y := yc) kc))
  let pd := TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (x := xd) (y := yd) kd))
  have hRecipe (z : SSet.toTop.obj (nerve C)) :
      realizedNerveFunctorMap F z = M (HC.symm z) := rfl
  have hVertex (c : C) :
      M (SSet.realizedVertex
        (X := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C)))
          (ComposableArrows.mk₀ (ULiftHom.objUp (ULift.up c)))) =
        SSet.realizedVertex (X := nerve D) (ComposableArrows.mk₀ (F.obj c)) :=
    (congrArg M (SSet.realizedNerveLiftHomeomorph_symm_vertex.{uC, vC, max uC vC uD vD}
      C c)).symm.trans ((hRecipe _).symm.trans (realizedNerveFunctorMap_vertex F c))
  have hArrow : L.map kc = (kd : L.obj xc ⟶ L.obj yc) := rfl
  have hEdge : (nerveMap L).app (Opposite.op ⦋1⦌)
      (nerve.edgeMk (x := xc) (y := yc) kc).edge =
      (nerve.edgeMk (x := xd) (y := yd) kd).edge := by
    have hFirst : (nerveMap L).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk (x := xc) (y := yc) kc).edge =
        ComposableArrows.mk₁ (L.map kc) := nerveMap_app_mk₁ L kc
    exact hFirst.trans
      (congrArg (fun h : L.obj xc ⟶ L.obj yc => ComposableArrows.mk₁ h) hArrow)
  have hCurve (t : unitInterval) : K (pc t) = pd t := by
    let a := nerve.edgeMk (x := xc) (y := yc) kc
    let b := nerve.edgeMk (x := xd) (y := yd) kd
    let f := nerveMap L
    let Y : SSet.{max uC vC uD vD} :=
      nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D))
    have hEdgeValue : f.app (Opposite.op ⦋1⦌) a.edge = b.edge := hEdge
    have hYoneda : (SSet.yonedaEquiv.symm b.edge : (Δ[1] : SSet.{max uC vC uD vD}) ⟶ Y) =
        SSet.yonedaEquiv.symm a.edge ≫ f :=
      (congrArg (fun z : Y _⦋1⦌ => SSet.yonedaEquiv.symm z) hEdgeValue).symm.trans
        (SSet.yonedaEquiv_symm_comp a.edge f).symm
    have hNat : (SSet.realizedEdgePath b).hom =
        (SSet.realizedEdgePath a).hom ≫ SSet.toTop.map f := by
      calc
        _ = SSet.stdSimplex.toTopObjIsoI.inv ≫
            SSet.toTop.map (SSet.yonedaEquiv.symm b.edge) := SSet.realizedEdgePath_hom b
        _ = SSet.stdSimplex.toTopObjIsoI.inv ≫
            SSet.toTop.map (SSet.yonedaEquiv.symm a.edge ≫ f) :=
          congrArg (fun g : (Δ[1] : SSet.{max uC vC uD vD}) ⟶ Y =>
            SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map g) hYoneda
        _ = SSet.stdSimplex.toTopObjIsoI.inv ≫
            (SSet.toTop.map (SSet.yonedaEquiv.symm a.edge) ≫ SSet.toTop.map f) :=
          congrArg (fun g : SSet.toTop.obj (Δ[1] : SSet.{max uC vC uD vD}) ⟶
              SSet.toTop.obj Y => SSet.stdSimplex.toTopObjIsoI.inv ≫ g)
            (SSet.toTop.map_comp (SSet.yonedaEquiv.symm a.edge) f)
        _ = (SSet.stdSimplex.toTopObjIsoI.inv ≫
            SSet.toTop.map (SSet.yonedaEquiv.symm a.edge)) ≫ SSet.toTop.map f :=
          (Category.assoc _ _ _).symm
        _ = (SSet.realizedEdgePath a).hom ≫ SSet.toTop.map f :=
          congrArg (fun g : TopCat.I.{max uC vC uD vD} ⟶
              SSet.toTop.obj (nerve (ULiftHom.{max uC vC uD vD}
                (ULift.{max uC vC uD vD} C))) => g ≫ SSet.toTop.map f)
            (SSet.realizedEdgePath_hom a).symm
    change SSet.toTop.map f
        ((SSet.realizedEdgePath a).hom
          (TopCat.I.homeomorph.{max uC vC uD vD}.symm t)) =
      (SSet.realizedEdgePath b).hom (TopCat.I.homeomorph.{max uC vC uD vD}.symm t)
    exact (ConcreteCategory.congr_hom hNat
      (TopCat.I.homeomorph.{max uC vC uD vD}.symm t)).symm
  have h := ((SSet.realizedNerveLiftHomeomorph_symm_edge_homotopic.{uC, vC, max uC vC uD vD}
    C k).map M).pathCast (hVertex x).symm (hVertex y).symm
  have hp :
      ((((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := C) (x := x) (y := y) k))).map HC.symm.continuous_toFun).cast
          (SSet.realizedNerveLiftHomeomorph_symm_vertex.{uC, vC, max uC vC uD vD} C x).symm
          (SSet.realizedNerveLiftHomeomorph_symm_vertex.{uC, vC, max uC vC uD vD} C y).symm).map
            M.continuous).cast (hVertex x).symm (hVertex y).symm =
      (((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := C) (x := x) (y := y) k))).map
          (realizedNerveFunctorMap F).continuous).cast
            (realizedNerveFunctorMap_vertex F x).symm
            (realizedNerveFunctorMap_vertex F y).symm) := by
    apply Path.ext
    funext t
    exact (hRecipe _).symm
  have hq :
      (((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C))
          (x := ULiftHom.objUp (ULift.up x)) (y := ULiftHom.objUp (ULift.up y))
          (ULiftHom.up.map (ULift.upFunctor.map k))))).map M.continuous).cast
            (hVertex x).symm (hVertex y).symm) =
      (((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D))
          (x := ULiftHom.objUp (ULift.up (F.obj x)))
          (y := ULiftHom.objUp (ULift.up (F.obj y)))
          (ULiftHom.up.map (ULift.upFunctor.map (F.map k)))))).map HD.continuous_toFun).cast
            (SSet.realizedNerveLiftHomeomorph_vertex.{uD, vD, max uC vC uD vD} D (F.obj x)).symm
            (SSet.realizedNerveLiftHomeomorph_vertex.{uD, vD, max uC vC uD vD}
              D (F.obj y)).symm) := by
    apply Path.ext
    funext t
    exact congrArg HD (hCurve t)
  obtain ⟨H⟩ := h
  refine Path.Homotopic.trans ?_
    (SSet.realizedNerveLiftHomeomorph_edge_homotopic.{uD, vD, max uC vC uD vD} D (F.map k))
  exact ⟨Path.Homotopy.cast H hp hq⟩

/-- The actual mixed-world realization map retains the original mapped edge
up to a homotopy with its two derived vertex transports fixed. -/
public theorem realizedNerveFunctorMap_edge_homotopic
    (F : C ⥤ D) {x y : C} (k : x ⟶ y) :
    (((TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := C) (x := x) (y := y) k))).map
          (realizedNerveFunctorMap F).continuous).cast
            (realizedNerveFunctorMap_vertex F x).symm
            (realizedNerveFunctorMap_vertex F y).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (C := D) (x := F.obj x) (y := F.obj y) (F.map k)))) :=
  realizedNerveFunctorMap_edge_homotopic_computed F k


section SameFrameCalibration

universe uF vF

variable {A B : Type uF} [Category.{vF} A] [Category.{vF} B]

/-- At a common original category frame, the selected mixed-world map
is the original nerve realization. -/
public theorem realizedNerveFunctorMap_sameFrame (F : A ⥤ B) :
    realizedNerveFunctorMap.{uF, vF, uF, vF} F = (SSet.toTop.map (nerveMap F)).hom := by
  apply ContinuousMap.ext
  intro x
  let HC := SSet.realizedNerveLiftHomeomorph.{uF, vF, max uF vF} A
  let HD := SSet.realizedNerveLiftHomeomorph.{uF, vF, max uF vF} B
  let L := liftedFunctor.{uF, vF, uF, vF} F
  have hL : L = ULiftHom.down ⋙ (ULift.downFunctor ⋙ F ⋙ ULift.upFunctor) ⋙ ULiftHom.up := rfl
  have hN := SSet.realizedNerveLiftHomeomorph_functor_naturality.{uF, vF, max uF vF}
    F (HC.symm x)
  change HD (SSet.toTop.map (nerveMap L) (HC.symm x)) = SSet.toTop.map (nerveMap F) x
  exact (congrArg (fun J : ULiftHom.{max uF vF} (ULift.{max uF vF} A) ⥤
      ULiftHom.{max uF vF} (ULift.{max uF vF} B) =>
        HD (SSet.toTop.map (nerveMap J) (HC.symm x))) hL).trans
    (hN.trans (congrArg (SSet.toTop.map (nerveMap F)) (HC.apply_symm_apply x)))

end SameFrameCalibration

section PostcompositionFrame

universe uA vA uB vB

variable {A : Type uA} [Category.{vA} A]
  {B E : Type uB} [Category.{vB} B] [Category.{vB} E]

/-- A same-frame target functor composes with the actual mixed-world realization map. -/
public theorem realizedNerveFunctorMap_postcomp_sameFrame (F : A ⥤ B) (G : B ⥤ E) :
    realizedNerveFunctorMap (F ⋙ G) =
      (realizedNerveFunctorMap G).comp (realizedNerveFunctorMap F) := by
  rw [realizedNerveFunctorMap_sameFrame G]
  apply ContinuousMap.ext
  intro x
  let HA := SSet.realizedNerveLiftHomeomorph.{uA, vA, max uA vA uB vB} A
  let HB := SSet.realizedNerveLiftHomeomorph.{uB, vB, max uA vA uB vB} B
  let HE := SSet.realizedNerveLiftHomeomorph.{uB, vB, max uA vA uB vB} E
  let LF := liftedFunctor F
  let LFG := liftedFunctor (F ⋙ G)
  let LG :=
    (ULiftHomULiftCategory.equiv.{max uA vA uB vB, max uA vA uB vB, vB, uB} B).inverse ⋙
      G ⋙ (ULiftHomULiftCategory.equiv.{max uA vA uB vB, max uA vA uB vB, vB, uB} E).functor
  let z := HA.symm x
  have hFunctor : LFG = LF ⋙ LG := rfl
  have hNerve : nerveMap LFG = nerveMap LF ≫ nerveMap LG :=
    (congrArg nerveMap hFunctor).trans ((nerveMap_comp LF LG).symm)
  have hValue := ConcreteCategory.congr_hom
    (congrArg (fun f : nerve (ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} A)) ⟶
        nerve (ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} E)) =>
          SSet.toTop.map f) hNerve) z
  have hStep : HE (SSet.toTop.map (nerveMap LFG) z) =
      HE (SSet.toTop.map (nerveMap LG) (SSet.toTop.map (nerveMap LF) z)) := by
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using congrArg HE hValue
  have hLG : LG = ULiftHom.down ⋙ (ULift.downFunctor ⋙ G ⋙ ULift.upFunctor) ⋙ ULiftHom.up := rfl
  have hNat : HE (SSet.toTop.map (nerveMap LG) (SSet.toTop.map (nerveMap LF) z)) =
      SSet.toTop.map (nerveMap G) (HB (SSet.toTop.map (nerveMap LF) z)) :=
    (congrArg (fun J : ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} B) ⥤
        ULiftHom.{max uA vA uB vB} (ULift.{max uA vA uB vB} E) =>
          HE (SSet.toTop.map (nerveMap J) (SSet.toTop.map (nerveMap LF) z))) hLG).trans
      (SSet.realizedNerveLiftHomeomorph_functor_naturality.{uB, vB, max uA vA uB vB}
        G (SSet.toTop.map (nerveMap LF) z))
  change HE (SSet.toTop.map (nerveMap LFG) z) =
    SSet.toTop.map (nerveMap G) (HB (SSet.toTop.map (nerveMap LF) z))
  exact hStep.trans hNat

end PostcompositionFrame

section PrecompositionFrame

universe uA vA uE vE

variable {A B : Type uA} [Category.{vA} A] [Category.{vA} B]
  {E : Type uE} [Category.{vE} E]

/-- A same-frame source functor composes with the selected actual mixed-world map. -/
public theorem realizedNerveFunctorMap_precomp_sameFrame (F : A ⥤ B) (G : B ⥤ E) :
    realizedNerveFunctorMap (F ⋙ G) =
      (realizedNerveFunctorMap G).comp (realizedNerveFunctorMap F) := by
  rw [realizedNerveFunctorMap_sameFrame F]
  apply ContinuousMap.ext
  intro x
  let HA := SSet.realizedNerveLiftHomeomorph.{uA, vA, max uA vA uE vE} A
  let HB := SSet.realizedNerveLiftHomeomorph.{uA, vA, max uA vA uE vE} B
  let HE := SSet.realizedNerveLiftHomeomorph.{uE, vE, max uA vA uE vE} E
  let LG := liftedFunctor G
  let LFG := liftedFunctor (F ⋙ G)
  let LF :=
    (ULiftHomULiftCategory.equiv.{max uA vA uE vE, max uA vA uE vE, vA, uA} A).inverse ⋙
      F ⋙ (ULiftHomULiftCategory.equiv.{max uA vA uE vE, max uA vA uE vE, vA, uA} B).functor
  let z := HA.symm x
  have hFunctor : LFG = LF ⋙ LG := rfl
  have hNerve : nerveMap LFG = nerveMap LF ≫ nerveMap LG :=
    (congrArg nerveMap hFunctor).trans ((nerveMap_comp LF LG).symm)
  have hValue := ConcreteCategory.congr_hom
    (congrArg (fun f : nerve (ULiftHom.{max uA vA uE vE} (ULift.{max uA vA uE vE} A)) ⟶
        nerve (ULiftHom.{max uA vA uE vE} (ULift.{max uA vA uE vE} E)) =>
          SSet.toTop.map f) hNerve) z
  have hStep : HE (SSet.toTop.map (nerveMap LFG) z) =
      HE (SSet.toTop.map (nerveMap LG) (SSet.toTop.map (nerveMap LF) z)) := by
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using congrArg HE hValue
  have hLF : LF = ULiftHom.down ⋙ (ULift.downFunctor ⋙ F ⋙ ULift.upFunctor) ⋙ ULiftHom.up := rfl
  have hNat : HB (SSet.toTop.map (nerveMap LF) z) = SSet.toTop.map (nerveMap F) x :=
    (congrArg (fun J : ULiftHom.{max uA vA uE vE} (ULift.{max uA vA uE vE} A) ⥤
        ULiftHom.{max uA vA uE vE} (ULift.{max uA vA uE vE} B) =>
          HB (SSet.toTop.map (nerveMap J) z)) hLF).trans
      ((SSet.realizedNerveLiftHomeomorph_functor_naturality.{uA, vA, max uA vA uE vE} F z).trans
        (congrArg (SSet.toTop.map (nerveMap F)) (HA.apply_symm_apply x)))
  have hMiddle : HB.symm (SSet.toTop.map (nerveMap F) x) = SSet.toTop.map (nerveMap LF) z :=
    (congrArg HB.symm hNat).symm.trans (HB.symm_apply_apply _)
  change HE (SSet.toTop.map (nerveMap LFG) z) =
    HE (SSet.toTop.map (nerveMap LG) (HB.symm (SSet.toTop.map (nerveMap F) x)))
  exact hStep.trans (congrArg (fun t => HE (SSet.toTop.map (nerveMap LG) t)) hMiddle).symm

end PrecompositionFrame


section ActualNaturalTransformation

private def liftedNatTrans {F G : C ⥤ D} (alpha : F ⟶ G) :
    liftedFunctor F ⟶ liftedFunctor G :=
  Functor.whiskerLeft
    (ULiftHomULiftCategory.equiv.{max uC vC uD vD, max uC vC uD vD, vC, uC} C).inverse
    (Functor.whiskerRight alpha
      (ULiftHomULiftCategory.equiv.{max uC vC uD vD, max uC vC uD vD, vD, uD} D).functor)

/-- Realize the actual natural transformation on both original carriers,
using only the existing internal category lifts and their homeomorphisms. -/
public def realizedNerveFunctorMapHomotopy {F G : C ⥤ D} (alpha : F ⟶ G) :
    ContinuousMap.Homotopy (realizedNerveFunctorMap F) (realizedNerveFunctorMap G) := by
  let HC := SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD} C
  let HD := SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD} D
  let LF := liftedFunctor F
  let LG := liftedFunctor G
  let A := liftedNatTrans alpha
  let H := SSet.realizeHomotopy
    (nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C)))
    (nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D)))
    (nerveMap LF) (nerveMap LG) (NatTrans.nerveHomotopy A)
  let K := (ContinuousMap.Homotopy.refl HD.toHomotopyEquiv.toFun).comp
    (H.compContinuousMap HC.symm.toHomotopyEquiv.toFun)
  exact K.cast rfl rfl

/-- The original vertex trace is homotopic to the actual component edge,
with both endpoints transported only through the original vertex equations. -/
public theorem realizedNerveFunctorMapHomotopy_vertex {F G : C ⥤ D}
    (alpha : F ⟶ G) (x : C) :
    (((realizedNerveFunctorMapHomotopy alpha).evalAt
      (SSet.realizedVertex (X := nerve C) (ComposableArrows.mk₀ x))).cast
        (realizedNerveFunctorMap_vertex F x).symm
        (realizedNerveFunctorMap_vertex G x).symm).Homotopic
      (TopCat.pathEquiv (SSet.realizedEdgePath (nerve.edgeMk (alpha.app x)))) := by
  let HC := SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD} C
  let HD := SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD} D
  let LF := liftedFunctor F
  let LG := liftedFunctor G
  let A := liftedNatTrans alpha
  let xc : ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C) :=
    ULiftHom.objUp (ULift.up x)
  let vc := SSet.realizedVertex (X := nerve C) (ComposableArrows.mk₀ x)
  let vl := SSet.realizedVertex
    (X := nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C)))
    (ComposableArrows.mk₀ xc)
  let H := SSet.realizeHomotopy
    (nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} C)))
    (nerve (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D)))
    (nerveMap LF) (nerveMap LG) (NatTrans.nerveHomotopy A)
  let ea := nerve.edgeMk.{max uC vC uD vD, max uC vC uD vD}
    (C := ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D))
    (x := LF.obj xc) (y := LG.obj xc) (A.app xc)
  let el := nerve.edgeMk.{max uC vC uD vD, max uC vC uD vD}
    (C := ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D))
    (x := ULiftHom.objUp (ULift.up (F.obj x)))
    (y := ULiftHom.objUp (ULift.up (G.obj x)))
    (ULiftHom.up.map (ULift.upFunctor.map (alpha.app x)))
  have hApp : A.app xc = (ULift.up (alpha.app x) : LF.obj xc ⟶ LG.obj xc) := rfl
  have hEdge : ea.edge = el.edge :=
    congrArg (fun f : LF.obj xc ⟶ LG.obj xc => ComposableArrows.mk₁ f) hApp
  have hHom : (SSet.realizedEdgePath ea).hom = (SSet.realizedEdgePath el).hom :=
    (SSet.realizedEdgePath_hom ea).trans
      ((congrArg (fun z :
          (nerve.{max uC vC uD vD, max uC vC uD vD}
            (ULiftHom.{max uC vC uD vD} (ULift.{max uC vC uD vD} D))) _⦋1⦌ =>
        SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.toTop.map (SSet.yonedaEquiv.symm z)) hEdge).trans
          (SSet.realizedEdgePath_hom el).symm)
  have hEval := SSet.realizeHomotopy_nerveHomotopy_evalAt_polymorphic A xc
  have hTransport (t : unitInterval) :
      realizedNerveFunctorMapHomotopy alpha (t, vc) = HD (H (t, vl)) := by
    change HD (H (t, HC.symm vc)) = HD (H (t, vl))
    exact congrArg (fun z => HD (H (t, z)))
      (SSet.realizedNerveLiftHomeomorph_symm_vertex.{uC, vC, max uC vC uD vD} C x)
  have hPath :
      (((realizedNerveFunctorMapHomotopy alpha).evalAt vc).cast
        (realizedNerveFunctorMap_vertex F x).symm
        (realizedNerveFunctorMap_vertex G x).symm) =
      (((TopCat.pathEquiv (SSet.realizedEdgePath el)).map HD.continuous_toFun).cast
        (SSet.realizedNerveLiftHomeomorph_vertex.{uD, vD, max uC vC uD vD} D (F.obj x)).symm
        (SSet.realizedNerveLiftHomeomorph_vertex.{uD, vD, max uC vC uD vD} D (G.obj x)).symm) := by
    apply Path.ext
    funext t
    have hValue : H (t, vl) =
        (SSet.realizedEdgePath ea).hom (TopCat.I.homeomorph.{max uC vC uD vD}.symm t) :=
      congrArg (fun p => p t) hEval
    exact (hTransport t).trans
      ((congrArg HD hValue).trans
        (congrArg HD (ConcreteCategory.congr_hom hHom
          (TopCat.I.homeomorph.{max uC vC uD vD}.symm t))))
  obtain ⟨K⟩ :=
    SSet.realizedNerveLiftHomeomorph_edge_homotopic.{uD, vD, max uC vC uD vD} D (alpha.app x)
  exact ⟨Path.Homotopy.cast K hPath.symm rfl⟩

end ActualNaturalTransformation


private theorem realizedNerveFunctorMap_recipe_computed (F : C ⥤ D) :
    realizedNerveFunctorMap F =
      (SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD} D).toHomotopyEquiv.toFun.comp
        ((SSet.toTop.map (nerveMap
          ((ULiftHomULiftCategory.equiv.{max uC vC uD vD, max uC vC uD vD, vC, uC} C).inverse ⋙
            F ⋙
            (ULiftHomULiftCategory.equiv.{max uC vC uD vD, max uC vC uD vD, vD, uD}
              D).functor))).hom.comp
          (SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD}
            C).symm.toHomotopyEquiv.toFun) :=
  rfl

/-- The entire original realization map uses its actual public lift equivalences and charts.
The four original category worlds are retained; the working lift is their actual maximum. -/
public theorem realizedNerveFunctorMap_recipe (F : C ⥤ D) :
    realizedNerveFunctorMap F =
      (SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD} D).toHomotopyEquiv.toFun.comp
        ((SSet.toTop.map (nerveMap
          ((ULiftHomULiftCategory.equiv.{max uC vC uD vD, max uC vC uD vD, vC, uC} C).inverse ⋙
            F ⋙
            (ULiftHomULiftCategory.equiv.{max uC vC uD vD, max uC vC uD vD, vD, uD}
              D).functor))).hom.comp
          (SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD}
            C).symm.toHomotopyEquiv.toFun) :=
  realizedNerveFunctorMap_recipe_computed F

end CategoryTheory

end


noncomputable section

open scoped ContinuousMap Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe uUp vUp uE vE

namespace CategoryTheory

section OriginalCommonUpComposition

variable {A : Type (max uUp vUp)} [Category.{vUp} A]
  {B : Type uUp} [Category.{vUp} B]

/-- The SAME original upward object-level functor realizes as its actual
common-Hom chain map, on the complete original source and target carriers. -/
public theorem realizedNerveFunctorMap_commonUpFrame (F : B ⥤ A) :
    realizedNerveFunctorMap F =
      (SSet.toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F)).hom := by
  rw [realizedNerveFunctorMap_recipe]
  apply ContinuousMap.ext
  intro x
  let HB := SSet.realizedNerveLiftHomeomorph.{uUp, vUp, max uUp vUp} B
  let HA := SSet.realizedNerveLiftHomeomorph.{max uUp vUp, vUp, max uUp vUp} A
  let LF := (ULiftHomULiftCategory.equiv.{max uUp vUp, max uUp vUp} B).inverse ⋙ F ⋙
    (ULiftHomULiftCategory.equiv.{max uUp vUp, max uUp vUp} A).functor
  have hLF : LF = ULiftHom.down ⋙
      (ULift.downFunctor ⋙ F ⋙ ULift.upFunctor) ⋙ ULiftHom.up := by
    rfl
  have hNat :=
    SSet.realizedNerveLiftHomeomorph_commonUpFunctor_naturality.{uUp, vUp, 0} F (HB.symm x)
  change HA (SSet.toTop.map (nerveMap LF) (HB.symm x)) =
    SSet.toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F) x
  exact (congrArg
    (fun K : ULiftHom.{max uUp vUp} (ULift.{max uUp vUp} B) ⥤
      ULiftHom.{max uUp vUp} (ULift.{max uUp vUp} A) =>
        HA (SSet.toTop.map (nerveMap K) (HB.symm x))) hLF).trans
      (hNat.trans (congrArg (SSet.toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F))
        (HB.apply_symm_apply x)))

variable {E : Type uE} [Category.{vE} E]

/-- An arbitrary original mixed-world target map composes with the SAME
original upward common-Hom source map. The full working envelope is derived. -/
public theorem realizedNerveFunctorMap_precomp_commonUpFrame
    (F : B ⥤ A) (G : A ⥤ E) :
    realizedNerveFunctorMap (F ⋙ G) =
      (realizedNerveFunctorMap G).comp
        (SSet.toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F)).hom := by
  rw [realizedNerveFunctorMap_recipe (F ⋙ G), realizedNerveFunctorMap_recipe G]
  apply ContinuousMap.ext
  intro x
  let HB := SSet.realizedNerveLiftHomeomorph.{uUp, vUp, max uUp vUp uE vE} B
  let HA := SSet.realizedNerveLiftHomeomorph.{max uUp vUp, vUp, max uUp vUp uE vE} A
  let HE := SSet.realizedNerveLiftHomeomorph.{uE, vE, max uUp vUp uE vE} E
  let LF := (ULiftHomULiftCategory.equiv.{max uUp vUp uE vE, max uUp vUp uE vE} B).inverse ⋙ F ⋙
    (ULiftHomULiftCategory.equiv.{max uUp vUp uE vE, max uUp vUp uE vE} A).functor
  let LG := (ULiftHomULiftCategory.equiv.{max uUp vUp uE vE, max uUp vUp uE vE} A).inverse ⋙ G ⋙
    (ULiftHomULiftCategory.equiv.{max uUp vUp uE vE, max uUp vUp uE vE} E).functor
  let LFG :=
    (ULiftHomULiftCategory.equiv.{max uUp vUp uE vE, max uUp vUp uE vE} B).inverse ⋙ (F ⋙ G) ⋙
    (ULiftHomULiftCategory.equiv.{max uUp vUp uE vE, max uUp vUp uE vE} E).functor
  let z := HB.symm x
  have hFunctor : LFG = LF ⋙ LG := by
    rfl
  have hNerve : nerveMap LFG = nerveMap LF ≫ nerveMap LG :=
    (congrArg nerveMap hFunctor).trans ((nerveMap_comp LF LG).symm)
  have hTop : SSet.toTop.map (nerveMap LFG) =
      SSet.toTop.map (nerveMap LF) ≫ SSet.toTop.map (nerveMap LG) :=
    (SSet.toTop.congr_map hNerve).trans (SSet.toTop.map_comp _ _)
  have hStep := congrArg HE ((ConcreteCategory.congr_hom hTop z).trans
    (TopCat.comp_app (SSet.toTop.map (nerveMap LF)) (SSet.toTop.map (nerveMap LG)) z))
  have hLF : LF = ULiftHom.down ⋙
      (ULift.downFunctor ⋙ F ⋙ ULift.upFunctor) ⋙ ULiftHom.up := by
    rfl
  have hNat : HA (SSet.toTop.map (nerveMap LF) z) =
      SSet.toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F) x :=
    (congrArg
      (fun K : ULiftHom.{max uUp vUp uE vE} (ULift.{max uUp vUp uE vE} B) ⥤
        ULiftHom.{max uUp vUp uE vE} (ULift.{max uUp vUp uE vE} A) =>
          HA (SSet.toTop.map (nerveMap K) z)) hLF).trans
      ((SSet.realizedNerveLiftHomeomorph_commonUpFunctor_naturality.{uUp, vUp, max uE vE} F z).trans
        (congrArg (SSet.toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F))
          (HB.apply_symm_apply x)))
  have hMiddle : HA.symm
      (SSet.toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F) x) =
        SSet.toTop.map (nerveMap LF) z :=
    (congrArg HA.symm hNat).symm.trans (HA.symm_apply_apply _)
  change HE (SSet.toTop.map (nerveMap LFG) z) =
    HE (SSet.toTop.map (nerveMap LG)
      (HA.symm (SSet.toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F) x)))
  exact hStep.trans
    ((congrArg (fun y => HE (SSet.toTop.map (nerveMap LG) y)) hMiddle).symm)

universe wUpRecipe

/-- The SAME original upward common-Hom map has its entire canonical recipe
in every larger working max-envelope, with both original charts retained. -/
public theorem realizedNerveFunctorMap_commonUp_recipe (F : B ⥤ A) :
    realizedNerveFunctorMap F =
      (SSet.realizedNerveLiftHomeomorph.{max uUp vUp, vUp, max uUp vUp wUpRecipe}
        A).toHomotopyEquiv.toFun.comp
        ((SSet.toTop.map (nerveMap
          ((ULiftHomULiftCategory.equiv.{max uUp vUp wUpRecipe, max uUp vUp wUpRecipe}
            B).inverse ⋙ F ⋙
            (ULiftHomULiftCategory.equiv.{max uUp vUp wUpRecipe, max uUp vUp wUpRecipe}
              A).functor))).hom.comp
          (SSet.realizedNerveLiftHomeomorph.{uUp, vUp, max uUp vUp wUpRecipe}
            B).symm.toHomotopyEquiv.toFun) := by
  apply ContinuousMap.ext
  intro x
  let HB := SSet.realizedNerveLiftHomeomorph.{uUp, vUp, max uUp vUp wUpRecipe} B
  let HA := SSet.realizedNerveLiftHomeomorph.{max uUp vUp, vUp, max uUp vUp wUpRecipe} A
  let LF :=
    (ULiftHomULiftCategory.equiv.{max uUp vUp wUpRecipe, max uUp vUp wUpRecipe} B).inverse ⋙ F ⋙
    (ULiftHomULiftCategory.equiv.{max uUp vUp wUpRecipe, max uUp vUp wUpRecipe} A).functor
  have hLF : LF = ULiftHom.down ⋙
      (ULift.downFunctor ⋙ F ⋙ ULift.upFunctor) ⋙ ULiftHom.up := by
    rfl
  have hNat :=
    SSet.realizedNerveLiftHomeomorph_commonUpFunctor_naturality.{uUp, vUp, wUpRecipe} F (HB.symm x)
  have hRight : HA (SSet.toTop.map (nerveMap LF) (HB.symm x)) =
      SSet.toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F) x :=
    (congrArg
      (fun K : ULiftHom.{max uUp vUp wUpRecipe} (ULift.{max uUp vUp wUpRecipe} B) ⥤
        ULiftHom.{max uUp vUp wUpRecipe} (ULift.{max uUp vUp wUpRecipe} A) =>
          HA (SSet.toTop.map (nerveMap K) (HB.symm x))) hLF).trans
      (hNat.trans (congrArg (SSet.toTop.map (nerveMapCommonHomUp.{uUp, vUp, 0} F))
        (HB.apply_symm_apply x)))
  have hLeft := congrArg
    (fun k : C(SSet.toTop.obj (nerve B), SSet.toTop.obj (nerve A)) => k x)
    (realizedNerveFunctorMap_commonUpFrame F)
  exact hLeft.trans hRight.symm

end OriginalCommonUpComposition

end CategoryTheory

end


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ContinuousMap Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe uC vC uD vD wExtra uSimplex

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]

private def originalLargerEnvelopeFunctor (F : C ⥤ D) :
    ULiftHom.{max uC vC uD vD wExtra} (ULift.{max uC vC uD vD wExtra} C) ⥤
      ULiftHom.{max uC vC uD vD wExtra} (ULift.{max uC vC uD vD wExtra} D) :=
  (ULiftHomULiftCategory.equiv.{max uC vC uD vD wExtra,
    max uC vC uD vD wExtra, vC, uC} C).inverse ⋙ F ⋙
    (ULiftHomULiftCategory.equiv.{max uC vC uD vD wExtra,
      max uC vC uD vD wExtra, vD, uD} D).functor

private def originalLargerEnvelopeRecipe (F : C ⥤ D) :
    C(SSet.toTop.obj (nerve C), SSet.toTop.obj (nerve D)) :=
  (SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD wExtra}
    D).toHomotopyEquiv.toFun.comp
      ((SSet.toTop.map (nerveMap
        (originalLargerEnvelopeFunctor.{uC, vC, uD, vD, wExtra} F))).hom.comp
        (SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD wExtra}
          C).symm.toHomotopyEquiv.toFun)

private theorem originalLargerEnvelopeRecipeSimplexComputed (F : C ⥤ D)
    (n : SimplexCategory) (σ : (nerve C).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    originalLargerEnvelopeRecipe.{uC, vC, uD, vD, wExtra} F
        (SSet.toTop.map (SSet.yonedaEquiv.symm σ)
          ((SSet.toTopSimplex.{max uC vC}.inv.app n)
            (ULift.up t : SimplexCategory.toTop.{max uC vC}.obj n))) =
      SSet.toTop.map (SSet.yonedaEquiv.symm (σ ⋙ F))
        ((SSet.toTopSimplex.{max uD vD}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{max uD vD}.obj n)) := by
  let LC := ULiftHom.{max uC vC uD vD wExtra} (ULift.{max uC vC uD vD wExtra} C)
  let LD := ULiftHom.{max uC vC uD vD wExtra} (ULift.{max uC vC uD vD wExtra} D)
  let UC : C ⥤ LC :=
    (ULiftHomULiftCategory.equiv.{max uC vC uD vD wExtra,
      max uC vC uD vD wExtra, vC, uC} C).functor
  let UD : D ⥤ LD :=
    (ULiftHomULiftCategory.equiv.{max uC vC uD vD wExtra,
      max uC vC uD vD wExtra, vD, uD} D).functor
  let L : LC ⥤ LD := originalLargerEnvelopeFunctor.{uC, vC, uD, vD, wExtra} F
  let σC : (nerve LC).obj (op n) := σ ⋙ UC
  let σD : (nerve LD).obj (op n) := (σ ⋙ F) ⋙ UD
  let HC := SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD wExtra} C
  let HD := SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD wExtra} D
  let y : SimplexCategory.toTop.{max uC vC uD vD wExtra}.obj n := ULift.up t
  let zC := SSet.toTop.map (SSet.yonedaEquiv.symm σC)
    ((SSet.toTopSimplex.{max uC vC uD vD wExtra}.inv.app n) y)
  let zD := SSet.toTop.map (SSet.yonedaEquiv.symm σD)
    ((SSet.toTopSimplex.{max uC vC uD vD wExtra}.inv.app n) y)
  let x := SSet.toTop.map (SSet.yonedaEquiv.symm σ)
    ((SSet.toTopSimplex.{max uC vC}.inv.app n)
      (ULift.up t : SimplexCategory.toTop.{max uC vC}.obj n))
  have hC : HC zC = x :=
    SSet.realizedNerveLiftHomeomorph_simplexValue.{uC, vC, max uC vC uD vD wExtra} C n σ t
  have hCInverse : HC.symm x = zC :=
    (congrArg HC.symm hC).symm.trans (HC.symm_apply_apply zC)
  have hD : HD zD = SSet.toTop.map (SSet.yonedaEquiv.symm (σ ⋙ F))
      ((SSet.toTopSimplex.{max uD vD}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{max uD vD}.obj n)) :=
    SSet.realizedNerveLiftHomeomorph_simplexValue.{uD, vD, max uC vC uD vD wExtra}
      D n (σ ⋙ F) t
  have hChain : σC ⋙ L = σD := by
    exact CategoryTheory.Functor.ext (fun i => rfl) (fun i j f => by
      change σD.map f = eqToHom (rfl : σD.obj i = σD.obj i) ≫ σD.map f ≫
        eqToHom (rfl : σD.obj j = σD.obj j)
      exact CategoryTheory.eq_conj_eqToHom (σD.map f))
  have hNerve : (nerveMap L).app (op n) σC = σD := hChain
  have hYoneda : SSet.yonedaEquiv.symm σC ≫ nerveMap L = SSet.yonedaEquiv.symm σD :=
    (SSet.yonedaEquiv_symm_comp σC (nerveMap L)).trans
      (congrArg (fun q : (nerve LD).obj (op n) => SSet.yonedaEquiv.symm q) hNerve)
  have hPoint : SSet.toTop.map (nerveMap L) zC = zD :=
    (TopCat.comp_app (SSet.toTop.map (SSet.yonedaEquiv.symm σC))
      (SSet.toTop.map (nerveMap L))
      ((SSet.toTopSimplex.{max uC vC uD vD wExtra}.inv.app n) y)).symm.trans
      ((ConcreteCategory.congr_hom
        (SSet.toTop.map_comp (SSet.yonedaEquiv.symm σC) (nerveMap L)).symm
        ((SSet.toTopSimplex.{max uC vC uD vD wExtra}.inv.app n) y)).trans
        (congrArg (fun f : SSet.stdSimplex.{max uC vC uD vD wExtra}.obj n ⟶ nerve LD =>
          SSet.toTop.map f ((SSet.toTopSimplex.{max uC vC uD vD wExtra}.inv.app n) y)) hYoneda))
  change HD (SSet.toTop.map (nerveMap L) (HC.symm x)) = _
  exact (congrArg (fun z => HD (SSet.toTop.map (nerveMap L) z)) hCInverse).trans
    ((congrArg HD hPoint).trans hD)

private theorem originalRealizationSimplexPresentationComputed
    (X : SSet.{uSimplex}) (x : SSet.toTop.obj X) :
    ∃ (n : SimplexCategory) (σ : X.obj (op n))
      (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))),
      SSet.toTop.map (SSet.yonedaEquiv.symm σ)
        ((SSet.toTopSimplex.{uSimplex}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{uSimplex}.obj n)) = x := by
  let c := Presheaf.tautologicalCocone' (C := SimplexCategory) (P := X)
  have hc : IsColimit c := Presheaf.isColimitTautologicalCocone' X
  have hcTop : IsColimit (SSet.toTop.mapCocone c) :=
    isColimitOfPreserves SSet.toTop hc
  have hcType : IsColimit ((SSet.toTop ⋙ forget TopCat).mapCocone c) :=
    isColimitOfPreserves (forget TopCat) hcTop
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hcType x
  let σ : X.obj (op j.left) := CategoryTheory.uliftYonedaEquiv j.hom
  let t : Convexity.StdSimplex ℝ (Fin (j.left.len + 1)) :=
    (SimplexCategory.toTopHomeo.{uSimplex} j.left) y
  have hσ : SSet.yonedaEquiv.symm σ = j.hom :=
    (SSet.yonedaEquiv).symm_apply_apply j.hom
  have hPoint : (SSet.toTopSimplex.{uSimplex}.inv.app j.left)
      (ULift.up t : SimplexCategory.toTop.{uSimplex}.obj j.left) = y := by
    have h := (SimplexCategory.toTopHomeo.{uSimplex} j.left).symm_apply_apply y
    change (SSet.toTopSimplex.{uSimplex}.inv.app j.left)
      (ULift.up t : SimplexCategory.toTop.{uSimplex}.obj j.left) = y at h
    exact h
  refine ⟨j.left, σ, t, ?_⟩
  exact (congrArg (fun f : SSet.stdSimplex.{uSimplex}.obj j.left ⟶ X =>
      SSet.toTop.map f ((SSet.toTopSimplex.{uSimplex}.inv.app j.left)
        (ULift.up t : SimplexCategory.toTop.{uSimplex}.obj j.left))) hσ).trans
    ((congrArg (SSet.toTop.map j.hom) hPoint).trans hy)

private theorem realizedNerveFunctorMapLargerRecipeComputed (F : C ⥤ D) :
    realizedNerveFunctorMap F =
      originalLargerEnvelopeRecipe.{uC, vC, uD, vD, wExtra} F := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨n, σ, t, hσ⟩ := originalRealizationSimplexPresentationComputed (nerve C) x
  let a := SSet.toTop.map (SSet.yonedaEquiv.symm σ)
    ((SSet.toTopSimplex.{max uC vC}.inv.app n)
      (ULift.up t : SimplexCategory.toTop.{max uC vC}.obj n))
  let b : SSet.toTop.obj (nerve D) := SSet.toTop.map
    ((SSet.yonedaEquiv (X := nerve D) (n := n)).symm (σ ⋙ F))
    ((SSet.toTopSimplex.{max uD vD}.inv.app n)
      (ULift.up t : SimplexCategory.toTop.{max uD vD}.obj n))
  have hDefault : realizedNerveFunctorMap F a = b :=
    originalLargerEnvelopeRecipeSimplexComputed.{uC, vC, uD, vD, 0} F n σ t
  have hLarger : originalLargerEnvelopeRecipe.{uC, vC, uD, vD, wExtra} F a = b :=
    originalLargerEnvelopeRecipeSimplexComputed.{uC, vC, uD, vD, wExtra} F n σ t
  exact (congrArg (realizedNerveFunctorMap F) hσ).symm.trans
    (hDefault.trans (hLarger.symm.trans
      (congrArg (originalLargerEnvelopeRecipe.{uC, vC, uD, vD, wExtra} F) hσ)))

/-- The SAME original mixed-world functor map has its whole canonical recipe
in every larger working envelope, retaining all four original category worlds. -/
public theorem realizedNerveFunctorMap_larger_recipe (F : C ⥤ D) :
    realizedNerveFunctorMap F =
      (SSet.realizedNerveLiftHomeomorph.{uD, vD, max uC vC uD vD wExtra}
        D).toHomotopyEquiv.toFun.comp
        ((SSet.toTop.map (nerveMap
          ((ULiftHomULiftCategory.equiv.{max uC vC uD vD wExtra,
            max uC vC uD vD wExtra, vC, uC} C).inverse ⋙ F ⋙
            (ULiftHomULiftCategory.equiv.{max uC vC uD vD wExtra,
              max uC vC uD vD wExtra, vD, uD} D).functor))).hom.comp
          (SSet.realizedNerveLiftHomeomorph.{uC, vC, max uC vC uD vD wExtra}
            C).symm.toHomotopyEquiv.toFun) :=
  realizedNerveFunctorMapLargerRecipeComputed.{uC, vC, uD, vD, wExtra} F

end CategoryTheory

end


/-!
# Every original point of the whole mixed realized natural-transformation family

This proper owned value retains the actual original HC/HD charts, lifted
functors, whiskered natural transformation and whole realized cylinder.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContinuousMap Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe uCWhole vCWhole uDWhole vDWhole

namespace CategoryTheory

variable {C : Type uCWhole} [Category.{vCWhole} C]
  {D : Type uDWhole} [Category.{vDWhole} D]

private theorem originalMixedFunctorHomotopyWholeValue
    {F G : C ⥤ D} (alpha : F ⟶ G) (t : unitInterval)
    (x : SSet.toTop.obj (nerve C)) :
    realizedNerveFunctorMapHomotopy alpha (t, x) =
      (SSet.realizedNerveLiftHomeomorph.{uDWhole, vDWhole,
        max uCWhole vCWhole uDWhole vDWhole} D)
        (SSet.realizeHomotopy
          (nerve (ULiftHom.{max uCWhole vCWhole uDWhole vDWhole}
            (ULift.{max uCWhole vCWhole uDWhole vDWhole} C)))
          (nerve (ULiftHom.{max uCWhole vCWhole uDWhole vDWhole}
            (ULift.{max uCWhole vCWhole uDWhole vDWhole} D)))
          (nerveMap
            ((ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
              max uCWhole vCWhole uDWhole vDWhole, vCWhole, uCWhole} C).inverse ⋙ F ⋙
              (ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
                max uCWhole vCWhole uDWhole vDWhole, vDWhole, uDWhole} D).functor))
          (nerveMap
            ((ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
              max uCWhole vCWhole uDWhole vDWhole, vCWhole, uCWhole} C).inverse ⋙ G ⋙
              (ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
                max uCWhole vCWhole uDWhole vDWhole, vDWhole, uDWhole} D).functor))
          (NatTrans.nerveHomotopy (Functor.whiskerLeft
            (ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
              max uCWhole vCWhole uDWhole vDWhole, vCWhole, uCWhole} C).inverse
            (Functor.whiskerRight alpha
              (ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
                max uCWhole vCWhole uDWhole vDWhole, vDWhole, uDWhole} D).functor)))
          (t, (SSet.realizedNerveLiftHomeomorph.{uCWhole, vCWhole,
            max uCWhole vCWhole uDWhole vDWhole} C).symm x)) := rfl

/-- Every interval/original-point value retains the SAME whole original lifted natural-transformation cylinder. -/
public theorem realizedNerveFunctorMapHomotopy_value
    {F G : C ⥤ D} (alpha : F ⟶ G) (t : unitInterval)
    (x : SSet.toTop.obj (nerve C)) :
    realizedNerveFunctorMapHomotopy alpha (t, x) =
      (SSet.realizedNerveLiftHomeomorph.{uDWhole, vDWhole,
        max uCWhole vCWhole uDWhole vDWhole} D)
        (SSet.realizeHomotopy
          (nerve (ULiftHom.{max uCWhole vCWhole uDWhole vDWhole}
            (ULift.{max uCWhole vCWhole uDWhole vDWhole} C)))
          (nerve (ULiftHom.{max uCWhole vCWhole uDWhole vDWhole}
            (ULift.{max uCWhole vCWhole uDWhole vDWhole} D)))
          (nerveMap
            ((ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
              max uCWhole vCWhole uDWhole vDWhole, vCWhole, uCWhole} C).inverse ⋙ F ⋙
              (ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
                max uCWhole vCWhole uDWhole vDWhole, vDWhole, uDWhole} D).functor))
          (nerveMap
            ((ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
              max uCWhole vCWhole uDWhole vDWhole, vCWhole, uCWhole} C).inverse ⋙ G ⋙
              (ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
                max uCWhole vCWhole uDWhole vDWhole, vDWhole, uDWhole} D).functor))
          (NatTrans.nerveHomotopy (Functor.whiskerLeft
            (ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
              max uCWhole vCWhole uDWhole vDWhole, vCWhole, uCWhole} C).inverse
            (Functor.whiskerRight alpha
              (ULiftHomULiftCategory.equiv.{max uCWhole vCWhole uDWhole vDWhole,
                max uCWhole vCWhole uDWhole vDWhole, vDWhole, uDWhole} D).functor)))
          (t, (SSet.realizedNerveLiftHomeomorph.{uCWhole, vCWhole,
            max uCWhole vCWhole uDWhole vDWhole} C).symm x)) :=
  originalMixedFunctorHomotopyWholeValue alpha t x

end CategoryTheory

end


/-!
# Whole original downward common-Hom realization value

The SAME original mixed realized functor map is the original downward
common-Hom chain map. Its original simplex presentation and larger-envelope
simplex values prove this on every original point, with no new maps/charts.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ContinuousMap Simplicial

attribute [local instance] CategoryTheory.uliftCategory

universe uDown vDown

namespace CategoryTheory

variable {A : Type (max uDown vDown)} [Category.{vDown} A]
  {B : Type uDown} [Category.{vDown} B]

private theorem originalCommonDownMapWholeValue (F : A ⥤ B) :
    realizedNerveFunctorMap F =
      (SSet.toTop.map (nerveMapCommonHom.{uDown, vDown, 0} F)).hom := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨n, sigma, t, hSigma⟩ := originalRealizationSimplexPresentationComputed (nerve A) x
  let a := SSet.toTop.map (SSet.yonedaEquiv.symm sigma)
    ((SSet.toTopSimplex.{max uDown vDown}.inv.app n)
      (ULift.up t : SimplexCategory.toTop.{max uDown vDown}.obj n))
  let b : SSet.toTop.obj (nerve B) := SSet.toTop.map
    ((SSet.yonedaEquiv (X := nerve B) (n := n)).symm (sigma ⋙ F))
    ((SSet.toTopSimplex.{max uDown vDown}.inv.app n)
      (ULift.up t : SimplexCategory.toTop.{max uDown vDown}.obj n))
  let M := nerveMapCommonHom.{uDown, vDown, 0} F
  let s := (SSet.toTopSimplex.{max uDown vDown}.inv.app n)
    (ULift.up t : SimplexCategory.toTop.{max uDown vDown}.obj n)
  have hActual : realizedNerveFunctorMap F a = b :=
    originalLargerEnvelopeRecipeSimplexComputed.{max uDown vDown, vDown,
      uDown, vDown, 0} F n sigma t
  have hChain : M.app (op n) sigma = sigma ⋙ F := rfl
  have hYoneda : SSet.yonedaEquiv.symm sigma ≫ M =
      SSet.yonedaEquiv.symm (sigma ⋙ F) :=
    (SSet.yonedaEquiv_symm_comp sigma M).trans
      (congrArg (fun q : (nerve B).obj (op n) => SSet.yonedaEquiv.symm q) hChain)
  have hOriginal : SSet.toTop.map M a = b :=
    (TopCat.comp_app (SSet.toTop.map (SSet.yonedaEquiv.symm sigma))
      (SSet.toTop.map M) s).symm.trans
        ((ConcreteCategory.congr_hom
          (SSet.toTop.map_comp (SSet.yonedaEquiv.symm sigma) M).symm s).trans
            (ConcreteCategory.congr_hom (congrArg SSet.toTop.map hYoneda) s))
  exact (congrArg (realizedNerveFunctorMap F) hSigma).symm.trans
    (hActual.trans (hOriginal.symm.trans (congrArg (SSet.toTop.map M) hSigma)))

/-- The SAME original mixed map retains its actual whole downward common-Hom realization recipe. -/
public theorem realizedNerveFunctorMap_commonDownFrame (F : A ⥤ B) :
    realizedNerveFunctorMap F =
      (SSet.toTop.map (nerveMapCommonHom.{uDown, vDown, 0} F)).hom :=
  originalCommonDownMapWholeValue F

end CategoryTheory

end
