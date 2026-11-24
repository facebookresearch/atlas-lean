/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftHomEquiv
public import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic

@[expose] public section

/-!
# Full original fundamental-groupoid universe lift

Both original vertex and edge directions lift and lower the same full
native simplices. The original two-simplex composition relation is
retained. The canonical native universal groupoid constructor supplies
actual inverse functors with all original objects and arrows kept.
-/

noncomputable section

universe u v

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- The same native original edge lifted coefficientwise, retaining both complete original
endpoint equations. -/
def uliftEdge {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    (uliftFunctor.{v, u}.obj X).Edge (uliftObjEquiv.{u, v} X _ x) (uliftObjEquiv.{u, v} X _ y) where
  edge := uliftObjEquiv.{u, v} X _ e.edge
  src_eq := congrArg (uliftObjEquiv.{u, v} X _) e.src_eq
  tgt_eq := congrArg (uliftObjEquiv.{u, v} X _) e.tgt_eq

/-- The same full native original lifted edge lowered coefficientwise with its original
endpoints. -/
def downEdge {X : SSet.{u}} {x y : (uliftFunctor.{v, u}.obj X) _⦋0⦌}
    (e : (uliftFunctor.{v, u}.obj X).Edge x y) :
    X.Edge ((uliftObjEquiv.{u, v} X _).symm x) ((uliftObjEquiv.{u, v} X _).symm y) where
  edge := (uliftObjEquiv.{u, v} X _).symm e.edge
  src_eq := congrArg (uliftObjEquiv.{u, v} X _).symm e.src_eq
  tgt_eq := congrArg (uliftObjEquiv.{u, v} X _).symm e.tgt_eq

/-- The same full original composition simplex lifts with all its original face equations. -/
def uliftCompStruct {X : SSet.{u}} {x y z : X _⦋0⦌}
    {e : X.Edge x y} {f : X.Edge y z} {g : X.Edge x z} (h : Edge.CompStruct e f g) :
    Edge.CompStruct (uliftEdge.{u, v} e) (uliftEdge.{u, v} f) (uliftEdge.{u, v} g) where
  simplex := uliftObjEquiv.{u, v} X _ h.simplex
  d₂ := congrArg (uliftObjEquiv.{u, v} X _) h.d₂
  d₀ := congrArg (uliftObjEquiv.{u, v} X _) h.d₀
  d₁ := congrArg (uliftObjEquiv.{u, v} X _) h.d₁

/-- The same full original composition simplex lowers with all its original face equations. -/
def downCompStruct {X : SSet.{u}} {x y z : (uliftFunctor.{v, u}.obj X) _⦋0⦌}
    {e : (uliftFunctor.{v, u}.obj X).Edge x y} {f : (uliftFunctor.{v, u}.obj X).Edge y z}
    {g : (uliftFunctor.{v, u}.obj X).Edge x z} (h : Edge.CompStruct e f g) :
    Edge.CompStruct (downEdge e) (downEdge f) (downEdge g) where
  simplex := (uliftObjEquiv.{u, v} X _).symm h.simplex
  d₂ := congrArg (uliftObjEquiv.{u, v} X _).symm h.d₂
  d₀ := congrArg (uliftObjEquiv.{u, v} X _).symm h.d₀
  d₁ := congrArg (uliftObjEquiv.{u, v} X _).symm h.d₁

/-- The same full original coefficient lift acts on the native fundamental groupoid through
every original edge. -/
def fundamentalGroupoidULift (X : SSet.{u}) :
    FundamentalGroupoid X ⥤ FundamentalGroupoid (uliftFunctor.{v, u}.obj X) :=
  FundamentalGroupoid.desc (fun x => FundamentalGroupoid.mk (uliftObjEquiv.{u, v} X _ x))
    (fun e => FundamentalGroupoid.homMk (uliftEdge e))
    (fun h => (uliftCompStruct h).homMk_comp)

/-- The same full original coefficient lowering acts on the native lifted fundamental groupoid
through every original edge. -/
def fundamentalGroupoidDown (X : SSet.{u}) :
    FundamentalGroupoid (uliftFunctor.{v, u}.obj X) ⥤ FundamentalGroupoid X :=
  FundamentalGroupoid.desc (fun x => FundamentalGroupoid.mk ((uliftObjEquiv.{u, v} X _).symm x))
    (fun e => FundamentalGroupoid.homMk (downEdge e))
    (fun h => (downCompStruct h).homMk_comp)

private theorem fundamentalGroupoidULift_map_edge {X : SSet.{u}}
    {x y : X _⦋0⦌} (e : X.Edge x y) :
    (fundamentalGroupoidULift.{u, v} X).map (FundamentalGroupoid.homMk e) =
      FundamentalGroupoid.homMk (uliftEdge.{u, v} e) := by
  exact FundamentalGroupoid.desc_map_homMk _ _ (fun h => (uliftCompStruct h).homMk_comp) e

private theorem fundamentalGroupoidDown_map_edge {X : SSet.{u}}
    {x y : (uliftFunctor.{v, u}.obj X) _⦋0⦌}
    (e : (uliftFunctor.{v, u}.obj X).Edge x y) :
    (fundamentalGroupoidDown.{u, v} X).map (FundamentalGroupoid.homMk e) =
      FundamentalGroupoid.homMk (downEdge e) := by
  exact FundamentalGroupoid.desc_map_homMk _ _ (fun h => (downCompStruct h).homMk_comp) e

private theorem homMk_of_edge_eq {X : SSet.{u}} {a b x y : X _⦋0⦌}
    (e' : X.Edge a b) (e : X.Edge x y) (ha : a = x) (hb : b = y)
    (he : e'.edge = e.edge) :
    FundamentalGroupoid.homMk e' =
      eqToHom (congrArg FundamentalGroupoid.mk ha) ≫ FundamentalGroupoid.homMk e ≫
        eqToHom (congrArg FundamentalGroupoid.mk hb).symm := by
  subst a
  subst b
  have hEdge : e' = e := by
    apply Truncated.Edge.ext
    exact he
  subst e'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The lifted fundamental-groupoid functor retains the original vertex coefficient. -/
theorem fundamentalGroupoidULift_obj (X : SSet.{u}) (x : X _⦋0⦌) :
    (fundamentalGroupoidULift.{u, v} X).obj (FundamentalGroupoid.mk x) =
      FundamentalGroupoid.mk (uliftObjEquiv.{u, v} X _ x) := by
  rfl

/-- The inverse functor retains the original lowered vertex coefficient. -/
theorem fundamentalGroupoidDown_obj (X : SSet.{u})
    (x : (uliftFunctor.{v, u}.obj X) _⦋0⦌) :
    (fundamentalGroupoidDown.{u, v} X).obj (FundamentalGroupoid.mk x) =
      FundamentalGroupoid.mk ((uliftObjEquiv.{u, v} X _).symm x) := by
  rfl

/-- The lifted edge retains the same entire original one-simplex. -/
theorem uliftEdge_edge {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    (uliftEdge.{u, v} e).edge = uliftObjEquiv.{u, v} X _ e.edge := by
  rfl

/-- The full lifted groupoid map retains each edge, with its actual object identifications. -/
theorem fundamentalGroupoidULift_map_homMk {X : SSet.{u}}
    {x y : X _⦋0⦌} (e : X.Edge x y) :
    (fundamentalGroupoidULift.{u, v} X).map (FundamentalGroupoid.homMk e) =
      eqToHom (fundamentalGroupoidULift_obj X x) ≫
        FundamentalGroupoid.homMk (uliftEdge.{u, v} e) ≫
          eqToHom (fundamentalGroupoidULift_obj X y).symm := by
  exact (fundamentalGroupoidULift_map_edge e).trans (eq_conj_eqToHom _)

/-- The lifted source edge square retains its full map with the actual endpoint identifications. -/
theorem uliftEdge_map_homMk {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} (e : X.Edge x y) :
    FundamentalGroupoid.homMk ((uliftEdge.{u, v} e).map (uliftFunctor.map f)) =
      eqToHom (congrArg FundamentalGroupoid.mk (uliftObjEquiv_naturality.{u, v} f _ x)) ≫
        FundamentalGroupoid.homMk (uliftEdge.{u, v} (e.map f)) ≫
          eqToHom (congrArg FundamentalGroupoid.mk
            (uliftObjEquiv_naturality.{u, v} f _ y)).symm := by
  have hEdge : ((uliftEdge.{u, v} e).map (uliftFunctor.map f)).edge =
      (uliftEdge.{u, v} (e.map f)).edge := uliftObjEquiv_naturality.{u, v} f _ e.edge
  exact homMk_of_edge_eq ((uliftEdge.{u, v} e).map (uliftFunctor.map f))
    (uliftEdge.{u, v} (e.map f)) (uliftObjEquiv_naturality.{u, v} f _ x)
    (uliftObjEquiv_naturality.{u, v} f _ y) hEdge

/-- Both full original vertex and edge functors are inverse on the same original fundamental
groupoid. -/
theorem fundamentalGroupoidULift_comp_down (X : SSet.{u}) :
    fundamentalGroupoidULift.{u, v} X ⋙ fundamentalGroupoidDown X = 𝟭 (FundamentalGroupoid X) := by
  apply FundamentalGroupoid.functor_ext (X := X)
    (F := fundamentalGroupoidULift.{u, v} X ⋙ fundamentalGroupoidDown X)
    (G := 𝟭 (FundamentalGroupoid X)) (fun x =>
      congrArg FundamentalGroupoid.mk ((uliftObjEquiv.{u, v} X _).symm_apply_apply x))
  intro x y e
  have hEdge : (downEdge (uliftEdge.{u, v} e)).edge = e.edge :=
    (uliftObjEquiv.{u, v} X _).symm_apply_apply e.edge
  exact (congrArg (fundamentalGroupoidDown X).map (fundamentalGroupoidULift_map_edge e)).trans
    ((fundamentalGroupoidDown_map_edge (uliftEdge.{u, v} e)).trans
      (homMk_of_edge_eq (downEdge (uliftEdge.{u, v} e)) e
        ((uliftObjEquiv.{u, v} X _).symm_apply_apply x)
        ((uliftObjEquiv.{u, v} X _).symm_apply_apply y) hEdge))

/-- Both full original vertex and edge functors are inverse on the same lifted fundamental
groupoid. -/
theorem fundamentalGroupoidDown_comp_ulift (X : SSet.{u}) :
    fundamentalGroupoidDown.{u, v} X ⋙ fundamentalGroupoidULift X =
      𝟭 (FundamentalGroupoid (uliftFunctor.{v, u}.obj X)) := by
  apply FundamentalGroupoid.functor_ext (X := uliftFunctor.{v, u}.obj X)
    (F := fundamentalGroupoidDown.{u, v} X ⋙ fundamentalGroupoidULift X)
    (G := 𝟭 (FundamentalGroupoid (uliftFunctor.{v, u}.obj X))) (fun x =>
      congrArg FundamentalGroupoid.mk ((uliftObjEquiv.{u, v} X _).apply_symm_apply x))
  intro x y e
  have hEdge : (uliftEdge (downEdge.{u, v} e)).edge = e.edge :=
    (uliftObjEquiv.{u, v} X _).apply_symm_apply e.edge
  exact (congrArg (fundamentalGroupoidULift X).map (fundamentalGroupoidDown_map_edge e)).trans
    ((fundamentalGroupoidULift_map_edge (downEdge.{u, v} e)).trans
      (homMk_of_edge_eq (uliftEdge (downEdge.{u, v} e)) e
        ((uliftObjEquiv.{u, v} X _).apply_symm_apply x)
        ((uliftObjEquiv.{u, v} X _).apply_symm_apply y) hEdge))

end SSet
