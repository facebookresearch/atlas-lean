/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.Limits
public import MathlibExt.Topology.Category.CGWH.Point
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Based strict fibers in CGWH

This file defines strict fibers of native CGWH maps over chosen points.  It
also packages based arrows, their defining cospans, strict fibers, and the two
strict projections functorially.  The construction is independent of any
model-category structure or chosen homotopy pullback.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits

namespace CGWH

/-- The cospan defining the fiber of `f` over the chosen point `b`. -/
noncomputable def basedFiberCospan
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    WalkingCospan ⥤ CGWH.{u, v} :=
  cospan f b

/-- The strict fiber of `f` over the chosen point `b`. -/
noncomputable abbrev strictFiber
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) : CGWH.{u, v} :=
  pullback f b

/-- The strict fiber projects to the total space. -/
noncomputable abbrev strictFiberToTotal
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    strictFiber f b ⟶ E :=
  pullback.fst f b

/-- The strict fiber projects to the point object. -/
noncomputable abbrev strictFiberToPoint
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    strictFiber f b ⟶ CGWH.point.{u, v} :=
  pullback.snd f b

/-- The two projections of the strict fiber satisfy the pullback equation. -/
theorem strictFiber_condition
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    strictFiberToTotal f b ≫ f = strictFiberToPoint f b ≫ b :=
  pullback.condition

/-- A lift of the chosen basepoint to the total space determines a point of
the strict fiber. -/
noncomputable def strictFiberPoint
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (he : e ≫ f = b) :
    CGWH.point.{u, v} ⟶ strictFiber f b :=
  pullback.lift e (𝟙 _) (by simpa using he)

/-- The total-space projection of the supplied strict-fiber point. -/
theorem strictFiberPoint_toTotal
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (he : e ≫ f = b) :
    strictFiberPoint f b e he ≫ strictFiberToTotal f b = e :=
  pullback.lift_fst _ _ _

/-- The point projection of the supplied strict-fiber point. -/
theorem strictFiberPoint_toPoint
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B)
    (e : CGWH.point.{u, v} ⟶ E) (he : e ≫ f = b) :
    strictFiberPoint f b e he ≫ strictFiberToPoint f b = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- A compatible square and chosen-point equation induce a map of based
fiber cospans. -/
noncomputable def basedFiberCospanMap
    {E B E' B' : CGWH.{u, v}}
    {f : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {f' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    (eMap : E ⟶ E') (bMap : B ⟶ B')
    (hf : eMap ≫ f' = f ≫ bMap) (hb : b ≫ bMap = b') :
    basedFiberCospan f b ⟶ basedFiberCospan f' b' :=
  cospanHomMk (F := basedFiberCospan f b)
    (G := basedFiberCospan f' b') bMap eMap (𝟙 _)
    (by
      change f ≫ bMap = eMap ≫ f'
      exact hf.symm)
    (by
      change b ≫ bMap = 𝟙 CGWH.point.{u, v} ≫ b'
      simpa using hb)

private theorem basedFiberCospanMap_id
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    basedFiberCospanMap (f := f) (b := b) (f' := f) (b' := b)
        (𝟙 E) (𝟙 B) (by simp) (by simp) =
      𝟙 (basedFiberCospan f b) := by
  apply NatTrans.ext
  funext j
  rcases j with (_ | _ | _)
  · change 𝟙 B = 𝟙 B
    rfl
  · change 𝟙 E = 𝟙 E
    rfl
  · change 𝟙 CGWH.point.{u, v} = 𝟙 CGWH.point.{u, v}
    rfl

private theorem basedFiberCospanMap_comp
    {E B E' B' E'' B'' : CGWH.{u, v}}
    {f : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {f' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    {f'' : E'' ⟶ B''} {b'' : CGWH.point.{u, v} ⟶ B''}
    (eMap₁ : E ⟶ E') (bMap₁ : B ⟶ B')
    (hf₁ : eMap₁ ≫ f' = f ≫ bMap₁) (hb₁ : b ≫ bMap₁ = b')
    (eMap₂ : E' ⟶ E'') (bMap₂ : B' ⟶ B'')
    (hf₂ : eMap₂ ≫ f'' = f' ≫ bMap₂) (hb₂ : b' ≫ bMap₂ = b'') :
    basedFiberCospanMap eMap₁ bMap₁ hf₁ hb₁ ≫
        basedFiberCospanMap eMap₂ bMap₂ hf₂ hb₂ =
      basedFiberCospanMap (eMap₁ ≫ eMap₂) (bMap₁ ≫ bMap₂)
        (by
          rw [Category.assoc, hf₂, ← Category.assoc, hf₁,
            Category.assoc])
        (by rw [← Category.assoc, hb₁, hb₂]) := by
  apply NatTrans.ext
  funext j
  rcases j with (_ | _ | _)
  · change bMap₁ ≫ bMap₂ = bMap₁ ≫ bMap₂
    rfl
  · change eMap₁ ≫ eMap₂ = eMap₁ ≫ eMap₂
    rfl
  · change 𝟙 CGWH.point.{u, v} ≫ 𝟙 CGWH.point.{u, v} =
      𝟙 CGWH.point.{u, v}
    simp

/-- A compatible square and chosen-point equation induce a map of strict
fibers. -/
noncomputable def strictFiberMap
    {E B E' B' : CGWH.{u, v}}
    {f : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {f' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    (eMap : E ⟶ E') (bMap : B ⟶ B')
    (hf : eMap ≫ f' = f ≫ bMap) (hb : b ≫ bMap = b') :
    strictFiber f b ⟶ strictFiber f' b' :=
  lim.map (basedFiberCospanMap eMap bMap hf hb)

/-- A strict-fiber map commutes with projection to the total space. -/
theorem strictFiberMap_toTotal
    {E B E' B' : CGWH.{u, v}}
    {f : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {f' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    (eMap : E ⟶ E') (bMap : B ⟶ B')
    (hf : eMap ≫ f' = f ≫ bMap) (hb : b ≫ bMap = b') :
    strictFiberMap eMap bMap hf hb ≫ strictFiberToTotal f' b' =
      strictFiberToTotal f b ≫ eMap := by
  change lim.map (basedFiberCospanMap eMap bMap hf hb) ≫
      limit.π (basedFiberCospan f' b') WalkingCospan.left =
    limit.π (basedFiberCospan f b) WalkingCospan.left ≫ eMap
  rw [limit.map_π]
  rfl

/-- A strict-fiber map commutes with projection to the point object. -/
theorem strictFiberMap_toPoint
    {E B E' B' : CGWH.{u, v}}
    {f : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {f' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    (eMap : E ⟶ E') (bMap : B ⟶ B')
    (hf : eMap ≫ f' = f ≫ bMap) (hb : b ≫ bMap = b') :
    strictFiberMap eMap bMap hf hb ≫ strictFiberToPoint f' b' =
      strictFiberToPoint f b := by
  change lim.map (basedFiberCospanMap eMap bMap hf hb) ≫
      limit.π (basedFiberCospan f' b') WalkingCospan.right =
    limit.π (basedFiberCospan f b) WalkingCospan.right
  rw [limit.map_π]
  change limit.π (cospan f b) WalkingCospan.right ≫
      𝟙 CGWH.point.{u, v} = limit.π (cospan f b) WalkingCospan.right
  exact Category.comp_id _

/-- Strict-fiber base change along the identity square is the identity. -/
theorem strictFiberMap_id
    {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) :
    strictFiberMap (f := f) (b := b) (f' := f) (b' := b)
      (𝟙 E) (𝟙 B) (by simp) (by simp) = 𝟙 _ := by
  change lim.map
      (basedFiberCospanMap (f := f) (b := b) (f' := f) (b' := b)
        (𝟙 E) (𝟙 B) (by simp) (by simp)) = 𝟙 _
  rw [basedFiberCospanMap_id]
  exact (lim : (WalkingCospan ⥤ CGWH.{u, v}) ⥤ CGWH.{u, v}).map_id _

/-- Strict-fiber base change respects source-first composition. -/
theorem strictFiberMap_comp
    {E B E' B' E'' B'' : CGWH.{u, v}}
    {f : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {f' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    {f'' : E'' ⟶ B''} {b'' : CGWH.point.{u, v} ⟶ B''}
    (eMap₁ : E ⟶ E') (bMap₁ : B ⟶ B')
    (hf₁ : eMap₁ ≫ f' = f ≫ bMap₁) (hb₁ : b ≫ bMap₁ = b')
    (eMap₂ : E' ⟶ E'') (bMap₂ : B' ⟶ B'')
    (hf₂ : eMap₂ ≫ f'' = f' ≫ bMap₂) (hb₂ : b' ≫ bMap₂ = b'') :
    strictFiberMap eMap₁ bMap₁ hf₁ hb₁ ≫
        strictFiberMap eMap₂ bMap₂ hf₂ hb₂ =
      strictFiberMap (eMap₁ ≫ eMap₂) (bMap₁ ≫ bMap₂)
        (by
          rw [Category.assoc, hf₂, ← Category.assoc, hf₁,
            Category.assoc])
        (by rw [← Category.assoc, hb₁, hb₂]) := by
  change lim.map (basedFiberCospanMap eMap₁ bMap₁ hf₁ hb₁) ≫
      lim.map (basedFiberCospanMap eMap₂ bMap₂ hf₂ hb₂) =
    lim.map (basedFiberCospanMap (eMap₁ ≫ eMap₂) (bMap₁ ≫ bMap₂)
      (by
        rw [Category.assoc, hf₂, ← Category.assoc, hf₁,
          Category.assoc])
      (by rw [← Category.assoc, hb₁, hb₂]))
  rw [← lim.map_comp, basedFiberCospanMap_comp]

/-- Strict-fiber base change carries a compatible supplied point to the
target supplied point. -/
theorem strictFiberPoint_naturality
    {E B E' B' : CGWH.{u, v}}
    {f : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
    {f' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
    (eMap : E ⟶ E') (bMap : B ⟶ B')
    (hf : eMap ≫ f' = f ≫ bMap) (hb : b ≫ bMap = b')
    (e : CGWH.point.{u, v} ⟶ E) (he : e ≫ f = b)
    (e' : CGWH.point.{u, v} ⟶ E') (he' : e' ≫ f' = b')
    (heMap : e ≫ eMap = e') :
    strictFiberPoint f b e he ≫ strictFiberMap eMap bMap hf hb =
      strictFiberPoint f' b' e' he' := by
  apply pullback.hom_ext
  · rw [Category.assoc, strictFiberMap_toTotal, ← Category.assoc,
      strictFiberPoint_toTotal, heMap, strictFiberPoint_toTotal]
  · rw [Category.assoc, strictFiberMap_toPoint,
      strictFiberPoint_toPoint, strictFiberPoint_toPoint]

/-- A CGWH arrow equipped with a chosen point in its target. -/
abbrev BasedArrow :=
  StructuredArrow CGWH.point.{u, v}
    (Arrow.rightFunc : Arrow CGWH.{u, v} ⥤ CGWH.{u, v})

/-- Construct a based arrow from its map and chosen target point. -/
noncomputable def BasedArrow.mk {E B : CGWH.{u, v}} (f : E ⟶ B)
    (b : CGWH.point.{u, v} ⟶ B) : BasedArrow.{u, v} :=
  StructuredArrow.mk
    (T := (Arrow.rightFunc : Arrow CGWH.{u, v} ⥤ CGWH.{u, v}))
    (Y := Arrow.mk f) b

/-- The total space of a based arrow. -/
abbrev BasedArrow.total (F : BasedArrow.{u, v}) : CGWH.{u, v} :=
  F.right.left

/-- The base space of a based arrow. -/
abbrev BasedArrow.base (F : BasedArrow.{u, v}) : CGWH.{u, v} :=
  F.right.right

/-- The underlying map of a based arrow. -/
abbrev BasedArrow.map (F : BasedArrow.{u, v}) : F.total ⟶ F.base :=
  F.right.hom

/-- The chosen point of the base of a based arrow. -/
abbrev BasedArrow.point
    (F : BasedArrow.{u, v}) : CGWH.point.{u, v} ⟶ F.base :=
  F.hom

/-- Construct a morphism of based arrows from a compatible square and
chosen-point equation. -/
noncomputable def BasedArrow.homMk {F G : BasedArrow.{u, v}}
    (eMap : F.total ⟶ G.total) (bMap : F.base ⟶ G.base)
    (hf : eMap ≫ G.map = F.map ≫ bMap)
    (hb : F.point ≫ bMap = G.point) : F ⟶ G :=
  StructuredArrow.homMk (Arrow.homMk eMap bMap hf) (by
    change F.point ≫ bMap = G.point
    exact hb)

/-- The functor assigning to a based arrow its defining fiber cospan. -/
noncomputable def basedFiberCospanFunctor :
    BasedArrow.{u, v} ⥤ (WalkingCospan ⥤ CGWH.{u, v}) where
  obj F := basedFiberCospan F.map F.point
  map {F G} phi := basedFiberCospanMap
    phi.right.left phi.right.right (Arrow.w phi.right) (by
      change F.point ≫ phi.right.right = G.point
      exact StructuredArrow.w phi)
  map_id F := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · rfl
    · rfl
    · change 𝟙 CGWH.point.{u, v} = 𝟙 CGWH.point.{u, v}
      rfl
  map_comp phi psi := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · rfl
    · rfl
    · change 𝟙 CGWH.point.{u, v} =
        𝟙 CGWH.point.{u, v} ≫ 𝟙 CGWH.point.{u, v}
      simp

/-- The cospan functor has the expected object formula. -/
theorem basedFiberCospanFunctor_obj (F : BasedArrow.{u, v}) :
    basedFiberCospanFunctor.obj F = basedFiberCospan F.map F.point :=
  rfl

/-- The cospan functor has the expected map formula. -/
theorem basedFiberCospanFunctor_map
    {F G : BasedArrow.{u, v}} (phi : F ⟶ G) :
    basedFiberCospanFunctor.map phi = basedFiberCospanMap
      phi.right.left phi.right.right (Arrow.w phi.right) (by
        change F.point ≫ phi.right.right = G.point
        exact StructuredArrow.w phi) :=
  rfl

/-- The functor assigning to a based arrow its strict fiber. -/
noncomputable def strictFiberFunctor : BasedArrow.{u, v} ⥤ CGWH.{u, v} :=
  basedFiberCospanFunctor ⋙ lim

/-- The strict-fiber functor has the expected object formula. -/
theorem strictFiberFunctor_obj (F : BasedArrow.{u, v}) :
    strictFiberFunctor.obj F = strictFiber F.map F.point :=
  rfl

/-- The strict-fiber functor has the expected map formula. -/
theorem strictFiberFunctor_map
    {F G : BasedArrow.{u, v}} (phi : F ⟶ G) :
    strictFiberFunctor.map phi = strictFiberMap
      phi.right.left phi.right.right (Arrow.w phi.right) (by
        change F.point ≫ phi.right.right = G.point
        exact StructuredArrow.w phi) :=
  rfl

/-- The strict-fiber projections to total spaces form a natural
transformation. -/
noncomputable def strictFiberToTotalNatTrans :
    strictFiberFunctor.{u, v} ⟶
      StructuredArrow.proj CGWH.point.{u, v}
          (Arrow.rightFunc : Arrow CGWH.{u, v} ⥤ CGWH.{u, v}) ⋙
        Arrow.leftFunc where
  app F := strictFiberToTotal F.map F.point
  naturality {F G} phi := by
    let hf : phi.right.left ≫ G.map = F.map ≫ phi.right.right :=
      Arrow.w phi.right
    let hb : F.point ≫ phi.right.right = G.point := by
      exact StructuredArrow.w phi
    change strictFiberMap phi.right.left phi.right.right hf hb ≫
        strictFiberToTotal G.map G.point =
      strictFiberToTotal F.map F.point ≫ phi.right.left
    exact strictFiberMap_toTotal _ _ hf hb

/-- The strict-fiber projections to the point object form a natural
transformation. -/
noncomputable def strictFiberToPointNatTrans :
    strictFiberFunctor.{u, v} ⟶
      (Functor.const BasedArrow.{u, v}).obj CGWH.point.{u, v} where
  app F := strictFiberToPoint F.map F.point
  naturality {F G} phi := by
    let hf : phi.right.left ≫ G.map = F.map ≫ phi.right.right :=
      Arrow.w phi.right
    let hb : F.point ≫ phi.right.right = G.point := by
      exact StructuredArrow.w phi
    change strictFiberMap phi.right.left phi.right.right hf hb ≫
        strictFiberToPoint G.map G.point =
      strictFiberToPoint F.map F.point ≫ 𝟙 CGWH.point.{u, v}
    simpa using strictFiberMap_toPoint
      phi.right.left phi.right.right hf hb

/-- The total projection transformation has the expected component. -/
theorem strictFiberToTotalNatTrans_app (F : BasedArrow.{u, v}) :
    strictFiberToTotalNatTrans.app F = strictFiberToTotal F.map F.point :=
  rfl

/-- The point projection transformation has the expected component. -/
theorem strictFiberToPointNatTrans_app (F : BasedArrow.{u, v}) :
    strictFiberToPointNatTrans.app F = strictFiberToPoint F.map F.point :=
  rfl

end CGWH
