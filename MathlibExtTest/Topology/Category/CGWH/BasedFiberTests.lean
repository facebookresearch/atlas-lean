/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.Topology.Category.CGWH.BasedFiber
public import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization

/-!
# Tests for neutral based strict fibers in CGWH
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace MathlibExtTest.CGWH.BasedFiberTests

section PublicSurface

#check @CGWH.basedFiberCospan.{u, v}
#check @CGWH.strictFiber.{u, v}
#check @CGWH.strictFiberToTotal.{u, v}
#check @CGWH.strictFiberToPoint.{u, v}
#check @CGWH.strictFiber_condition.{u, v}
#check @CGWH.strictFiberPoint.{u, v}
#check @CGWH.strictFiberPoint_toTotal.{u, v}
#check @CGWH.strictFiberPoint_toPoint.{u, v}
#check @CGWH.basedFiberCospanMap.{u, v}
#check @CGWH.strictFiberMap.{u, v}
#check @CGWH.strictFiberMap_toTotal.{u, v}
#check @CGWH.strictFiberMap_toPoint.{u, v}
#check @CGWH.strictFiberMap_id.{u, v}
#check @CGWH.strictFiberMap_comp.{u, v}
#check @CGWH.strictFiberPoint_naturality.{u, v}
#check CGWH.BasedArrow
#check @CGWH.BasedArrow.mk.{u, v}
#check @CGWH.BasedArrow.total.{u, v}
#check @CGWH.BasedArrow.base.{u, v}
#check @CGWH.BasedArrow.map.{u, v}
#check @CGWH.BasedArrow.point.{u, v}
#check @CGWH.BasedArrow.homMk.{u, v}
#check @CGWH.basedFiberCospanFunctor.{u, v}
#check @CGWH.basedFiberCospanFunctor_obj.{u, v}
#check @CGWH.basedFiberCospanFunctor_map.{u, v}
#check @CGWH.strictFiberFunctor.{u, v}
#check @CGWH.strictFiberFunctor_obj.{u, v}
#check @CGWH.strictFiberFunctor_map.{u, v}
#check @CGWH.strictFiberToTotalNatTrans.{u, v}
#check @CGWH.strictFiberToPointNatTrans.{u, v}
#check @CGWH.strictFiberToTotalNatTrans_app.{u, v}
#check @CGWH.strictFiberToPointNatTrans_app.{u, v}

end PublicSurface

section LimitsScopeOff

example : True := by
  fail_if_success
    let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : HasPullbacks CGWH.{u, v} := inferInstance
  trivial

end LimitsScopeOff

section LimitsScopeOn

open scoped CGWH.limits

#synth HasLimitsOfSize.{v, v} CGWH.{u, v}
#synth HasPullbacks CGWH.{u, v}

end LimitsScopeOn

section Cospan

variable {E B : CGWH.{u, v}} (f : E ⟶ B)
  (b : CGWH.point.{u, v} ⟶ B)

example : (CGWH.basedFiberCospan f b).obj WalkingCospan.one = B := rfl
example : (CGWH.basedFiberCospan f b).obj WalkingCospan.left = E := rfl
example : (CGWH.basedFiberCospan f b).obj WalkingCospan.right =
    CGWH.point.{u, v} := rfl
example : (CGWH.basedFiberCospan f b).map WalkingCospan.Hom.inl = f := rfl
example : (CGWH.basedFiberCospan f b).map WalkingCospan.Hom.inr = b := rfl

example : CGWH.strictFiber f b ⟶ E :=
  CGWH.strictFiberToTotal f b

example : CGWH.strictFiber f b ⟶ CGWH.point.{u, v} :=
  CGWH.strictFiberToPoint f b

example : CGWH.strictFiberToTotal f b ≫ f =
    CGWH.strictFiberToPoint f b ≫ b :=
  CGWH.strictFiber_condition f b

variable (e : CGWH.point.{u, v} ⟶ E) (he : e ≫ f = b)

example : CGWH.point.{u, v} ⟶ CGWH.strictFiber f b :=
  CGWH.strictFiberPoint f b e he

example : CGWH.strictFiberPoint f b e he ≫
      CGWH.strictFiberToTotal f b = e :=
  CGWH.strictFiberPoint_toTotal f b e he

example : CGWH.strictFiberPoint f b e he ≫
      CGWH.strictFiberToPoint f b = 𝟙 _ :=
  CGWH.strictFiberPoint_toPoint f b e he

end Cospan

section Square

variable {E B E' B' : CGWH.{u, v}}
  {f : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
  {f' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
  (eMap : E ⟶ E') (bMap : B ⟶ B')
  (hf : eMap ≫ f' = f ≫ bMap) (hb : b ≫ bMap = b')

example : (CGWH.basedFiberCospanMap eMap bMap hf hb).app
    WalkingCospan.one = bMap := rfl

example : (CGWH.basedFiberCospanMap eMap bMap hf hb).app
    WalkingCospan.left = eMap := rfl

example : (CGWH.basedFiberCospanMap eMap bMap hf hb).app
    WalkingCospan.right = 𝟙 _ := rfl

example : (CGWH.basedFiberCospan f b).map WalkingCospan.Hom.inl ≫
      (CGWH.basedFiberCospanMap eMap bMap hf hb).app WalkingCospan.one =
    (CGWH.basedFiberCospanMap eMap bMap hf hb).app WalkingCospan.left ≫
      (CGWH.basedFiberCospan f' b').map WalkingCospan.Hom.inl :=
  (CGWH.basedFiberCospanMap eMap bMap hf hb).naturality _

example : (CGWH.basedFiberCospan f b).map WalkingCospan.Hom.inr ≫
      (CGWH.basedFiberCospanMap eMap bMap hf hb).app WalkingCospan.one =
    (CGWH.basedFiberCospanMap eMap bMap hf hb).app WalkingCospan.right ≫
      (CGWH.basedFiberCospan f' b').map WalkingCospan.Hom.inr :=
  (CGWH.basedFiberCospanMap eMap bMap hf hb).naturality _

example : CGWH.strictFiber f b ⟶ CGWH.strictFiber f' b' :=
  CGWH.strictFiberMap eMap bMap hf hb

example : CGWH.strictFiberMap eMap bMap hf hb ≫
      CGWH.strictFiberToTotal f' b' =
    CGWH.strictFiberToTotal f b ≫ eMap :=
  CGWH.strictFiberMap_toTotal eMap bMap hf hb

example : CGWH.strictFiberMap eMap bMap hf hb ≫
      CGWH.strictFiberToPoint f' b' =
    CGWH.strictFiberToPoint f b :=
  CGWH.strictFiberMap_toPoint eMap bMap hf hb

variable (e : CGWH.point.{u, v} ⟶ E) (he : e ≫ f = b)
  (e' : CGWH.point.{u, v} ⟶ E') (he' : e' ≫ f' = b')
  (heMap : e ≫ eMap = e')

example : CGWH.strictFiberPoint f b e he ≫
      CGWH.strictFiberMap eMap bMap hf hb =
    CGWH.strictFiberPoint f' b' e' he' :=
  CGWH.strictFiberPoint_naturality eMap bMap hf hb e he e' he' heMap

end Square

section IdentityAndComposition

variable {E B E' B' E'' B'' : CGWH.{u, v}}
  {f : E ⟶ B} {b : CGWH.point.{u, v} ⟶ B}
  {f' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
  {f'' : E'' ⟶ B''} {b'' : CGWH.point.{u, v} ⟶ B''}
  (eMap₁ : E ⟶ E') (bMap₁ : B ⟶ B')
  (hf₁ : eMap₁ ≫ f' = f ≫ bMap₁) (hb₁ : b ≫ bMap₁ = b')
  (eMap₂ : E' ⟶ E'') (bMap₂ : B' ⟶ B'')
  (hf₂ : eMap₂ ≫ f'' = f' ≫ bMap₂) (hb₂ : b' ≫ bMap₂ = b'')

example : CGWH.strictFiberMap (f := f) (b := b) (f' := f) (b' := b)
      (𝟙 E) (𝟙 B) (by simp) (by simp) = 𝟙 _ :=
  CGWH.strictFiberMap_id f b

example : CGWH.strictFiberMap eMap₁ bMap₁ hf₁ hb₁ ≫
      CGWH.strictFiberMap eMap₂ bMap₂ hf₂ hb₂ =
    CGWH.strictFiberMap (eMap₁ ≫ eMap₂) (bMap₁ ≫ bMap₂)
      (by
        rw [Category.assoc, hf₂, ← Category.assoc, hf₁,
          Category.assoc])
      (by rw [← Category.assoc, hb₁, hb₂]) :=
  CGWH.strictFiberMap_comp eMap₁ bMap₁ hf₁ hb₁
    eMap₂ bMap₂ hf₂ hb₂

end IdentityAndComposition

section BasedArrow

variable {E B : CGWH.{u, v}} (f : E ⟶ B)
  (b : CGWH.point.{u, v} ⟶ B)

example : (CGWH.BasedArrow.mk f b).total = E := rfl
example : (CGWH.BasedArrow.mk f b).base = B := rfl
example : (CGWH.BasedArrow.mk f b).map = f := rfl
example : (CGWH.BasedArrow.mk f b).point = b := rfl

variable {E' B' : CGWH.{u, v}}
  {f' : E' ⟶ B'} {b' : CGWH.point.{u, v} ⟶ B'}
  (eMap : E ⟶ E') (bMap : B ⟶ B')
  (hf : eMap ≫ f' = f ≫ bMap) (hb : b ≫ bMap = b')

example : (CGWH.BasedArrow.homMk
    (F := CGWH.BasedArrow.mk f b) (G := CGWH.BasedArrow.mk f' b')
    eMap bMap hf hb).right.left = eMap := rfl

example : (CGWH.BasedArrow.homMk
    (F := CGWH.BasedArrow.mk f b) (G := CGWH.BasedArrow.mk f' b')
    eMap bMap hf hb).right.right = bMap := rfl

example : (CGWH.BasedArrow.mk f b).point ≫ bMap =
    (CGWH.BasedArrow.mk f' b').point :=
  StructuredArrow.w (CGWH.BasedArrow.homMk
    (F := CGWH.BasedArrow.mk f b) (G := CGWH.BasedArrow.mk f' b')
    eMap bMap hf hb)

end BasedArrow

section Functors

variable (F : CGWH.BasedArrow.{u, v})

example : CGWH.basedFiberCospanFunctor.obj F =
    CGWH.basedFiberCospan F.map F.point :=
  CGWH.basedFiberCospanFunctor_obj F

example : CGWH.strictFiberFunctor.obj F =
    CGWH.strictFiber F.map F.point :=
  CGWH.strictFiberFunctor_obj F

example : CGWH.strictFiberToTotalNatTrans.app F =
    CGWH.strictFiberToTotal F.map F.point :=
  CGWH.strictFiberToTotalNatTrans_app F

example : CGWH.strictFiberToPointNatTrans.app F =
    CGWH.strictFiberToPoint F.map F.point :=
  CGWH.strictFiberToPointNatTrans_app F

example : CGWH.basedFiberCospanFunctor.map (𝟙 F) = 𝟙 _ :=
  CGWH.basedFiberCospanFunctor.map_id F

example : CGWH.strictFiberFunctor.map (𝟙 F) = 𝟙 _ :=
  CGWH.strictFiberFunctor.map_id F

variable {F G H : CGWH.BasedArrow.{u, v}}
  (phi : F ⟶ G) (psi : G ⟶ H)

example : CGWH.basedFiberCospanFunctor.map (phi ≫ psi) =
    CGWH.basedFiberCospanFunctor.map phi ≫
      CGWH.basedFiberCospanFunctor.map psi :=
  CGWH.basedFiberCospanFunctor.map_comp phi psi

example : CGWH.strictFiberFunctor.map (phi ≫ psi) =
    CGWH.strictFiberFunctor.map phi ≫ CGWH.strictFiberFunctor.map psi :=
  CGWH.strictFiberFunctor.map_comp phi psi

example : CGWH.strictFiberFunctor.map phi ≫
      CGWH.strictFiberToTotalNatTrans.app G =
    CGWH.strictFiberToTotalNatTrans.app F ≫ phi.right.left :=
  CGWH.strictFiberToTotalNatTrans.naturality phi

example : CGWH.strictFiberFunctor.map phi ≫
      CGWH.strictFiberToPointNatTrans.app G =
    CGWH.strictFiberToPointNatTrans.app F ≫
      ((Functor.const CGWH.BasedArrow.{u, v}).obj
        CGWH.point.{u, v}).map phi :=
  CGWH.strictFiberToPointNatTrans.naturality phi

example : CGWH.basedFiberCospanFunctor.map phi =
    CGWH.basedFiberCospanMap phi.right.left phi.right.right
      (Arrow.w phi.right) (by
        change F.point ≫ phi.right.right = G.point
        exact StructuredArrow.w phi) :=
  CGWH.basedFiberCospanFunctor_map phi

example : CGWH.strictFiberFunctor.map phi =
    CGWH.strictFiberMap phi.right.left phi.right.right
      (Arrow.w phi.right) (by
        change F.point ≫ phi.right.right = G.point
        exact StructuredArrow.w phi) :=
  CGWH.strictFiberFunctor_map phi

end Functors

section RealizationShapedSquare

variable {X Y : SSet.{v}} (s : X ⟶ Y)
  (x : CGWH.point.{u, v} ⟶ SSet.toCGWH.{u, v}.obj X)
  (y : CGWH.point.{u, v} ⟶ SSet.toCGWH.{u, v}.obj Y)
  (hxy : x ≫ SSet.toCGWH.{u, v}.map s = y)

example :
    CGWH.strictFiber (𝟙 (SSet.toCGWH.{u, v}.obj X)) x ⟶
      CGWH.strictFiber (𝟙 (SSet.toCGWH.{u, v}.obj Y)) y :=
  CGWH.strictFiberMap
    (SSet.toCGWH.{u, v}.map s) (SSet.toCGWH.{u, v}.map s)
    (by simp) hxy

example :
    (CGWH.strictFiberFunctor.{u, v}).map
      (CGWH.BasedArrow.homMk
        (F := CGWH.BasedArrow.mk (𝟙 (SSet.toCGWH.{u, v}.obj X)) x)
        (G := CGWH.BasedArrow.mk (𝟙 (SSet.toCGWH.{u, v}.obj Y)) y)
        (SSet.toCGWH.{u, v}.map s) (SSet.toCGWH.{u, v}.map s)
        (by
          change SSet.toCGWH.{u, v}.map s ≫ 𝟙 _ =
            𝟙 _ ≫ SSet.toCGWH.{u, v}.map s
          simp)
        (by
          change x ≫ SSet.toCGWH.{u, v}.map s = y
          exact hxy)) =
      CGWH.strictFiberMap
        (f := 𝟙 (SSet.toCGWH.{u, v}.obj X)) (b := x)
        (f' := 𝟙 (SSet.toCGWH.{u, v}.obj Y)) (b' := y)
        (SSet.toCGWH.{u, v}.map s) (SSet.toCGWH.{u, v}.map s)
        (by simp) hxy :=
  CGWH.strictFiberFunctor_map _

end RealizationShapedSquare

section Universes

#check @CGWH.BasedArrow.{0, 0}
#check @CGWH.strictFiberFunctor.{0, 0}
#check @CGWH.strictFiberToTotalNatTrans.{0, 0}
#check @CGWH.BasedArrow.{1, 1}
#check @CGWH.strictFiberFunctor.{1, 1}
#check @CGWH.strictFiberToTotalNatTrans.{1, 1}
#check @CGWH.BasedArrow.{0, 1}
#check @CGWH.strictFiberFunctor.{0, 1}
#check @CGWH.strictFiberToTotalNatTrans.{0, 1}
#check @CGWH.BasedArrow.{1, 0}
#check @CGWH.strictFiberFunctor.{1, 0}
#check @CGWH.strictFiberToTotalNatTrans.{1, 0}

end Universes

section LimitsDeletion

open scoped CGWH.limits

attribute [-instance] CGWH.limits.instHasLimitsOfSize in
example : True := by
  fail_if_success
    let _ : HasPullbacks CGWH.{u, v} := inferInstance
  trivial

end LimitsDeletion

section ScopeTeardown

example : True := by
  fail_if_success
    let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} := inferInstance
  fail_if_success
    let _ : HasPullbacks CGWH.{u, v} := inferInstance
  trivial

end ScopeTeardown

section PrivacyAndNonclaims

#guard_msgs (error, substring := true) in
#check CGWH.basedFiberCospanMap_id

#guard_msgs (error, substring := true) in
#check CGWH.basedFiberCospanMap_comp

#guard_msgs (error, substring := true) in
#check CGWH.homotopyFiber

#guard_msgs (error, substring := true) in
#check CGWH.strictFiberToHomotopyFiber

#guard_msgs (error, substring := true) in
#check CGWH.modelCategory.strictFiberToHomotopyFiber_weakEquivalence

#guard_msgs (error, substring := true) in
#check CGWH.mappingPathFiber

end PrivacyAndNonclaims

#print axioms CGWH.basedFiberCospan
#print axioms CGWH.strictFiber_condition
#print axioms CGWH.strictFiberPoint
#print axioms CGWH.basedFiberCospanMap
#print axioms CGWH.strictFiberMap
#print axioms CGWH.strictFiberMap_id
#print axioms CGWH.strictFiberMap_comp
#print axioms CGWH.strictFiberPoint_naturality
#print axioms CGWH.BasedArrow.mk
#print axioms CGWH.BasedArrow.homMk
#print axioms CGWH.basedFiberCospanFunctor
#print axioms CGWH.strictFiberFunctor
#print axioms CGWH.strictFiberToTotalNatTrans
#print axioms CGWH.strictFiberToPointNatTrans

end MathlibExtTest.CGWH.BasedFiberTests
