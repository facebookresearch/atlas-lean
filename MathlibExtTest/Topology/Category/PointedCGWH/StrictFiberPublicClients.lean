/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/

import MathlibExt.Topology.Category.PointedCGWH.StrictFiber

/-!
# Full native pointed strict-fiber universal-property and map clients

Arbitrary actual pointed cones exercise both native lift legs and unique
factorization. The full two projection Arrow functors retain identity,
composition and naturality at general native universe combinations.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits

namespace PointedCGWH.StrictFiberPublicClients

open StrictFiberGeometry

example {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) (s : PullbackCone f (fromPoint Y)) :
    fiberLift f s ≫ fiberToTotal f = s.fst ∧ fiberLift f s ≫ fiberToPoint f = s.snd :=
  ⟨fiberLift_fst f s, fiberLift_snd f s⟩

example {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) (s : PullbackCone f (fromPoint Y))
    (m : s.pt ⟶ fiber f) (hm : m ≫ fiberToTotal f = s.fst)
    (hn : m ≫ fiberToPoint f = s.snd) : m = fiberLift f s := by
  apply PullbackCone.IsLimit.hom_ext (fiberConeIsLimit f)
  · exact hm.trans (fiberLift_fst f s).symm
  · exact hn.trans (fiberLift_snd f s).symm

example {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) (s : PullbackCone f (fromPoint Y)) :
    (fiberConeIsLimit f).lift s = fiberLift f s := by
  apply PullbackCone.IsLimit.hom_ext (fiberConeIsLimit f)
  · exact ((fiberConeIsLimit f).fac s WalkingCospan.left).trans (fiberLift_fst f s).symm
  · exact ((fiberConeIsLimit f).fac s WalkingCospan.right).trans (fiberLift_snd f s).symm

example {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) (s : PullbackCone f (fromPoint Y)) :
    s.pt.hom ≫ (fiberLift f s).right = (fiber f).hom :=
  Under.w (fiberLift f s)

example (F : Arrow PointedCGWH.{u, v}) :
    fiberFunctor.map (𝟙 F) = 𝟙 (fiber F.hom) :=
  fiberFunctor.map_id F

example {F G H : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) (r : G ⟶ H) :
    fiberFunctor.map (q ≫ r) = fiberMap q ≫ fiberMap r :=
  fiberFunctor.map_comp q r

example {F G H : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) (r : G ⟶ H) :
    (fiberToTotalArrowFunctor.map (q ≫ r)).left = fiberMap q ≫ fiberMap r ∧
      (fiberToTotalArrowFunctor.map (q ≫ r)).right = q.left ≫ r.left := by
  constructor
  · exact fiberFunctor.map_comp q r
  · rfl

example {F G H : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) (r : G ⟶ H) :
    (fiberToPointArrowFunctor.map (q ≫ r)).left = fiberMap q ≫ fiberMap r ∧
      (fiberToPointArrowFunctor.map (q ≫ r)).right = 𝟙 pointObject := by
  constructor
  · exact fiberFunctor.map_comp q r
  · rfl

example {F G H : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) (r : G ⟶ H) :
    (fiberFunctor.map q ≫ fiberFunctor.map r) ≫ fiberToTotal H.hom =
      fiberToTotal F.hom ≫ (q.left ≫ r.left) := by
  rw [← fiberFunctor.map_comp]
  change fiberMap (q ≫ r) ≫ fiberToTotal H.hom =
    fiberToTotal F.hom ≫ (q.left ≫ r.left)
  exact fiberMap_fst (q ≫ r)

example {F G H : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) (r : G ⟶ H) :
    (fiberFunctor.map q ≫ fiberFunctor.map r) ≫ fiberToPoint H.hom = fiberToPoint F.hom := by
  rw [← fiberFunctor.map_comp]
  change fiberMap (q ≫ r) ≫ fiberToPoint H.hom = fiberToPoint F.hom
  exact fiberMap_snd (q ≫ r)

example (F : Arrow PointedCGWH.{v, v}) :
    fiberToTotalArrowFunctor.map (𝟙 F) = 𝟙 (Arrow.mk (fiberToTotal F.hom)) :=
  fiberToTotalArrowFunctor.map_id F

example (F : Arrow PointedCGWH.{u, 0}) :
    fiberToPointArrowFunctor.map (𝟙 F) = 𝟙 (Arrow.mk (fiberToPoint F.hom)) :=
  fiberToPointArrowFunctor.map_id F

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    fiberFunctor.map q ≫ fiberToTotalNatTrans.app G = fiberToTotalNatTrans.app F ≫ q.left :=
  fiberToTotalNatTrans.naturality q

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    fiberFunctor.map q ≫ fiberToPointNatTrans.app G = fiberToPointNatTrans.app F ≫ 𝟙 pointObject :=
  fiberToPointNatTrans.naturality q

end PointedCGWH.StrictFiberPublicClients

/-!
The neutral strict-fiber import also exposes arbitrary chosen fibers and their
whole projection arrows. These clients retain the supplied cones and limits.
-/

run_cmd do
  let env ← Lean.getEnv
  let modelPrefix : Lean.Name :=
    `MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative
  for moduleName in env.header.moduleNames do
    if modelPrefix.isPrefixOf moduleName then
      throwError m!"neutral StrictFiber imported model module {moduleName}"

namespace PointedCGWH.StrictFiberPublicClients

open StrictFiberGeometry

section ChosenCones

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G)
    (c : PullbackCone F.hom (fromPoint F.right)) :
    (nativeChosenMapCone q c).pt = c.pt ∧
      (nativeChosenMapCone q c).fst = c.fst ≫ q.left ∧
      (nativeChosenMapCone q c).snd = c.snd :=
  ⟨rfl, rfl, rfl⟩

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G)
    (c : PullbackCone F.hom (fromPoint F.right)) :
    (nativeChosenMapCone q c).fst ≫ G.hom =
      (nativeChosenMapCone q c).snd ≫ fromPoint G.right :=
  (nativeChosenMapCone q c).condition

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G)
    (c : PullbackCone F.hom (fromPoint F.right))
    (d : PullbackCone G.hom (fromPoint G.right)) (hd : IsLimit d) :
    c.pt ⟶ d.pt :=
  nativeChosenFiberMap q c d hd

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G)
    (c : PullbackCone F.hom (fromPoint F.right))
    (d : PullbackCone G.hom (fromPoint G.right)) (hd : IsLimit d) :
    nativeChosenFiberMap q c d hd ≫ d.fst = c.fst ≫ q.left ∧
      nativeChosenFiberMap q c d hd ≫ d.snd = c.snd :=
  ⟨nativeChosenFiberMap_fst q c d hd, nativeChosenFiberMap_snd q c d hd⟩

example (F : Arrow PointedCGWH.{u, v})
    (c : PullbackCone F.hom (fromPoint F.right)) (hc : IsLimit c) :
    c.pt ≅ fiber F.hom :=
  nativeChosenFiberIso F c hc

example (F : Arrow PointedCGWH.{u, v})
    (c : PullbackCone F.hom (fromPoint F.right)) (hc : IsLimit c) :
    (nativeChosenFiberIso F c hc).hom ≫ fiberToTotal F.hom = c.fst ∧
      (nativeChosenFiberIso F c hc).hom ≫ fiberToPoint F.hom = c.snd ∧
      (nativeChosenFiberIso F c hc).inv ≫ c.fst = fiberToTotal F.hom ∧
      (nativeChosenFiberIso F c hc).inv ≫ c.snd = fiberToPoint F.hom :=
  ⟨nativeChosenFiberIso_hom_fst F c hc, nativeChosenFiberIso_hom_snd F c hc,
    nativeChosenFiberIso_inv_fst F c hc, nativeChosenFiberIso_inv_snd F c hc⟩

example (F : Arrow PointedCGWH.{u, v})
    (c : PullbackCone F.hom (fromPoint F.right)) (hc : IsLimit c) :
    (nativeChosenFiberIso F c hc).hom ≫ (nativeChosenFiberIso F c hc).inv = 𝟙 c.pt ∧
      (nativeChosenFiberIso F c hc).inv ≫ (nativeChosenFiberIso F c hc).hom =
        𝟙 (fiber F.hom) :=
  ⟨(nativeChosenFiberIso F c hc).hom_inv_id, (nativeChosenFiberIso F c hc).inv_hom_id⟩

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G)
    (c : PullbackCone F.hom (fromPoint F.right)) (hc : IsLimit c)
    (d : PullbackCone G.hom (fromPoint G.right)) (hd : IsLimit d) :
    nativeChosenFiberMap q c d hd ≫ (nativeChosenFiberIso G d hd).hom =
      (nativeChosenFiberIso F c hc).hom ≫ fiberFunctor.map q :=
  nativeChosenFiberIso_naturality q c hc d hd

end ChosenCones

section ChosenFamilies

variable
  (c : ∀ F : Arrow PointedCGWH.{u, v}, PullbackCone F.hom (fromPoint F.right))
  (hc : ∀ F, IsLimit (c F))

example (F : Arrow PointedCGWH.{u, v}) :
    (nativeChosenFiberFunctor c hc).obj F = (c F).pt := rfl

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    (nativeChosenFiberFunctor c hc).map q =
      nativeChosenFiberMap q (c F) (c G) (hc G) := rfl

example (F : Arrow PointedCGWH.{u, v}) :
    (nativeChosenFiberFunctor c hc).map (𝟙 F) = 𝟙 (c F).pt :=
  (nativeChosenFiberFunctor c hc).map_id F

example {F G H : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) (r : G ⟶ H) :
    (nativeChosenFiberFunctor c hc).map (q ≫ r) =
      (nativeChosenFiberFunctor c hc).map q ≫ (nativeChosenFiberFunctor c hc).map r :=
  (nativeChosenFiberFunctor c hc).map_comp q r

example : nativeChosenFiberFunctor c hc ≅ fiberFunctor :=
  nativeChosenFiberNatIso c hc

example (F : Arrow PointedCGWH.{u, v}) :
    (nativeChosenFiberNatIso c hc).hom.app F = (nativeChosenFiberIso F (c F) (hc F)).hom ∧
      (nativeChosenFiberNatIso c hc).inv.app F =
        (nativeChosenFiberIso F (c F) (hc F)).inv :=
  ⟨rfl, rfl⟩

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    (nativeChosenFiberFunctor c hc).map q ≫ (nativeChosenFiberNatIso c hc).hom.app G =
      (nativeChosenFiberNatIso c hc).hom.app F ≫ fiberFunctor.map q :=
  (nativeChosenFiberNatIso c hc).hom.naturality q

example (F : Arrow PointedCGWH.{u, v}) :
    (nativeChosenTotalArrowFunctor c hc).obj F = Arrow.mk (c F).fst ∧
      (nativeChosenPointArrowFunctor c hc).obj F = Arrow.mk (c F).snd :=
  ⟨rfl, rfl⟩

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    ((nativeChosenTotalArrowFunctor c hc).map q).left =
        (nativeChosenFiberFunctor c hc).map q ∧
      ((nativeChosenTotalArrowFunctor c hc).map q).right = q.left ∧
      ((nativeChosenPointArrowFunctor c hc).map q).left =
        (nativeChosenFiberFunctor c hc).map q ∧
      ((nativeChosenPointArrowFunctor c hc).map q).right = 𝟙 pointObject :=
  ⟨rfl, rfl, rfl, rfl⟩

example (F : Arrow PointedCGWH.{u, v}) :
    (nativeChosenTotalArrowFunctor c hc).map (𝟙 F) = 𝟙 (Arrow.mk (c F).fst) ∧
      (nativeChosenPointArrowFunctor c hc).map (𝟙 F) = 𝟙 (Arrow.mk (c F).snd) :=
  ⟨(nativeChosenTotalArrowFunctor c hc).map_id F,
    (nativeChosenPointArrowFunctor c hc).map_id F⟩

example {F G H : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) (r : G ⟶ H) :
    (nativeChosenTotalArrowFunctor c hc).map (q ≫ r) =
        (nativeChosenTotalArrowFunctor c hc).map q ≫
          (nativeChosenTotalArrowFunctor c hc).map r ∧
      (nativeChosenPointArrowFunctor c hc).map (q ≫ r) =
        (nativeChosenPointArrowFunctor c hc).map q ≫
          (nativeChosenPointArrowFunctor c hc).map r :=
  ⟨(nativeChosenTotalArrowFunctor c hc).map_comp q r,
    (nativeChosenPointArrowFunctor c hc).map_comp q r⟩

example : nativeChosenTotalArrowFunctor c hc ≅ fiberToTotalArrowFunctor :=
  nativeChosenTotalArrowNatIso c hc

example : nativeChosenPointArrowFunctor c hc ≅ fiberToPointArrowFunctor :=
  nativeChosenPointArrowNatIso c hc

example (F : Arrow PointedCGWH.{u, v}) :
    ((nativeChosenTotalArrowNatIso c hc).hom.app F).left =
        (nativeChosenFiberIso F (c F) (hc F)).hom ∧
      ((nativeChosenTotalArrowNatIso c hc).hom.app F).right = 𝟙 F.left ∧
      ((nativeChosenPointArrowNatIso c hc).hom.app F).left =
        (nativeChosenFiberIso F (c F) (hc F)).hom ∧
      ((nativeChosenPointArrowNatIso c hc).hom.app F).right = 𝟙 pointObject :=
  ⟨rfl, rfl, rfl, rfl⟩

example (F : Arrow PointedCGWH.{u, v}) :
    ((nativeChosenTotalArrowNatIso c hc).inv.app F).left =
        (nativeChosenFiberIso F (c F) (hc F)).inv ∧
      ((nativeChosenTotalArrowNatIso c hc).inv.app F).right = 𝟙 F.left ∧
      ((nativeChosenPointArrowNatIso c hc).inv.app F).left =
        (nativeChosenFiberIso F (c F) (hc F)).inv ∧
      ((nativeChosenPointArrowNatIso c hc).inv.app F).right = 𝟙 pointObject :=
  ⟨rfl, rfl, rfl, rfl⟩

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    (nativeChosenTotalArrowFunctor c hc).map q ≫
        (nativeChosenTotalArrowNatIso c hc).hom.app G =
      (nativeChosenTotalArrowNatIso c hc).hom.app F ≫ fiberToTotalArrowFunctor.map q :=
  (nativeChosenTotalArrowNatIso c hc).hom.naturality q

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    fiberToTotalArrowFunctor.map q ≫ (nativeChosenTotalArrowNatIso c hc).inv.app G =
      (nativeChosenTotalArrowNatIso c hc).inv.app F ≫
        (nativeChosenTotalArrowFunctor c hc).map q :=
  (nativeChosenTotalArrowNatIso c hc).inv.naturality q

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    (nativeChosenPointArrowFunctor c hc).map q ≫
        (nativeChosenPointArrowNatIso c hc).hom.app G =
      (nativeChosenPointArrowNatIso c hc).hom.app F ≫ fiberToPointArrowFunctor.map q :=
  (nativeChosenPointArrowNatIso c hc).hom.naturality q

example {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    fiberToPointArrowFunctor.map q ≫ (nativeChosenPointArrowNatIso c hc).inv.app G =
      (nativeChosenPointArrowNatIso c hc).inv.app F ≫
        (nativeChosenPointArrowFunctor c hc).map q :=
  (nativeChosenPointArrowNatIso c hc).inv.naturality q

end ChosenFamilies

section ChosenUniverseClients

example
    (c : ∀ F : Arrow PointedCGWH.{v, v}, PullbackCone F.hom (fromPoint F.right))
    (hc : ∀ F, IsLimit (c F)) :
    nativeChosenFiberFunctor c hc ≅ fiberFunctor.{v, v} :=
  nativeChosenFiberNatIso c hc

example
    (c : ∀ F : Arrow PointedCGWH.{u, 0}, PullbackCone F.hom (fromPoint F.right))
    (hc : ∀ F, IsLimit (c F)) :
    nativeChosenPointArrowFunctor c hc ≅ fiberToPointArrowFunctor.{u, 0} :=
  nativeChosenPointArrowNatIso c hc

end ChosenUniverseClients

end PointedCGWH.StrictFiberPublicClients
