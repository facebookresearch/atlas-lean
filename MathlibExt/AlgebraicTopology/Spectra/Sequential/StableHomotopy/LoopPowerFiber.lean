/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.Evaluation
import MathlibExt.Topology.Category.PointedCGWH.SerreSequence.LoopFiberArrow

/-!
# Every original ordered loop power preserves the original pointed fiber

The actual one-sphere loop/fiber comparison is iterated in its original
order. Every comparison retains the original total and point projections,
both inverse functions and every full original Arrow square. These are
ordinary limit comparisons, with no stabilization or exactness input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open PointedCGWH.SequentialSpectrum.OrderedLoop
open PointedCGWH.StrictFiberGeometry
open PointedCGWH.LoopFiberGeometry
open scoped MonoidalClosed CGWH.limits CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedFiber

/-- The original point comparison is iterated using the same ordered loop powers. -/
def loopPowerPointIso : ∀ n : ℕ,
    (loopPower.{u, v} n).obj pointObject ≅ pointObject
  | 0 => Iso.refl _
  | n + 1 => PointedCGWH.loop.mapIso (loopPowerPointIso n) ≪≫ loopPointIso

/-- The entire original fiber functor is followed by the actual ordered loop power. -/
def loopPowerFiberFunctor (n : ℕ) : Arrow PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  fiberFunctor ⋙ loopPower n

/-- The entire original Arrow is looped before taking its actual original pointed fiber. -/
def fiberLoopPowerFunctor (n : ℕ) : Arrow PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  (loopPower n).mapArrow ⋙ fiberFunctor

/-- Each full comparison uses the same original one-sphere loop/fiber construction. -/
def loopPowerFiberIso : ∀ (n : ℕ) (F : Arrow PointedCGWH.{u, v}),
    (loopPower n).obj (fiber F.hom) ≅ fiber ((loopPower n).map F.hom)
  | 0, F => Iso.refl (fiber F.hom)
  | n + 1, F => PointedCGWH.loop.mapIso (loopPowerFiberIso n F) ≪≫
      nativeLoopFiberIso (Arrow.mk ((loopPower n).map F.hom))

/-- Every complete forward comparison retains the original looped total projection. -/
theorem loopPowerFiberIso_hom_fst (n : ℕ) (F : Arrow PointedCGWH.{u, v}) :
    (loopPowerFiberIso n F).hom ≫ fiberToTotal ((loopPower n).map F.hom) =
      (loopPower n).map (fiberToTotal F.hom) := by
  induction n with
  | zero => exact Category.id_comp _
  | succ n ih =>
    let d : PointedCGWH.loop.obj (fiber ((loopPower n).map F.hom)) ⟶
        fiber (PointedCGWH.loop.map ((loopPower n).map F.hom)) :=
      (nativeLoopFiberIso (Arrow.mk ((loopPower n).map F.hom))).hom
    have hd : d ≫ fiberToTotal (PointedCGWH.loop.map ((loopPower n).map F.hom)) =
        PointedCGWH.loop.map (fiberToTotal ((loopPower n).map F.hom)) :=
      nativeLoopFiberIso_hom_fst (Arrow.mk ((loopPower n).map F.hom))
    change (PointedCGWH.loop.map (loopPowerFiberIso n F).hom ≫
        d) ≫
      fiberToTotal (PointedCGWH.loop.map ((loopPower n).map F.hom)) =
      PointedCGWH.loop.map ((loopPower n).map (fiberToTotal F.hom))
    calc
      _ = PointedCGWH.loop.map (loopPowerFiberIso n F).hom ≫
          PointedCGWH.loop.map (fiberToTotal ((loopPower n).map F.hom)) :=
        (Category.assoc _ _ _).trans (congrArg (fun g =>
          PointedCGWH.loop.map (loopPowerFiberIso n F).hom ≫ g) hd)
      _ = PointedCGWH.loop.map ((loopPowerFiberIso n F).hom ≫
          fiberToTotal ((loopPower n).map F.hom)) := (PointedCGWH.loop.map_comp _ _).symm
      _ = _ := PointedCGWH.loop.congr_map ih

/-- Every complete forward comparison retains the original point leg and its actual point Iso. -/
theorem loopPowerFiberIso_hom_snd (n : ℕ) (F : Arrow PointedCGWH.{u, v}) :
    (loopPowerFiberIso n F).hom ≫ fiberToPoint ((loopPower n).map F.hom) =
      (loopPower n).map (fiberToPoint F.hom) ≫ (loopPowerPointIso n).hom := by
  induction n with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ n ih =>
    let d : PointedCGWH.loop.obj (fiber ((loopPower n).map F.hom)) ⟶
        fiber (PointedCGWH.loop.map ((loopPower n).map F.hom)) :=
      (nativeLoopFiberIso (Arrow.mk ((loopPower n).map F.hom))).hom
    have hd : d ≫ fiberToPoint (PointedCGWH.loop.map ((loopPower n).map F.hom)) =
        PointedCGWH.loop.map (fiberToPoint ((loopPower n).map F.hom)) ≫ loopPointIso.hom :=
      nativeLoopFiberIso_hom_snd (Arrow.mk ((loopPower n).map F.hom))
    change (PointedCGWH.loop.map (loopPowerFiberIso n F).hom ≫
        d) ≫
      fiberToPoint (PointedCGWH.loop.map ((loopPower n).map F.hom)) =
      PointedCGWH.loop.map ((loopPower n).map (fiberToPoint F.hom)) ≫
        (PointedCGWH.loop.map (loopPowerPointIso n).hom ≫ loopPointIso.hom)
    rw [Category.assoc, hd, ← Category.assoc,
      ← PointedCGWH.loop.map_comp, ih, PointedCGWH.loop.map_comp, Category.assoc]

/-- The complete inverse comparison retains the same original looped total projection. -/
theorem loopPowerFiberIso_inv_fst (n : ℕ) (F : Arrow PointedCGWH.{u, v}) :
    (loopPowerFiberIso n F).inv ≫ (loopPower n).map (fiberToTotal F.hom) =
      fiberToTotal ((loopPower n).map F.hom) := by
  rw [← loopPowerFiberIso_hom_fst n F, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The entire inverse comparison retains the same original point projection
and inverse point Iso. -/
theorem loopPowerFiberIso_inv_snd (n : ℕ) (F : Arrow PointedCGWH.{u, v}) :
    (loopPowerFiberIso n F).inv ≫ (loopPower n).map (fiberToPoint F.hom) =
      fiberToPoint ((loopPower n).map F.hom) ≫ (loopPowerPointIso n).inv := by
  apply (cancel_epi (loopPowerFiberIso n F).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, ← Category.assoc,
    loopPowerFiberIso_hom_snd, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Every full original Arrow map is preserved by each actual ordered loop/fiber comparison. -/
theorem loopPowerFiberIso_naturality (n : ℕ)
    {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    (loopPowerFiberFunctor n).map q ≫ (loopPowerFiberIso n G).hom =
      (loopPowerFiberIso n F).hom ≫ (fiberLoopPowerFunctor n).map q := by
  apply PullbackCone.IsLimit.hom_ext (fiberConeIsLimit ((loopPower n).map G.hom))
  · let d : fiber ((loopPower n).map F.hom) ⟶ fiber ((loopPower n).map G.hom) :=
      fiberMap ((loopPower n).mapArrow.map q)
    have hd : d ≫ fiberToTotal ((loopPower n).map G.hom) =
        fiberToTotal ((loopPower n).map F.hom) ≫ (loopPower n).map q.left :=
      fiberMap_fst ((loopPower n).mapArrow.map q)
    change ((loopPower n).map (fiberMap q) ≫ (loopPowerFiberIso n G).hom) ≫
        fiberToTotal ((loopPower n).map G.hom) =
      ((loopPowerFiberIso n F).hom ≫ d) ≫
        fiberToTotal ((loopPower n).map G.hom)
    rw [Category.assoc, loopPowerFiberIso_hom_fst n G,
      ← (loopPower n).map_comp, fiberMap_fst,
      Category.assoc, hd, ← Category.assoc, loopPowerFiberIso_hom_fst n F,
      (loopPower n).map_comp]
  · exact pointObjectIsTerminal.hom_ext _ _

/-- Both full original ordered loop/fiber functors form their genuine natural isomorphism. -/
def loopPowerFiberNatIso (n : ℕ) : loopPowerFiberFunctor.{u, v} n ≅ fiberLoopPowerFunctor n :=
  NatIso.ofComponents (loopPowerFiberIso n) (fun q => loopPowerFiberIso_naturality n q)

/-- The complete inverse naturality retains every original input Arrow map. -/
theorem loopPowerFiberNatIso_inv_naturality (n : ℕ)
    {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    (fiberLoopPowerFunctor n).map q ≫ (loopPowerFiberNatIso n).inv.app G =
      (loopPowerFiberNatIso n).inv.app F ≫ (loopPowerFiberFunctor n).map q :=
  (loopPowerFiberNatIso n).inv.naturality q

/-- Every actual ordered loop power preserves original pointed Serre fibrations. -/
theorem loopPower_map_fibration (n : ℕ) {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : fibrations PointedCGWH.{u, v} f) :
    fibrations PointedCGWH.{u, v} ((loopPower n).map f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
      PointedCGWH.modelCategory.sphereOne_isCofibrant
    let _ := ihomAdjunction_isQuillenAdjunction_of_isCofibrant PointedCGWH.sphereOne.{u, v}
    exact Adjunction.IsQuillenAdjunction.preservesFibrations
      (adj := ihom.adjunction PointedCGWH.sphereOne) ((loopPower n).map f) ih

end PointedCGWH.SequentialSpectrum.StableHomotopy.LoopedFiber
