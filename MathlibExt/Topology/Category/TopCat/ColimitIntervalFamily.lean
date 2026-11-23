/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval

/-!
# Whole interval families on an actual ordinary colimit

Compatible continuous interval families form a strict compact-open path
cocone. The actual colimit universal property descends that cocone, and the
locally compact interval permits uncurrying. The resulting continuous family
retains every original cocone point and every interval time.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap

universe u v w

namespace TopCat

variable {J : Type v} [Category.{w} J] {F : J ⥤ TopCat.{u}}

private def intervalFamilyPathCocone (Y : TopCat.{u})
    (family : ∀ j : J, C(unitInterval × F.obj j, Y))
    (compatibility : ∀ {i j : J} (q : i ⟶ j) (t : unitInterval) (x : F.obj i),
      family j (t, F.map q x) = family i (t, x)) : Cocone F where
  pt := TopCat.of C(unitInterval, Y)
  ι.app j := TopCat.ofHom ((family j).comp ContinuousMap.prodSwap).curry
  ι.naturality {i j} q := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply ContinuousMap.ext
    intro t
    change family j (t, F.map q x) = family i (t, x)
    exact compatibility q t x

private def intervalFamilyPathDesc {c : Cocone F} (hc : IsColimit c)
    (Y : TopCat.{u}) (family : ∀ j : J, C(unitInterval × F.obj j, Y))
    (compatibility : ∀ {i j : J} (q : i ⟶ j) (t : unitInterval) (x : F.obj i),
      family j (t, F.map q x) = family i (t, x)) :
    c.pt ⟶ TopCat.of C(unitInterval, Y) :=
  hc.desc (intervalFamilyPathCocone Y family compatibility)

/-- Descend raw literally compatible continuous interval families through
an ACTUAL ordinary colimit. All original cocone points and times are retained. -/
public def descIntervalFamily {c : Cocone F} (hc : IsColimit c)
    (Y : TopCat.{u}) (family : ∀ j : J, C(unitInterval × F.obj j, Y))
    (compatibility : ∀ {i j : J} (q : i ⟶ j) (t : unitInterval) (x : F.obj i),
      family j (t, F.map q x) = family i (t, x)) : C(unitInterval × c.pt, Y) :=
  (intervalFamilyPathDesc hc Y family compatibility).hom.uncurry.comp
    ContinuousMap.prodSwap

/-- The descended WHOLE family agrees with the SAME original family at
EVERY cocone point and original interval time. -/
public theorem descIntervalFamily_fac {c : Cocone F} (hc : IsColimit c)
    (Y : TopCat.{u}) (family : ∀ j : J, C(unitInterval × F.obj j, Y))
    (compatibility : ∀ {i j : J} (q : i ⟶ j) (t : unitInterval) (x : F.obj i),
      family j (t, F.map q x) = family i (t, x))
    (j : J) (t : unitInterval) (x : F.obj j) :
    descIntervalFamily hc Y family compatibility (t, c.ι.app j x) = family j (t, x) := by
  have hx := ConcreteCategory.congr_hom
    (hc.fac (intervalFamilyPathCocone Y family compatibility) j) x
  have ht := congrArg (fun path : C(unitInterval, Y) => path t) hx
  change intervalFamilyPathDesc hc Y family compatibility (c.ι.app j x) t =
    family j (t, x)
  exact ht

end TopCat

end
