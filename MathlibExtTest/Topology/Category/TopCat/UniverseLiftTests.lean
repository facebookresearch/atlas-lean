/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.UniverseLift

/-! Clients for independent carrier lifts, original clocks and complete source images. -/

public section
noncomputable section

open scoped ContinuousMap
open TopCat.UniverseLift

universe u v k lX lY lZ

namespace MathlibExtTest.TopCatUniverseLift

/-- Both actual maps survive the two independent carrier dictionaries. -/
theorem originalMapsRetained {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (F : C(ULift.{lX} X, ULift.{lY} Y)) :
    returnMap (liftMap.{u, v, lX, lY} f) = f ∧
      liftMap.{u, v, lX, lY} (returnMap F) = F :=
  ⟨return_liftMap f, lift_returnMap F⟩

/-- Three original carriers and all three selected lifts remain independent. -/
theorem originalCompositeRetained {X : Type u} {Y : Type v} {Z : Type k}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    returnMap ((liftMap.{v, k, lY, lZ} g).comp (liftMap.{u, v, lX, lY} f)) =
      g.comp f := by
  rw [liftMap_comp, return_liftMap]

/-- The minimum common carrier reuses the same whole map and original point. -/
theorem minimumOriginalMapAndPoint {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {x : X} {y : Y} (hxy : f x = y) :
    returnMap (TopCat.minimumCommonCarrierMap f).hom = f ∧
      TopCat.minimumCommonCarrierMap f (ULift.up x) = ULift.up y := by
  refine ⟨?_, TopCat.minimumCommonCarrierMap_point f hxy⟩
  rw [TopCat.minimumCommonCarrierMap_hom, return_liftMap]

/-- Lifting and returning a whole homotopy retains every original time value. -/
theorem originalHomotopyClock {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (K : ContinuousMap.Homotopy f g) (t : unitInterval) (x : X) :
    returnHomotopy (liftHomotopy.{u, v, lX, lY} K) (t, x) = K (t, x) := by
  calc
    _ = (liftHomotopy.{u, v, lX, lY} K (t, ULift.up x)).down :=
      returnHomotopy_apply _ t x
    _ = K (t, x) :=
      congrArg ULift.down (liftHomotopy_apply.{u, v, lX, lY} K t (ULift.up x))

/-- The returned family fixes the entire image of an independently sized source. -/
theorem originalRelativeSourceImage {S : Type k} {X : Type u} {Y : Type v}
    [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]
    (i : C(S, X)) {f g : C(ULift.{lX} X, ULift.{lY} Y)}
    (K : ContinuousMap.HomotopyRel f g (ULift.up '' Set.range i)) :
    (∀ t x, returnHomotopyRel (Set.range i) K (t, x) = (K (t, ULift.up x)).down) ∧
      ∀ t s, returnHomotopyRel (Set.range i) K (t, i s) = (f (ULift.up (i s))).down := by
  refine ⟨fun t x => returnHomotopyRel_apply _ K t x, ?_⟩
  intro t s
  exact ((returnHomotopyRel (Set.range i) K).eq_fst t ⟨s, rfl⟩).trans
    (returnMap_apply f (i s))

end MathlibExtTest.TopCatUniverseLift
