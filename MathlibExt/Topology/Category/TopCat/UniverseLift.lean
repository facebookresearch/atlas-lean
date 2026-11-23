/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Category.TopCat.ULift
public import Mathlib.Topology.Homotopy.Basic

/-!
# Continuous maps and homotopies on lifted carriers

A continuous map between independently sized spaces is represented by the
literal `ULift.up`/original map/`ULift.down` composite. Only the two original
carrier universes enter this representation. Arbitrary chosen carrier lifts
also retain both complete map inverses, composition, the original homotopy
clock, and relative fixed sets when returning to the original spaces.
-/

open CategoryTheory
open scoped ContinuousMap

universe u v

public section

namespace TopCat

/-- The original continuous map in its minimum common carrier universe. -/
def minimumCommonCarrierMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    (TopCat.of (ULift.{v} X) : TopCat.{max u v}) ⟶
      (TopCat.of (ULift.{u} Y) : TopCat.{max u v}) :=
  TopCat.ofHom
    (⟨fun q : ULift.{v} X => (ULift.up (f q.down) : ULift.{u} Y),
      continuous_uliftUp.comp (f.continuous.comp continuous_uliftDown)⟩ :
      C(ULift.{v} X, ULift.{u} Y))

private theorem minimumCommonCarrierMap_apply_computation
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (q : ULift.{v} X) :
    minimumCommonCarrierMap f q = (ULift.up (f q.down) : ULift.{u} Y) := by
  unfold minimumCommonCarrierMap
  rfl

/-- A lifted point maps to the lift of its original image. -/
theorem minimumCommonCarrierMap_apply
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (q : ULift.{v} X) :
    minimumCommonCarrierMap f q = (ULift.up (f q.down) : ULift.{u} Y) :=
  minimumCommonCarrierMap_apply_computation f q

/-- The named map agrees with its original explicit carrier-lift encoding. -/
theorem minimumCommonCarrierMap_eq_ofHom
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    minimumCommonCarrierMap f =
      TopCat.ofHom
        (⟨fun q : ULift.{v} X => (ULift.up (f q.down) : ULift.{u} Y),
          continuous_uliftUp.comp (f.continuous.comp continuous_uliftDown)⟩ :
          C(ULift.{v} X, ULift.{u} Y)) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  exact minimumCommonCarrierMap_apply f q

end TopCat

noncomputable section

universe w z uZ lX lY lZ

namespace TopCat.UniverseLift

/-- The same continuous map between any two chosen lifts of its original carriers. -/
@[expose]
def liftMap {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : C(ULift.{w} X, ULift.{z} Y) where
  toFun q := ULift.up (f q.down)
  continuous_toFun := continuous_uliftUp.comp (f.continuous.comp continuous_uliftDown)

/-- Every lifted value is the lift of the same original value. -/
private theorem liftMap_applyComputed {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (q : ULift.{w} X) :
    liftMap.{u, v, w, z} f q = ULift.up (f q.down) := rfl

@[simp]
theorem liftMap_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (q : ULift.{w} X) :
    liftMap.{u, v, w, z} f q = ULift.up (f q.down) :=
  liftMap_applyComputed f q

/-- The original image-point equality is retained by the actual lifted map. -/
theorem liftMap_point {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {x : X} {y : Y} (hxy : f x = y) :
    liftMap.{u, v, w, z} f (ULift.up x) = ULift.up y :=
  congrArg ULift.up hxy

/-- Return an actual map of lifted carriers to the two original carriers. -/
@[expose]
def returnMap {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(ULift.{w} X, ULift.{z} Y)) : C(X, Y) where
  toFun x := (f (ULift.up x)).down
  continuous_toFun := continuous_uliftDown.comp (f.continuous.comp continuous_uliftUp)

private theorem returnMap_applyComputed {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(ULift.{w} X, ULift.{z} Y)) (x : X) :
    returnMap f x = (f (ULift.up x)).down := rfl

@[simp]
theorem returnMap_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(ULift.{w} X, ULift.{z} Y)) (x : X) :
    returnMap f x = (f (ULift.up x)).down := returnMap_applyComputed f x

/-- Returning the original lifted map gives the whole original map. -/
@[simp]
theorem return_liftMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    returnMap (liftMap.{u, v, w, z} f) = f := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- The two carrier homeomorphisms recover the whole given lifted map. -/
@[simp]
theorem lift_returnMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(ULift.{w} X, ULift.{z} Y)) :
    liftMap.{u, v, w, z} (returnMap f) = f := by
  apply ContinuousMap.ext
  intro q
  change ULift.up (f (ULift.up q.down)).down = f q
  rw [ULift.up_down, ULift.up_down]

/-- Actual carrier lifting preserves composition through the same middle carrier. -/
theorem liftMap_comp {X : Type u} {Y : Type v} {Z : Type uZ}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    (liftMap.{v, uZ, lY, lZ} g).comp (liftMap.{u, v, lX, lY} f) =
      liftMap.{u, uZ, lX, lZ} (g.comp f) := by
  apply ContinuousMap.ext
  intro q
  rfl

/-- Returning actual lifted maps preserves their whole composition. -/
theorem returnMap_comp {X : Type u} {Y : Type v} {Z : Type uZ}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(ULift.{lX} X, ULift.{lY} Y)) (g : C(ULift.{lY} Y, ULift.{lZ} Z)) :
    returnMap (g.comp f) = (returnMap g).comp (returnMap f) := by
  apply ContinuousMap.ext
  intro x
  change (g (f (ULift.up x))).down = (g (ULift.up (f (ULift.up x)).down)).down
  rw [ULift.up_down]

/-- Lift a complete homotopy with the same original time variable. -/
@[expose]
def liftHomotopy {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (K : ContinuousMap.Homotopy f g) :
    ContinuousMap.Homotopy (liftMap.{u, v, w, z} f) (liftMap.{u, v, w, z} g) where
  toFun q := ULift.up (K (q.1, q.2.down))
  continuous_toFun := continuous_uliftUp.comp
    (K.continuous.comp (continuous_fst.prodMk (continuous_uliftDown.comp continuous_snd)))
  map_zero_left q := congrArg ULift.up (K.apply_zero q.down)
  map_one_left q := congrArg ULift.up (K.apply_one q.down)

/-- Return a complete original-carrier homotopy without changing its clock. -/
@[expose]
def returnHomotopy {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(ULift.{w} X, ULift.{z} Y)} (K : ContinuousMap.Homotopy f g) :
    ContinuousMap.Homotopy (returnMap f) (returnMap g) where
  toFun q := (K (q.1, ULift.up q.2)).down
  continuous_toFun := continuous_uliftDown.comp
    (K.continuous.comp (continuous_fst.prodMk (continuous_uliftUp.comp continuous_snd)))
  map_zero_left q := congrArg ULift.down (K.apply_zero (ULift.up q))
  map_one_left q := congrArg ULift.down (K.apply_one (ULift.up q))

/-- Every returned point and time is the downward image of the same actual family value. -/
private theorem returnHomotopy_applyComputed {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(ULift.{w} X, ULift.{z} Y)} (K : ContinuousMap.Homotopy f g)
    (t : unitInterval) (x : X) :
    returnHomotopy K (t, x) = (K (t, ULift.up x)).down := rfl

theorem returnHomotopy_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(ULift.{w} X, ULift.{z} Y)} (K : ContinuousMap.Homotopy f g)
    (t : unitInterval) (x : X) :
    returnHomotopy K (t, x) = (K (t, ULift.up x)).down :=
  returnHomotopy_applyComputed K t x

/-- The complete returned relative family fixes the original specified range. -/
@[expose]
def returnHomotopyRel {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(ULift.{w} X, ULift.{z} Y)} (S : Set X)
    (K : ContinuousMap.HomotopyRel f g (ULift.up '' S)) :
    ContinuousMap.HomotopyRel (returnMap f) (returnMap g) S where
  toHomotopy := returnHomotopy K.toHomotopy
  prop' t x hx := congrArg ULift.down (K.eq_fst t ⟨x, hx, rfl⟩)

/-- The whole lifted family evaluates at the same original time and point. -/
private theorem liftHomotopy_applyComputed {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (K : ContinuousMap.Homotopy f g) (t : unitInterval) (q : ULift.{w} X) :
    liftHomotopy.{u, v, w, z} K (t, q) = ULift.up (K (t, q.down)) := rfl

/-- Lifting a homotopy preserves every original time and family value. -/
theorem liftHomotopy_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (K : ContinuousMap.Homotopy f g) (t : unitInterval) (q : ULift.{w} X) :
    liftHomotopy.{u, v, w, z} K (t, q) = ULift.up (K (t, q.down)) :=
  liftHomotopy_applyComputed K t q

/-- Returning a relative homotopy retains its complete original-time value. -/
theorem returnHomotopyRel_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(ULift.{w} X, ULift.{z} Y)} (S : Set X)
    (K : ContinuousMap.HomotopyRel f g (ULift.up '' S)) (t : unitInterval) (x : X) :
    returnHomotopyRel S K (t, x) = (K (t, ULift.up x)).down :=
  returnHomotopy_apply K.toHomotopy t x

end TopCat.UniverseLift

namespace TopCat

open UniverseLift

/-- The actual minimum-carrier arrow has the same entire lifted continuous map. -/
theorem minimumCommonCarrierMap_hom {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (TopCat.minimumCommonCarrierMap f).hom = liftMap.{u, v, v, u} f := by
  apply ContinuousMap.ext
  intro q
  exact TopCat.minimumCommonCarrierMap_apply f q

/-- The selected original point equality determines the same minimum-carrier point. -/
theorem minimumCommonCarrierMap_point {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {x : X} {y : Y} (hxy : f x = y) :
    TopCat.minimumCommonCarrierMap f (ULift.up x) = ULift.up y :=
  (TopCat.minimumCommonCarrierMap_apply f (ULift.up x)).trans (congrArg ULift.up hxy)

end TopCat
