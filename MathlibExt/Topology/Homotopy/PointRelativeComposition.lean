/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Product

noncomputable section

/-!
# Actual precomposition of a point-relative homotopy

The original continuous map sends the selected source point to the
selected fixed point. Precomposition then retains that point at EVERY
time. This uses the original whole family, not a based-homotopy witness
chosen after forgetting its unit trace.
-/

namespace ContinuousMap.HomotopyRel

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Precompose an ORIGINAL point-relative family along its actual point triangle. -/
public def precomposePointRelative
    {f g : C(Y, Z)} {y : Y} (H : ContinuousMap.HomotopyRel f g {y})
    (a : C(X, Y)) (x : X) (hx : a x = y) :
    ContinuousMap.HomotopyRel (f.comp a) (g.comp a) {x} where
  toHomotopy := H.toHomotopy.compContinuousMap a
  prop' t z hz := by
    have hzx : z = x := Set.mem_singleton_iff.mp hz
    subst z
    change H (t, a x) = f (a x)
    exact H.eq_fst t (by rw [hx]; exact Set.mem_singleton y)

end ContinuousMap.HomotopyRel

namespace ContinuousMap.HomotopyEquiv

open scoped ContinuousMap

universe u v w z

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

/-- Compose the actual source inverse families through the actual forward
point equation; every time remains fixed at the original source point. -/
public def transLeftHomotopyRel (e : X ≃ₕ Y) (d : Y ≃ₕ Z)
    (x : X) (y : Y) (he : e.toFun x = y)
    (L : ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id X) {x})
    (K : ContinuousMap.HomotopyRel (d.invFun.comp d.toFun) (ContinuousMap.id Y) {y}) :
    ContinuousMap.HomotopyRel ((e.trans d).invFun.comp (e.trans d).toFun)
      (ContinuousMap.id X) {x} := by
  let A := (K.precomposePointRelative e.toFun x he).compContinuousMap e.invFun
  exact (A.cast
    (by apply ContinuousMap.ext; intro a; rfl)
    (by apply ContinuousMap.ext; intro a; rfl)).trans L

/-- Compose the actual target inverse families through the actual inverse
point equation, retaining the original target point for the whole family. -/
public def transRightHomotopyRel (e : X ≃ₕ Y) (d : Y ≃ₕ Z)
    (y : Y) (q : Z) (hd : d.invFun q = y)
    (L : ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y})
    (K : ContinuousMap.HomotopyRel (d.toFun.comp d.invFun) (ContinuousMap.id Z) {q}) :
    ContinuousMap.HomotopyRel ((e.trans d).toFun.comp (e.trans d).invFun)
      (ContinuousMap.id Z) {q} := by
  let A := (L.precomposePointRelative d.invFun q hd).compContinuousMap d.toFun
  exact (A.cast
    (by apply ContinuousMap.ext; intro a; rfl)
    (by apply ContinuousMap.ext; intro a; rfl)).trans K

/-- The ordinary product of the actual inverse maps retains both source
families at the original product point, without product-cofibration input. -/
public def prodCongrLeftHomotopyRel (e : X ≃ₕ Y) (d : Z ≃ₕ W)
    (x : X) (q : Z)
    (L : ContinuousMap.HomotopyRel (e.invFun.comp e.toFun) (ContinuousMap.id X) {x})
    (K : ContinuousMap.HomotopyRel (d.invFun.comp d.toFun) (ContinuousMap.id Z) {q}) :
    ContinuousMap.HomotopyRel ((e.prodCongr d).invFun.comp (e.prodCongr d).toFun)
      (ContinuousMap.id (X × Z)) {(x, q)} := by
  let LX := L.precomposePointRelative (ContinuousMap.fst : C(X × Z, X)) (x, q) rfl
  let KZ := K.precomposePointRelative (ContinuousMap.snd : C(X × Z, Z)) (x, q) rfl
  exact (LX.prod KZ).cast
    (by apply ContinuousMap.ext; intro a; rfl)
    (by apply ContinuousMap.ext; intro a; rfl)

/-- The ordinary product also retains both target inverse families at
its actual product point, for independently sized original spaces. -/
public def prodCongrRightHomotopyRel (e : X ≃ₕ Y) (d : Z ≃ₕ W)
    (y : Y) (q : W)
    (L : ContinuousMap.HomotopyRel (e.toFun.comp e.invFun) (ContinuousMap.id Y) {y})
    (K : ContinuousMap.HomotopyRel (d.toFun.comp d.invFun) (ContinuousMap.id W) {q}) :
    ContinuousMap.HomotopyRel ((e.prodCongr d).toFun.comp (e.prodCongr d).invFun)
      (ContinuousMap.id (Y × W)) {(y, q)} := by
  let LY := L.precomposePointRelative (ContinuousMap.fst : C(Y × W, Y)) (y, q) rfl
  let KW := K.precomposePointRelative (ContinuousMap.snd : C(Y × W, W)) (y, q) rfl
  exact (LY.prod KW).cast
    (by apply ContinuousMap.ext; intro a; rfl)
    (by apply ContinuousMap.ext; intro a; rfl)

end ContinuousMap.HomotopyEquiv

end
