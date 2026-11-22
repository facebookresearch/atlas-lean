/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import Mathlib.Topology.Homotopy.Basic

/-!
# Full continuous path families into the original homotopy fiber

A continuous homotopy from `p` after a specified total-coordinate map to
the constant chosen base point gives a map into the original compact-open
homotopy fiber. Its total coordinate and complete path are retained.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology
open scoped unitInterval

universe u

namespace TopCat

/-- A continuous homotopy is the corresponding full compact-open path family. -/
def homotopyPathMap {Z B : TopCat.{u}} {f g : Z ⟶ B}
    (H : ContinuousMap.Homotopy f.hom g.hom) : Z ⟶ pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z => H.toContinuousMap (TopCat.I.homeomorph z.2, z.1)
      continuous_toFun := H.continuous.comp
        ((TopCat.I.homeomorph.continuous.comp continuous_snd).prodMk continuous_fst) }

private theorem homotopyPathMapApplyComputed {Z B : TopCat.{u}} {f g : Z ⟶ B}
    (H : ContinuousMap.Homotopy f.hom g.hom) (z : Z) (t : TopCat.I.{u}) :
    homotopyPathMap H z t = H.toContinuousMap (TopCat.I.homeomorph t, z) := rfl

/-- Every parameter of the compact-open family is the supplied homotopy value. -/
theorem homotopyPathMap_apply {Z B : TopCat.{u}} {f g : Z ⟶ B}
    (H : ContinuousMap.Homotopy f.hom g.hom) (z : Z) (t : TopCat.I.{u}) :
    homotopyPathMap H z t = H.toContinuousMap (TopCat.I.homeomorph t, z) :=
  homotopyPathMapApplyComputed H z t

/-- The family starts at the original source map. -/
theorem homotopyPathMap_evalZero {Z B : TopCat.{u}} {f g : Z ⟶ B}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    homotopyPathMap H ≫ pathEvalZero B = f := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change H.toContinuousMap (TopCat.I.homeomorph (0 : TopCat.I.{u}), z) = f.hom z
  exact (congrArg (fun t : unitInterval => H.toContinuousMap (t, z))
    TopCat.I.homeomorph_zero.{u}).trans (H.map_zero_left z)

/-- The family ends at the original target map. -/
theorem homotopyPathMap_evalOne {Z B : TopCat.{u}} {f g : Z ⟶ B}
    (H : ContinuousMap.Homotopy f.hom g.hom) :
    homotopyPathMap H ≫ pathEvalOne B = g := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change H.toContinuousMap (TopCat.I.homeomorph (1 : TopCat.I.{u}), z) = g.hom z
  exact (congrArg (fun t : unitInterval => H.toContinuousMap (t, z))
    TopCat.I.homeomorph_one.{u}).trans (H.map_one_left z)

/-- Lift the given total point and its entire path into the actual homotopy fiber. -/
def homotopyFiberMapOfPathFamily {Z E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) (l : Z ⟶ E)
    (H : ContinuousMap.Homotopy (l ≫ p).hom (TopCat.const b : Z ⟶ B).hom) :
    Z ⟶ homotopyFiber p b := by
  let P : TopCat.{u} := TopCat.of PUnit
  let c : Z ⟶ P := TopCat.const PUnit.unit
  let q : P ⟶ B := TopCat.const b
  refine pullback.lift (prod.lift l c) (homotopyPathMap H) ?_
  apply prod.hom_ext
  · calc
      _ = (prod.lift l c ≫ prod.fst) ≫ p := by
        rw [Category.assoc, prod.map_fst, ← Category.assoc]
      _ = l ≫ p := congrArg (· ≫ p) (prod.lift_fst l c)
      _ = homotopyPathMap H ≫ pathEvalZero B := (homotopyPathMap_evalZero H).symm
      _ = (homotopyPathMap H ≫ pathEndpoints B) ≫ prod.fst := by
        simp only [pathEndpoints, Category.assoc, prod.lift_fst]
  · calc
      _ = (prod.lift l c ≫ prod.snd) ≫ q := by
        rw [Category.assoc, prod.map_snd, ← Category.assoc]
      _ = c ≫ q := congrArg (· ≫ q) (prod.lift_snd l c)
      _ = TopCat.const b := rfl
      _ = homotopyPathMap H ≫ pathEvalOne B := (homotopyPathMap_evalOne H).symm
      _ = (homotopyPathMap H ≫ pathEndpoints B) ≫ prod.snd := by
        simp only [pathEndpoints, Category.assoc, prod.lift_snd]

/-- The lifted total coordinate is the given original map. -/
theorem homotopyFiberMapOfPathFamily_toTotal {Z E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) (l : Z ⟶ E)
    (H : ContinuousMap.Homotopy (l ≫ p).hom (TopCat.const b : Z ⟶ B).hom) :
    homotopyFiberMapOfPathFamily p b l H ≫ homotopyFiberToTotal p b = l := by
  change (homotopyFiberMapOfPathFamily p b l H ≫
      pullback.fst (prod.map p (TopCat.const b)) (pathEndpoints B)) ≫ prod.fst = l
  rw [homotopyFiberMapOfPathFamily, pullback.lift_fst]
  exact prod.lift_fst _ _

/-- The lifted full path is exactly the specified family. -/
theorem homotopyFiberMapOfPathFamily_path {Z E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) (l : Z ⟶ E)
    (H : ContinuousMap.Homotopy (l ≫ p).hom (TopCat.const b : Z ⟶ B).hom) :
    homotopyFiberMapOfPathFamily p b l H ≫ homotopyFiberPath p b = homotopyPathMap H := by
  unfold homotopyFiberMapOfPathFamily
  exact pullback.lift_snd _ _ _

/-- Every parameter of the original path is retained pointwise. -/
theorem homotopyFiberMapOfPathFamily_path_apply {Z E B : TopCat.{u}}
    (p : E ⟶ B) (b : B) (l : Z ⟶ E)
    (H : ContinuousMap.Homotopy (l ≫ p).hom (TopCat.const b : Z ⟶ B).hom)
    (z : Z) (t : TopCat.I.{u}) :
    homotopyFiberPath p b (homotopyFiberMapOfPathFamily p b l H z) t =
      H.toContinuousMap (TopCat.I.homeomorph t, z) := by
  have h := ConcreteCategory.congr_hom (homotopyFiberMapOfPathFamily_path p b l H) z
  exact congrArg (fun r : pathObject B => r t) h

end TopCat

end
