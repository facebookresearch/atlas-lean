/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopMultiplication
public import MathlibExt.Topology.Homotopy.TopCat.HomotopyTraceAction

/-!
# Positive homotopy-group maps with the original chosen root path

The actual cube map is followed by the existing basepoint transport along
exactly the root path of the supplied weakly pointed map. Source and target
carrier universes remain independent. The target unit is its own constant
cube class. The original continuous loop map also receives an internally
derived root to its own constant loop. Equality-point calibration retains the existing
equality-aware
map, and endpoint-fixed root homotopy retains this same transport.
-/

noncomputable section

open scoped Topology

universe u v

namespace ContinuousMap.WeaklyPointed

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

private theorem originalLoopMapUnitPathValueComputed (f : WeaklyPointed x y) (t s : unitInterval) :
    loopMapUnitPath f t s = loopMapUnitHomotopy f (t, s) :=
  loopMapUnitPath_apply f t s

/-- Every loop/path clock is evaluation of the same original unit homotopy. -/
public theorem loopMapUnitPath_value (f : WeaklyPointed x y) (t s : unitInterval) :
    loopMapUnitPath f t s = loopMapUnitHomotopy f (t, s) :=
  originalLoopMapUnitPathValueComputed f t s

/-- The actual loop map, rooted at its original constant loops by that derived path. -/
public def loopWeaklyPointedMap (f : WeaklyPointed x y) :
    WeaklyPointed (Path.refl x) (Path.refl y) where
  hom := f.loopMap
  rootPath := loopMapUnitPath f

private theorem originalLoopWeakMapHomValueComputed (f : WeaklyPointed x y) :
    (loopWeaklyPointedMap f).hom = f.loopMap :=
  rfl

/-- The whole underlying loop map is the original conjugation map. -/
public theorem loopWeaklyPointedMap_hom (f : WeaklyPointed x y) :
    (loopWeaklyPointedMap f).hom = f.loopMap :=
  originalLoopWeakMapHomValueComputed f

private theorem originalLoopWeakMapRootValueComputed (f : WeaklyPointed x y) :
    (loopWeaklyPointedMap f).rootPath =
      (loopMapUnitPath f).cast
        (congrArg (fun m => m (Path.refl x)) (loopWeaklyPointedMap_hom f)) rfl :=
  rfl

/-- The chosen loop root is the internally derived path to its own target unit. -/
public theorem loopWeaklyPointedMap_rootPath (f : WeaklyPointed x y) :
    (loopWeaklyPointedMap f).rootPath =
      (loopMapUnitPath f).cast
        (congrArg (fun m => m (Path.refl x)) (loopWeaklyPointedMap_hom f)) rfl :=
  originalLoopWeakMapRootValueComputed f

private def originalPositiveHomotopyGroupMapValue
    (n : ℕ) (f : WeaklyPointed x y) :
    HomotopyGroup.Pi (n + 1) X x →* HomotopyGroup.Pi (n + 1) Y y :=
  (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
    f.rootPath).toMonoidHom.comp (HomotopyGroup.mapHom f.hom)

/-- The actual positive group map uses the original continuous map and root. -/
public def positiveHomotopyGroupMap (n : ℕ) (f : WeaklyPointed x y) :
    HomotopyGroup.Pi (n + 1) X x →* HomotopyGroup.Pi (n + 1) Y y :=
  originalPositiveHomotopyGroupMapValue n f

private theorem originalPositiveGroupMapValueComputed
    (n : ℕ) (f : WeaklyPointed x y) :
    positiveHomotopyGroupMap n f =
      (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
        f.rootPath).toMonoidHom.comp (HomotopyGroup.mapHom f.hom) :=
  rfl

/-- The whole map is the original cube map followed by the original transport. -/
public theorem positiveHomotopyGroupMap_value
    (n : ℕ) (f : WeaklyPointed x y) :
    positiveHomotopyGroupMap n f =
      (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
        f.rootPath).toMonoidHom.comp (HomotopyGroup.mapHom f.hom) :=
  originalPositiveGroupMapValueComputed n f

private theorem originalPositiveGroupMapApplyComputed
    (n : ℕ) (f : WeaklyPointed x y) (a : HomotopyGroup.Pi (n + 1) X x) :
    positiveHomotopyGroupMap n f a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) f.rootPath
        (HomotopyGroup.map f.hom a) :=
  rfl

/-- Every original homotopy class follows that exact root transport. -/
public theorem positiveHomotopyGroupMap_apply
    (n : ℕ) (f : WeaklyPointed x y) (a : HomotopyGroup.Pi (n + 1) X x) :
    positiveHomotopyGroupMap n f a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) f.rootPath
        (HomotopyGroup.map f.hom a) :=
  originalPositiveGroupMapApplyComputed n f a

/-- Every actual cube representative is mapped before that same root transport. -/
public theorem positiveHomotopyGroupMap_mk
    (n : ℕ) (f : WeaklyPointed x y) (p : GenLoop (Fin (n + 1)) X x) :
    positiveHomotopyGroupMap n f (HomotopyGroup.mk p) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) f.rootPath
        (HomotopyGroup.mk (GenLoop.map f.hom p)) := by
  rw [positiveHomotopyGroupMap_apply, HomotopyGroup.map_mk]

/-- The actual target unit is preserved in every positive degree. -/
public theorem positiveHomotopyGroupMap_one
    (n : ℕ) (f : WeaklyPointed x y) :
    positiveHomotopyGroupMap n f (1 : HomotopyGroup.Pi (n + 1) X x) =
      (1 : HomotopyGroup.Pi (n + 1) Y y) :=
  (positiveHomotopyGroupMap n f).map_one

/-- Both units are their own original constant cube classes. -/
public theorem positiveHomotopyGroupMap_const
    (n : ℕ) (f : WeaklyPointed x y) :
    positiveHomotopyGroupMap n f
        (HomotopyGroup.mk (GenLoop.const (N := Fin (n + 1)) (X := X) (x := x))) =
      HomotopyGroup.mk (GenLoop.const (N := Fin (n + 1)) (X := Y) (x := y)) := by
  simpa only [← HomotopyGroup.one_eq_mk_const] using positiveHomotopyGroupMap_one n f

/-- The inverse of the same chosen transport recovers the actual cube-map value. -/
public theorem positiveHomotopyGroupMap_transport_inverse
    (n : ℕ) (f : WeaklyPointed x y) (a : HomotopyGroup.Pi (n + 1) X x) :
    (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) f.rootPath).symm
        (positiveHomotopyGroupMap n f a) = HomotopyGroup.map f.hom a :=
  by
    rw [positiveHomotopyGroupMap_apply]
    exact (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
      f.rootPath).symm_apply_apply (HomotopyGroup.map f.hom a)

/-- The other composition of the same target root transport fixes every class. -/
public theorem positiveHomotopyGroupMap_transport_right_inverse
    (n : ℕ) (f : WeaklyPointed x y) (b : HomotopyGroup.Pi (n + 1) Y y) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) f.rootPath
        ((TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
          f.rootPath).symm b) = b :=
  (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
    f.rootPath).apply_symm_apply b

private theorem originalPositiveGroupMapOfEqComputed
    (n : ℕ) (f : C(X, Y)) (h : f x = y)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    positiveHomotopyGroupMap n
        (⟨f, (Path.refl (f x)).cast rfl h.symm⟩ : WeaklyPointed x y) a =
      HomotopyGroup.mapHomOfEq f h n a := by
  subst y
  change TopCat.homotopyGroupBasepointChangeMulEquiv.{v} n (TopCat.of Y)
      (Path.refl (f x)) (HomotopyGroup.map f a) = HomotopyGroup.map f a
  have hRefl : TopCat.homotopyGroupBasepointChangeMulEquiv.{v} n (TopCat.of Y)
      (Path.refl (f x)) = MulEquiv.refl (HomotopyGroup.Pi (n + 1) Y (f x)) :=
    TopCat.homotopyGroupBasepointChangeMulEquiv_refl.{v} n (TopCat.of Y) (f x)
  exact (congrArg
    (fun e : HomotopyGroup.Pi (n + 1) Y (f x) ≃* HomotopyGroup.Pi (n + 1) Y (f x) =>
      e (HomotopyGroup.map f a)) hRefl).trans (MulEquiv.refl_apply (HomotopyGroup.map f a))

/-- A specified point equality calibrates to the existing equality-aware map. -/
public theorem positiveHomotopyGroupMap_of_eq
    (n : ℕ) (f : C(X, Y)) (h : f x = y)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    positiveHomotopyGroupMap n
        (⟨f, (Path.refl (f x)).cast rfl h.symm⟩ : WeaklyPointed x y) a =
      HomotopyGroup.mapHomOfEq f h n a :=
  originalPositiveGroupMapOfEqComputed n f h a

/-- The original weakly pointed identity fixes every original positive class. -/
public theorem positiveHomotopyGroupMap_id
    (x : X) (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X x) :
    positiveHomotopyGroupMap n (id x) a = a :=
  (positiveHomotopyGroupMap_of_eq n (ContinuousMap.id X) rfl a).trans
    (HomotopyGroup.mapHomOfEq_id x n a)

/-- Homotopic endpoint-fixed roots retain this exact positive group map. -/
public theorem positiveHomotopyGroupMap_root_homotopic
    (n : ℕ) (f : C(X, Y)) {p q : Path (f x) y} (h : p.Homotopic q) :
    positiveHomotopyGroupMap n (⟨f, p⟩ : WeaklyPointed x y) =
      positiveHomotopyGroupMap n (⟨f, q⟩ : WeaklyPointed x y) := by
  ext a
  change TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p
      (HomotopyGroup.map f a) =
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) q
      (HomotopyGroup.map f a)
  exact congrArg (fun e => e (HomotopyGroup.map f a))
    (TopCat.homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic n (TopCat.of Y) h)

/-- Positive homotopy groups of the original ordinary loop carriers use that actual unit path. -/
public def positiveLoopHomotopyGroupMap (n : ℕ) (f : WeaklyPointed x y) :
    HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x) →*
      HomotopyGroup.Pi (n + 1) (LoopSpace Y y) (Path.refl y) :=
  positiveHomotopyGroupMap n (loopWeaklyPointedMap f)

private theorem originalPositiveLoopGroupMapApplyComputed
    (n : ℕ) (f : WeaklyPointed x y)
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    positiveLoopHomotopyGroupMap n f a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (LoopSpace Y y))
        (loopMapUnitPath f) (HomotopyGroup.map f.loopMap a) :=
  rfl

/-- The original continuous loop map is followed by its derived own-unit transport. -/
public theorem positiveLoopHomotopyGroupMap_apply
    (n : ℕ) (f : WeaklyPointed x y)
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    positiveLoopHomotopyGroupMap n f a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (LoopSpace Y y))
        (loopMapUnitPath f) (HomotopyGroup.map f.loopMap a) :=
  originalPositiveLoopGroupMapApplyComputed n f a

/-- The actual group map on ordinary loops preserves its own target group unit. -/
public theorem positiveLoopHomotopyGroupMap_one
    (n : ℕ) (f : WeaklyPointed x y) :
    positiveLoopHomotopyGroupMap n f (1 :
        HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) =
      (1 : HomotopyGroup.Pi (n + 1) (LoopSpace Y y) (Path.refl y)) :=
  (positiveLoopHomotopyGroupMap n f).map_one

end ContinuousMap.WeaklyPointed

end
