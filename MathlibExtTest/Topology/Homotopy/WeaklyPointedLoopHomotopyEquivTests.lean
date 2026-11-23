/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopyEquiv
import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopies
import MathlibExt.Topology.Homotopy.ContinuousMappedLoopHomotopy

/-!
# Public weakly pointed loop API clients

The generic source and target have independent universes. The loop-space
families are the actual jointly continuous data returned by the public APIs.
The identity/reflexive-path case retains the original padding and checks its
homotopy to identity. No topology model is required on either raw loop space.
-/

noncomputable section

open ContinuousMap
open scoped Topology ContinuousMap

universe u v w

section MappedFamilies

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {f g : C(X, Y)}

example (H : ContinuousMap.HomotopyRel f g {x}) :
    C(unitInterval × LoopSpace X x, LoopSpace Y (f x)) := H.mappedLoopFamily

example (H : ContinuousMap.HomotopyRel f g {x}) :
    Continuous (H.mappedLoopFamily :
      unitInterval × LoopSpace X x → LoopSpace Y (f x)) :=
  H.mappedLoopFamily.continuous

example (H : ContinuousMap.HomotopyRel f g {x}) (gamma : LoopSpace X x) :
    H.mappedLoopFamily (0, gamma) = gamma.map f.continuous :=
  H.mappedLoopFamily_zero gamma

example (H : ContinuousMap.HomotopyRel f g {x}) (gamma : LoopSpace X x) :
    H.mappedLoopFamily (1, gamma) =
      (gamma.map g.continuous).cast
        (H.fst_eq_snd (Set.mem_singleton x))
        (H.fst_eq_snd (Set.mem_singleton x)) :=
  H.mappedLoopFamily_one gamma

example (H : ContinuousMap.HomotopyRel f g {x}) :
    ContinuousMap.Homotopy
      (H.mappedLoopFamily.comp
        ⟨fun gamma => ((0 : unitInterval), gamma),
          continuous_const.prodMk continuous_id⟩)
      (H.mappedLoopFamily.comp
        ⟨fun gamma => ((1 : unitInterval), gamma),
          continuous_const.prodMk continuous_id⟩) :=
  H.mappedLoopFamilyHomotopy

end MappedFamilies

section OrdinaryTrace

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}

example (H : ContinuousMap.Homotopy f g) (x : X) :
    C(unitInterval × LoopSpace X x, LoopSpace Y (g x)) :=
  H.traceLoopFamily x

example (H : ContinuousMap.Homotopy f g) (x : X) (gamma : LoopSpace X x) :
    H.traceLoopFamily x (0, gamma) =
      loopBasepointChange (H.evalAt x) (strictLoopMap f x gamma) :=
  H.traceLoopFamily_zero x gamma

example (H : ContinuousMap.Homotopy f g) (x : X) (gamma : LoopSpace X x) :
    H.traceLoopFamily x (1, gamma) =
      loopBasepointChange (Path.refl (g x)) (strictLoopMap g x gamma) :=
  H.traceLoopFamily_one x gamma

example (H : ContinuousMap.Homotopy f g) (x : X) :
    ContinuousMap.Homotopy
      ((loopBasepointChange (H.evalAt x)).comp (strictLoopMap f x))
      (strictLoopMap g x) :=
  H.traceConjugationLoopHomotopy x

end OrdinaryTrace

section WeaklyPointedFamilies

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

example (f : WeaklyPointed x y) (g : WeaklyPointed y z) :
    ContinuousMap.Homotopy ((WeaklyPointed.comp f g).loopMap)
      (g.loopMap.comp f.loopMap) :=
  WeaklyPointed.loopMapCompHomotopy f g

example (f g : WeaklyPointed x y)
    (H : ContinuousMap.Homotopy f.hom g.hom)
    (Hp : f.rootPath.Homotopy ((H.evalAt x).trans g.rootPath)) :
    ContinuousMap.Homotopy f.loopMap g.loopMap :=
  WeaklyPointed.loopMapHomotopyOfMap f g H Hp

example (f : WeaklyPointed x y) :
    ContinuousMap.Homotopy f.loopMap f.loopMap :=
  WeaklyPointed.loopMapRootPathHomotopy f.hom (Path.Homotopy.refl f.rootPath)

end WeaklyPointedFamilies

section InducedEquivalence

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  (e : X ≃ₕ Y) (x : X) {y : Y} (p : Path (e.toFun x) y)

example : LoopSpace X x ≃ₕ LoopSpace Y y :=
  e.weaklyPointedLoopHomotopyEquiv x p

example :
    (e.weaklyPointedLoopHomotopyEquiv x p).toFun =
      (⟨e.toFun, p⟩ : WeaklyPointed x y).loopMap :=
  HomotopyEquiv.weaklyPointedLoopHomotopyEquiv_toFun e x p

example :
    let E := e.weaklyPointedLoopHomotopyEquiv x p
    ContinuousMap.Homotopy (E.invFun.comp E.toFun)
      (ContinuousMap.id (LoopSpace X x)) :=
  (e.weaklyPointedLoopHomotopyEquiv x p).left_inv.some

example :
    let E := e.weaklyPointedLoopHomotopyEquiv x p
    ContinuousMap.Homotopy (E.toFun.comp E.invFun)
      (ContinuousMap.id (LoopSpace Y y)) :=
  (e.weaklyPointedLoopHomotopyEquiv x p).right_inv.some

example (gamma : LoopSpace X x) :
    let E := e.weaklyPointedLoopHomotopyEquiv x p
    E.left_inv.some (0, gamma) = E.invFun (E.toFun gamma) :=
  (e.weaklyPointedLoopHomotopyEquiv x p).left_inv.some.apply_zero gamma

example (gamma : LoopSpace X x) :
    let E := e.weaklyPointedLoopHomotopyEquiv x p
    E.left_inv.some (1, gamma) = gamma :=
  (e.weaklyPointedLoopHomotopyEquiv x p).left_inv.some.apply_one gamma

example (gamma : LoopSpace Y y) :
    let E := e.weaklyPointedLoopHomotopyEquiv x p
    E.right_inv.some (0, gamma) = E.toFun (E.invFun gamma) :=
  (e.weaklyPointedLoopHomotopyEquiv x p).right_inv.some.apply_zero gamma

example (gamma : LoopSpace Y y) :
    let E := e.weaklyPointedLoopHomotopyEquiv x p
    E.right_inv.some (1, gamma) = gamma :=
  (e.weaklyPointedLoopHomotopyEquiv x p).right_inv.some.apply_one gamma

example :
    let E := e.weaklyPointedLoopHomotopyEquiv x p
    Continuous (E.left_inv.some :
      unitInterval × LoopSpace X x → LoopSpace X x) :=
  (e.weaklyPointedLoopHomotopyEquiv x p).left_inv.some.continuous

example :
    let E := e.weaklyPointedLoopHomotopyEquiv x p
    Continuous (E.right_inv.some :
      unitInterval × LoopSpace Y y → LoopSpace Y y) :=
  (e.weaklyPointedLoopHomotopyEquiv x p).right_inv.some.continuous

end InducedEquivalence

section ReflexiveIdentity

variable {X : Type u} [TopologicalSpace X] (x : X)

example : LoopSpace X x ≃ₕ LoopSpace X x :=
  (HomotopyEquiv.refl X).weaklyPointedLoopHomotopyEquiv x (Path.refl x)

example (gamma : LoopSpace X x) :
    ((HomotopyEquiv.refl X).weaklyPointedLoopHomotopyEquiv x (Path.refl x)).toFun gamma =
      (Path.refl x).symm.trans
        ((gamma.map (ContinuousMap.id X).continuous).trans (Path.refl x)) := by
  have h := HomotopyEquiv.weaklyPointedLoopHomotopyEquiv_toFun
    (HomotopyEquiv.refl X) x (Path.refl x)
  exact (congrArg (fun F : C(LoopSpace X x, LoopSpace X x) => F gamma) h).trans
    (WeaklyPointed.loopMap_apply
      (⟨ContinuousMap.id X, Path.refl x⟩ : WeaklyPointed x x) gamma)

private def identityLoopForwardHomotopy :
    ContinuousMap.Homotopy
      ((HomotopyEquiv.refl X).weaklyPointedLoopHomotopyEquiv x (Path.refl x)).toFun
      (ContinuousMap.id (LoopSpace X x)) :=
  (WeaklyPointed.loopMapIdHomotopy x).cast
    (HomotopyEquiv.weaklyPointedLoopHomotopyEquiv_toFun
      (HomotopyEquiv.refl X) x (Path.refl x)).symm rfl

example :
    ContinuousMap.Homotopy
      ((HomotopyEquiv.refl X).weaklyPointedLoopHomotopyEquiv x (Path.refl x)).toFun
      (ContinuousMap.id (LoopSpace X x)) :=
  identityLoopForwardHomotopy x

example (gamma : LoopSpace X x) :
    identityLoopForwardHomotopy x (0, gamma) =
      ((HomotopyEquiv.refl X).weaklyPointedLoopHomotopyEquiv x
        (Path.refl x)).toFun gamma :=
  (identityLoopForwardHomotopy x).apply_zero gamma

example (gamma : LoopSpace X x) :
    identityLoopForwardHomotopy x (1, gamma) = gamma :=
  (identityLoopForwardHomotopy x).apply_one gamma

example :
    let E := (HomotopyEquiv.refl X).weaklyPointedLoopHomotopyEquiv x (Path.refl x)
    ContinuousMap.Homotopy (E.invFun.comp E.toFun)
      (ContinuousMap.id (LoopSpace X x)) :=
  ((HomotopyEquiv.refl X).weaklyPointedLoopHomotopyEquiv x
    (Path.refl x)).left_inv.some

example :
    let E := (HomotopyEquiv.refl X).weaklyPointedLoopHomotopyEquiv x (Path.refl x)
    ContinuousMap.Homotopy (E.toFun.comp E.invFun)
      (ContinuousMap.id (LoopSpace X x)) :=
  ((HomotopyEquiv.refl X).weaklyPointedLoopHomotopyEquiv x
    (Path.refl x)).right_inv.some

end ReflexiveIdentity

end
