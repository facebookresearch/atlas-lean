/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.TopCat.HomotopyTraceAction
public import MathlibExt.Topology.Homotopy.HomotopyGroupLoopShift

/-!
# Mixed-universe point traces on the original cube homotopy groups

The original homotopy factors through the target's compact-open path-map
space. Universal evaluation has the target universe, so the existing trace
comparison applies there. Original maps, group classes and point traces are
recovered explicitly. No original space is resized or root action replaced.
-/

public section

noncomputable section

open CategoryTheory
open scoped Topology Topology.Homotopy

universe u v w

namespace TopCat

/-- The actual zero-time evaluation continuous map on the target path-map space. -/
def mixedTraceEvalZero (Y : Type v) [TopologicalSpace Y] :
    C(C(unitInterval, Y), Y) :=
  ⟨fun p => p 0, continuous_eval_const 0⟩

/-- The actual one-time evaluation continuous map on the target path-map space. -/
def mixedTraceEvalOne (Y : Type v) [TopologicalSpace Y] :
    C(C(unitInterval, Y), Y) :=
  ⟨fun p => p 1, continuous_eval_const 1⟩

private theorem originalMixedEvalZeroValueComputed (Y : Type v) [TopologicalSpace Y]
    (p : C(unitInterval, Y)) : mixedTraceEvalZero Y p = p 0 := rfl
private theorem originalMixedEvalOneValueComputed (Y : Type v) [TopologicalSpace Y]
    (p : C(unitInterval, Y)) : mixedTraceEvalOne Y p = p 1 := rfl

/-- Actual defining-owner value of zero evaluation on EVERY original path map. -/
theorem mixedTraceEvalZero_apply (Y : Type v) [TopologicalSpace Y] (p : C(unitInterval, Y)) :
    mixedTraceEvalZero Y p = p 0 := originalMixedEvalZeroValueComputed Y p

/-- Actual defining-owner value of one evaluation on EVERY original path map. -/
theorem mixedTraceEvalOne_apply (Y : Type v) [TopologicalSpace Y] (p : C(unitInterval, Y)) :
    mixedTraceEvalOne Y p = p 1 := originalMixedEvalOneValueComputed Y p

/-- Currying the SAME original whole homotopy into its target path-map space. -/
def mixedTracePathMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) : C(X, C(unitInterval, Y)) :=
  (H.toContinuousMap.comp ContinuousMap.prodSwap).curry

private theorem originalMixedTracePathMapValueComputed
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (x : X) (t : unitInterval) :
    mixedTracePathMap H x t = H.toContinuousMap.toFun (t, x) := rfl



/-- Every original source point and time recover the actual original H value. -/
theorem mixedTracePathMap_apply
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (x : X) (t : unitInterval) :
    mixedTracePathMap H x t = H.toContinuousMap.toFun (t, x) :=
  originalMixedTracePathMapValueComputed H x t

/-- Zero-time evaluation recovers the entire original first map. -/
theorem mixedTraceEvalZero_comp
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    (mixedTraceEvalZero Y).comp (mixedTracePathMap H) = f := by
  apply ContinuousMap.ext
  intro x
  exact H.apply_zero x

/-- One-time evaluation recovers the entire original second map. -/
theorem mixedTraceEvalOne_comp
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) :
    (mixedTraceEvalOne Y).comp (mixedTracePathMap H) = g := by
  apply ContinuousMap.ext
  intro x
  exact H.apply_one x

private theorem originalMixedBasedMapRecover
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {f g : C(X, Y)} (h : f = g) (hp : f x = g x) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.mapHomOfEq f hp n a = HomotopyGroup.map g a := by
  cases h
  simp only [HomotopyGroup.mapHomOfEq_apply]

private theorem originalMixedBasedPostcompose
    {X : Type u} {P : Type v} {Y : Type w}
    [TopologicalSpace X] [TopologicalSpace P] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, P)) (g : C(P, Y)) (hp : g (f x) = y)
    (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.mapHomOfEq g hp n (HomotopyGroup.map f a) =
      HomotopyGroup.mapHomOfEq (g.comp f) hp n a := by
  have hComp := HomotopyGroup.mapHomOfEq_comp f g rfl hp hp n a
  have hFirst : HomotopyGroup.mapHomOfEq f rfl n a = HomotopyGroup.map f a :=
    HomotopyGroup.mapHomOfEq_apply f rfl n a
  have hValue := congrArg (fun b => HomotopyGroup.mapHomOfEq g hp n b) hFirst
  exact hValue.symm.trans hComp.symm

/-- The original positive cube maps of a mixed-universe homotopy differ by
transport along EXACTLY its actual original point trace. Both spaces retain
their independent universes and all original point/root/group data. -/
theorem homotopyGroup_map_homotopy_trace_mixed
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) (x : X)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) (H.evalAt x)
      (HomotopyGroup.map f a) = HomotopyGroup.map g a := by
  let P := C(unitInterval, Y)
  let e₀ : C(P, Y) := mixedTraceEvalZero Y
  let e₁ : C(P, Y) := mixedTraceEvalOne Y
  let c : C(X, P) := mixedTracePathMap H
  let p : P := c x
  let E : TopCat.Homotopy
      (TopCat.ofHom e₀ : TopCat.of P ⟶ TopCat.of Y) (TopCat.ofHom e₁) :=
    { toFun := fun z => z.2 z.1
      continuous_toFun := continuous_snd.eval continuous_fst
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl }
  have h₀ : e₀ p = f x := H.apply_zero x
  have h₁ : e₁ p = g x := H.apply_one x
  have hTrace : (E.evalAt p).cast h₀.symm h₁.symm = H.evalAt x := by
    apply _root_.Path.ext
    funext t
    rfl
  let b := HomotopyGroup.map c a
  have hUniversal := TopCat.homotopyGroup_map_homotopy_trace_of_eq n E p h₀ h₁ b
  have hF : HomotopyGroup.mapHomOfEq e₀ h₀ n b = HomotopyGroup.map f a :=
    (originalMixedBasedPostcompose c e₀ h₀ n a).trans
      (originalMixedBasedMapRecover (mixedTraceEvalZero_comp H) h₀ n a)
  have hG : HomotopyGroup.mapHomOfEq e₁ h₁ n b = HomotopyGroup.map g a :=
    (originalMixedBasedPostcompose c e₁ h₁ n a).trans
      (originalMixedBasedMapRecover (mixedTraceEvalOne_comp H) h₁ n a)
  calc
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) (H.evalAt x)
        (HomotopyGroup.map f a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
        ((E.evalAt p).cast h₀.symm h₁.symm) (HomotopyGroup.map f a) :=
      congrArg (fun q : _root_.Path (f x) (g x) =>
        TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) q
          (HomotopyGroup.map f a)) hTrace.symm
    _ = TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
        ((E.evalAt p).cast h₀.symm h₁.symm) (HomotopyGroup.mapHomOfEq e₀ h₀ n b) :=
      congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
        ((E.evalAt p).cast h₀.symm h₁.symm)) hF.symm
    _ = HomotopyGroup.mapHomOfEq e₁ h₁ n b := hUniversal
    _ = HomotopyGroup.map g a := hG

/-- An actual root-compatible mixed-universe whole homotopy gives identical
positive group maps of its original maps followed by their designated roots.
This retains the existing basepoint action, including its nontrivial cases. -/
theorem homotopyGroup_rooted_map_homotopy_mixed
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) {x : X} {y : Y} {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) (p : _root_.Path (f x) y)
    (q : _root_.Path (g x) y) (hRoot : ((H.evalAt x).trans q).Homotopic p) :
    (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p).toMonoidHom.comp
        (HomotopyGroup.mapHom f) =
      (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) q).toMonoidHom.comp
        (HomotopyGroup.mapHom g) := by
  ext a
  have hR := TopCat.homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic
    n (TopCat.of Y) hRoot
  have hT := TopCat.homotopyGroupBasepointChangeMulEquiv_trans
    n (TopCat.of Y) (H.evalAt x) q
  have hH := homotopyGroup_map_homotopy_trace_mixed n H x a
  calc
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p
        (HomotopyGroup.map f a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) ((H.evalAt x).trans q)
        (HomotopyGroup.map f a) :=
      congrArg (fun e => e (HomotopyGroup.map f a)) hR.symm
    _ = TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) q
        (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) (H.evalAt x)
          (HomotopyGroup.map f a)) :=
      congrArg (fun e => e (HomotopyGroup.map f a)) hT
    _ = TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) q
        (HomotopyGroup.map g a) := congrArg
      (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) q) hH

end TopCat

end
