/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.MixedHomotopyGroupTrace

/-!
# Original mixed-space basepoint naturality by path-space class lifting

Actual constant paths grow to the specified path in the original path-map
space. The original basepoint action lifts every original cube class there;
zero evaluation recovers it. Universal evaluation and actual path-map
postcomposition then recover mixed-universe naturality of the original action.
-/

public section

noncomputable section

open CategoryTheory
open scoped Topology Topology.Homotopy

universe u v

namespace TopCat

/-- The original constant-path continuous map, with actual compact-open topology. -/
def mixedTraceConstantPaths (X : Type u) [TopologicalSpace X] : C(X, C(unitInterval, X)) :=
  (ContinuousMap.fst : C(X × unitInterval, X)).curry

private theorem originalConstantPathValueComputed
    (X : Type u) [TopologicalSpace X] (x : X) (t : unitInterval) :
    mixedTraceConstantPaths X x t = x := rfl

private theorem originalZeroConstantCompositeComputed (X : Type u) [TopologicalSpace X] :
    (mixedTraceEvalZero X).comp (mixedTraceConstantPaths X) = ContinuousMap.id X := by
  apply ContinuousMap.ext
  intro x
  exact (mixedTraceEvalZero_apply X (mixedTraceConstantPaths X x)).trans
    (originalConstantPathValueComputed X x 0)

/-- Zero evaluation of the actual constant-path map is the original identity map. -/
theorem mixedTraceEvalZero_comp_constantPaths (X : Type u) [TopologicalSpace X] :
    (mixedTraceEvalZero X).comp (mixedTraceConstantPaths X) = ContinuousMap.id X :=
  originalZeroConstantCompositeComputed X

/-- The actual truncation family grows the original constant source path to p. -/
def mixedTracePathGrowth
    {X : Type u} [TopologicalSpace X] (p : C(unitInterval, X)) :
    _root_.Path (mixedTraceConstantPaths X (p 0)) p := by
  let G : C(unitInterval × unitInterval, X) :=
    ⟨fun z => p (Set.Icc.convexComb 0 z.2 z.1), by fun_prop⟩
  refine { toContinuousMap := G.curry, source' := ?_, target' := ?_ }
  · apply ContinuousMap.ext
    intro t
    change p (Set.Icc.convexComb 0 t 0) = p 0
    exact congrArg p (Set.Icc.convexComb_zero 0 t)
  · apply ContinuousMap.ext
    intro t
    change p (Set.Icc.convexComb 0 t 1) = p t
    exact congrArg p (Set.Icc.convexComb_one 0 t)

private theorem originalGrowthPathValueComputed
    {X : Type u} [TopologicalSpace X] (p : C(unitInterval, X))
    (t s : unitInterval) :
    mixedTracePathGrowth p t s = p (Set.Icc.convexComb 0 s t) := rfl

/-- Zero-time evaluation of the actual growth path is the SAME original reflexive path. -/
theorem mixedTracePathGrowth_evalZero
    {X : Type u} [TopologicalSpace X] (p : C(unitInterval, X)) :
    ((mixedTracePathGrowth p).map (mixedTraceEvalZero X).continuous).cast
        (DFunLike.congr_fun (mixedTraceEvalZero_comp_constantPaths X) (p 0)).symm
        (mixedTraceEvalZero_apply X p).symm = _root_.Path.refl (p 0) := by
  apply _root_.Path.ext
  funext t
  change mixedTraceEvalZero X ((mixedTracePathGrowth p).toContinuousMap.toFun t) = p 0
  exact (mixedTraceEvalZero_apply X _).trans
    ((originalGrowthPathValueComputed p t 0).trans
      (congrArg p (Set.Icc.convexComb_eq 0 t)))

private theorem originalStrictEvaluationMapCongr
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f g : C(X, Y))
    (hf : f x = y) (hg : g x = y) (h : f = g)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.mapHomOfEq f hf n a = HomotopyGroup.mapHomOfEq g hg n a := by
  cases h
  have hProof : hf = hg := Subsingleton.elim _ _
  cases hProof
  rfl

private theorem originalStrictEvaluationAction
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ x₁ : X} {y₀ y₁ : Y} (n : ℕ) (f : C(X, Y)) (p : _root_.Path x₀ x₁)
    (h₀ : f x₀ = y₀) (h₁ : f x₁ = y₁)
    (a : HomotopyGroup.Pi (n + 1) X x₀) :
    HomotopyGroup.mapHomOfEq f h₁ n
        (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of X) p a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
        ((p.map f.continuous).cast h₀.symm h₁.symm)
        (HomotopyGroup.mapHomOfEq f h₀ n a) := by
  subst y₀
  subst y₁
  simpa only [TopCat.hom_ofHom, HomotopyGroup.mapHomOfEq_apply,
    _root_.Path.cast_rfl_rfl] using
    TopCat.homotopyGroupBasepointChangeMulEquiv_naturality n
      (TopCat.ofHom f : TopCat.of X ⟶ TopCat.of Y) p a

private theorem originalStrictEvaluationTrace
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y₀ y₁ : Y} {f g : C(X, Y)} (n : ℕ)
    (H : ContinuousMap.Homotopy f g) (h₀ : f x = y₀) (h₁ : g x = y₁)
    (p : _root_.Path y₀ y₁)
    (hTrace : (H.evalAt x).cast h₀.symm h₁.symm = p)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p
        (HomotopyGroup.mapHomOfEq f h₀ n a) = HomotopyGroup.mapHomOfEq g h₁ n a := by
  subst y₀
  subst y₁
  have hTrace' : H.evalAt x = p := by
    simpa only [_root_.Path.cast_rfl_rfl] using hTrace
  rw [HomotopyGroup.mapHomOfEq_apply, HomotopyGroup.mapHomOfEq_apply]
  exact (congrArg (fun q : _root_.Path (f x) (g x) =>
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) q
      (HomotopyGroup.map f a)) hTrace'.symm).trans
        (TopCat.homotopyGroup_map_homotopy_trace_mixed n H x a)

/-- Every original class lifts along the ACTUAL specified growth path. -/
def mixedTracePathClassLift
    {X : Type u} [TopologicalSpace X] (n : ℕ) (p : C(unitInterval, X))
    (a : HomotopyGroup.Pi (n + 1) X (p 0)) :
    HomotopyGroup.Pi (n + 1) C(unitInterval, X) p :=
  TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of C(unitInterval, X))
    (mixedTracePathGrowth p) (HomotopyGroup.map (mixedTraceConstantPaths X) a)

private theorem originalPathClassLiftValueComputed
    {X : Type u} [TopologicalSpace X] (n : ℕ) (p : C(unitInterval, X))
    (a : HomotopyGroup.Pi (n + 1) X (p 0)) :
    mixedTracePathClassLift n p a =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of C(unitInterval, X))
        (mixedTracePathGrowth p) (HomotopyGroup.map (mixedTraceConstantPaths X) a) := rfl

/-- Evaluation recovers EVERY original class; no surjectivity outcome is an input. -/
theorem mixedTracePathClassLift_evalZero
    {X : Type u} [TopologicalSpace X] (n : ℕ) (p : C(unitInterval, X))
    (a : HomotopyGroup.Pi (n + 1) X (p 0)) :
    HomotopyGroup.mapHomOfEq (mixedTraceEvalZero X) (mixedTraceEvalZero_apply X p) n
      (mixedTracePathClassLift n p a) = a := by
  let c := mixedTraceConstantPaths X
  let e := mixedTraceEvalZero X
  let R := mixedTracePathGrowth p
  have hComp : e.comp c = ContinuousMap.id X := mixedTraceEvalZero_comp_constantPaths X
  let h₀ : e (c (p 0)) = p 0 := DFunLike.congr_fun hComp (p 0)
  let h₁ : e p = p 0 := mixedTraceEvalZero_apply X p
  have hStep := HomotopyGroup.mapHomOfEq_comp c e rfl h₀ h₀ n a
  have hId := originalStrictEvaluationMapCongr n (e.comp c) (ContinuousMap.id X)
    h₀ rfl hComp a
  have hMaps : HomotopyGroup.mapHomOfEq e h₀ n (HomotopyGroup.map c a) = a := by
    simpa only [HomotopyGroup.mapHomOfEq_apply] using
      hStep.symm.trans (hId.trans (HomotopyGroup.mapHomOfEq_id (p 0) n a))
  have hNat := originalStrictEvaluationAction n e R h₀ h₁ (HomotopyGroup.map c a)
  have hTransport : TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of X)
      ((R.map e.continuous).cast h₀.symm h₁.symm) =
        MulEquiv.refl (HomotopyGroup.Pi (n + 1) X (p 0)) :=
    (congrArg (fun q : _root_.Path (p 0) (p 0) =>
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of X) q)
        (mixedTracePathGrowth_evalZero p)).trans
          (TopCat.homotopyGroupBasepointChangeMulEquiv_refl n (TopCat.of X) (p 0))
  rw [originalPathClassLiftValueComputed]
  exact hNat.trans
    ((congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of X)
      ((R.map e.continuous).cast h₀.symm h₁.symm)) hMaps).trans
        (congrArg (fun e : HomotopyGroup.Pi (n + 1) X (p 0) ≃*
          HomotopyGroup.Pi (n + 1) X (p 0) => e a) hTransport))

/-- Actual path-map postcomposition between INDEPENDENT original path-map spaces. -/
def mixedTracePostcomposePaths
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : C(C(unitInterval, X), C(unitInterval, Y)) :=
  (f.comp (⟨fun z : C(unitInterval, X) × unitInterval => z.1 z.2,
    continuous_fst.eval continuous_snd⟩ : C(C(unitInterval, X) × unitInterval, X))).curry

private theorem originalPostcomposePathValueComputed
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (p : C(unitInterval, X)) (t : unitInterval) :
    mixedTracePostcomposePaths f p t = f (p t) := rfl

private theorem originalUniversalPathTrace
    {X : Type u} [TopologicalSpace X] (n : ℕ) (p : C(unitInterval, X))
    (a : HomotopyGroup.Pi (n + 1) C(unitInterval, X) p) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of X)
        (⟨p, rfl, rfl⟩ : _root_.Path (p 0) (p 1))
        (HomotopyGroup.mapHomOfEq (mixedTraceEvalZero X) (mixedTraceEvalZero_apply X p) n a) =
      HomotopyGroup.mapHomOfEq (mixedTraceEvalOne X) (mixedTraceEvalOne_apply X p) n a := by
  let E : ContinuousMap.Homotopy (mixedTraceEvalZero X) (mixedTraceEvalOne X) :=
    { toFun := fun z => z.2 z.1
      continuous_toFun := continuous_snd.eval continuous_fst
      map_zero_left := fun r => (mixedTraceEvalZero_apply X r).symm
      map_one_left := fun r => (mixedTraceEvalOne_apply X r).symm }
  have hTrace : (E.evalAt p).cast (mixedTraceEvalZero_apply X p).symm
      (mixedTraceEvalOne_apply X p).symm =
        (⟨p, rfl, rfl⟩ : _root_.Path (p 0) (p 1)) := by
    apply _root_.Path.ext
    funext t
    rfl
  exact originalStrictEvaluationTrace n E (mixedTraceEvalZero_apply X p)
    (mixedTraceEvalOne_apply X p) _ hTrace a

/-- The ORIGINAL basepoint action commutes with the ORIGINAL cube map across
independent source and target universes, along the SAME original p. -/
theorem homotopyGroupBasepointChangeMulEquiv_naturality_mixed
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) {x y : X} (p : _root_.Path x y)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.map f
        (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of X) p a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
        (p.map f.continuous) (HomotopyGroup.map f a) := by
  rcases p with ⟨p, h₀, h₁⟩
  cases h₀
  cases h₁
  let c := mixedTracePathClassLift n p a
  let F := mixedTracePostcomposePaths f
  let q := F p
  let b := HomotopyGroup.map F c
  let hX₀ := mixedTraceEvalZero_apply X p
  let hX₁ := mixedTraceEvalOne_apply X p
  have hY₀ : mixedTraceEvalZero Y q = f (p 0) :=
    (mixedTraceEvalZero_apply Y q).trans (originalPostcomposePathValueComputed f p 0)
  have hY₁ : mixedTraceEvalOne Y q = f (p 1) :=
    (mixedTraceEvalOne_apply Y q).trans (originalPostcomposePathValueComputed f p 1)
  have h₀ : (mixedTraceEvalZero Y).comp F = f.comp (mixedTraceEvalZero X) := by
    apply ContinuousMap.ext
    intro r
    change mixedTraceEvalZero Y (F r) = f (mixedTraceEvalZero X r)
    exact (mixedTraceEvalZero_apply Y (F r)).trans
      ((originalPostcomposePathValueComputed f r 0).trans
        (congrArg f (mixedTraceEvalZero_apply X r)).symm)
  have h₁ : (mixedTraceEvalOne Y).comp F = f.comp (mixedTraceEvalOne X) := by
    apply ContinuousMap.ext
    intro r
    change mixedTraceEvalOne Y (F r) = f (mixedTraceEvalOne X r)
    exact (mixedTraceEvalOne_apply Y (F r)).trans
      ((originalPostcomposePathValueComputed f r 1).trans
        (congrArg f (mixedTraceEvalOne_apply X r)).symm)
  have hMapZero : HomotopyGroup.mapHomOfEq (mixedTraceEvalZero Y) hY₀ n b =
      HomotopyGroup.map f a := by
    have hPost := HomotopyGroup.mapHomOfEq_comp F (mixedTraceEvalZero Y)
      rfl hY₀ hY₀ n c
    have hWhole := originalStrictEvaluationMapCongr n
      ((mixedTraceEvalZero Y).comp F) (f.comp (mixedTraceEvalZero X))
      hY₀ (congrArg f hX₀) h₀ c
    have hSource := HomotopyGroup.mapHomOfEq_comp (mixedTraceEvalZero X) f
      hX₀ rfl (congrArg f hX₀) n c
    have hRecovery := congrArg (HomotopyGroup.mapHomOfEq f rfl n)
      (mixedTracePathClassLift_evalZero n p a)
    simpa only [HomotopyGroup.mapHomOfEq_apply] using
      hPost.symm.trans (hWhole.trans (hSource.trans hRecovery))
  have hMapOne : HomotopyGroup.mapHomOfEq (mixedTraceEvalOne Y) hY₁ n b =
      HomotopyGroup.map f
        (HomotopyGroup.mapHomOfEq (mixedTraceEvalOne X) hX₁ n c) := by
    have hPost := HomotopyGroup.mapHomOfEq_comp F (mixedTraceEvalOne Y)
      rfl hY₁ hY₁ n c
    have hWhole := originalStrictEvaluationMapCongr n
      ((mixedTraceEvalOne Y).comp F) (f.comp (mixedTraceEvalOne X))
      hY₁ (congrArg f hX₁) h₁ c
    have hSource := HomotopyGroup.mapHomOfEq_comp (mixedTraceEvalOne X) f
      hX₁ rfl (congrArg f hX₁) n c
    simpa only [HomotopyGroup.mapHomOfEq_apply] using
      hPost.symm.trans (hWhole.trans hSource)
  have hX : TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of X)
      (⟨p, rfl, rfl⟩ : _root_.Path (p 0) (p 1)) a =
        HomotopyGroup.mapHomOfEq (mixedTraceEvalOne X) hX₁ n c :=
    (congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of X)
      (⟨p, rfl, rfl⟩ : _root_.Path (p 0) (p 1)))
        (mixedTracePathClassLift_evalZero n p a).symm).trans
          (originalUniversalPathTrace n p c)
  let E : ContinuousMap.Homotopy (mixedTraceEvalZero Y) (mixedTraceEvalOne Y) :=
    { toFun := fun z => z.2 z.1
      continuous_toFun := continuous_snd.eval continuous_fst
      map_zero_left := fun r => (mixedTraceEvalZero_apply Y r).symm
      map_one_left := fun r => (mixedTraceEvalOne_apply Y r).symm }
  have hTrace : (E.evalAt q).cast hY₀.symm hY₁.symm =
      ((⟨p, rfl, rfl⟩ : _root_.Path (p 0) (p 1)).map f.continuous) := by
    apply _root_.Path.ext
    funext t
    change q t = f (p t)
    exact originalPostcomposePathValueComputed f p t
  have hY := originalStrictEvaluationTrace n E hY₀ hY₁ _ hTrace b
  exact (congrArg (HomotopyGroup.map f) hX).trans
    (hMapOne.symm.trans (hY.symm.trans
      (congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y)
        ((⟨p, rfl, rfl⟩ : _root_.Path (p 0) (p 1)).map f.continuous)) hMapZero)))

end TopCat

end
