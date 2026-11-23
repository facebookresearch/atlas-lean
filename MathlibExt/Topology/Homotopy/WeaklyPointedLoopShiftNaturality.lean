/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.HomotopyGroupLoopShift
public import MathlibExt.Topology.Homotopy.PointTraceUnitContraction
public import MathlibExt.Topology.Homotopy.RootUnitTraceComparison
public import MathlibExt.Topology.Homotopy.RootUnitContractionMap
public import MathlibExt.Topology.Homotopy.WeaklyPointedPositiveHomotopyGroupMap
public import MathlibExt.Topology.Homotopy.OriginalLoopOwnUnitCalibration
public import MathlibExt.Topology.Homotopy.OriginalRootUnitPathCoherence

/-!
# Loop-shift naturality with the original chosen root

For arbitrary independently sized spaces, the canonical positive loop shift
commutes with the actual weakly pointed map and its whole original root.
The source loop map uses the existing positive homotopy-group API and the
existing own-unit path. Its exact joint contraction recipe is the proved
canonical equality. Both original unit choices are preserved.
-/

public section
noncomputable section

open CategoryTheory Topology
open scoped ContinuousMap unitInterval Topology.Homotopy

universe uX uY

namespace HomotopyGroup

private def pathSpaceEval (Y : Type uY) [TopologicalSpace Y]
    (t : unitInterval) : C(C(unitInterval, Y), Y) where
  toFun p := p t
  continuous_toFun := continuous_eval.comp (continuous_id.prodMk continuous_const)

private def pathSpaceConst (Y : Type uY) [TopologicalSpace Y] :
    C(Y, C(unitInterval, Y)) where
  toFun y := ContinuousMap.const unitInterval y
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_fst

private def pathSpaceEvalHomotopy (Y : Type uY) [TopologicalSpace Y] :
    ContinuousMap.Homotopy (pathSpaceEval Y 0) (pathSpaceEval Y 1) where
  toFun z := z.2 z.1
  continuous_toFun := continuous_eval.comp (continuous_snd.prodMk continuous_fst)
  map_zero_left _ := rfl
  map_one_left _ := rfl

private def pathSpaceConstToPoint {Y : Type uY} [TopologicalSpace Y]
    (p : C(unitInterval, Y)) : Path (pathSpaceConst Y (p 0)) p where
  toFun t :=
    { toFun s := p (Set.Icc.convexComb (0 : unitInterval) s t)
      continuous_toFun := p.continuous.comp
        (Set.Icc.continuous_convexComb_prod.comp
          (continuous_const.prodMk (continuous_id.prodMk continuous_const))) }
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact p.continuous.comp (Set.Icc.continuous_convexComb_prod.comp
      (continuous_const.prodMk (continuous_snd.prodMk continuous_fst)))
  source' := by
    apply ContinuousMap.ext
    intro s
    change p (Set.Icc.convexComb (0 : unitInterval) s 0) = p 0
    rw [Set.Icc.convexComb_zero]
  target' := by
    apply ContinuousMap.ext
    intro s
    change p (Set.Icc.convexComb (0 : unitInterval) s 1) = p s
    rw [Set.Icc.convexComb_one]

private theorem pathSpaceConstToPoint_evalZero
    {Y : Type uY} [TopologicalSpace Y] (p : C(unitInterval, Y)) :
    (pathSpaceConstToPoint p).map (pathSpaceEval Y 0).continuous = Path.refl (p 0) := by
  apply Path.ext
  funext t
  change p (Set.Icc.convexComb (0 : unitInterval) 0 t) = p 0
  rw [Set.Icc.convexComb_eq]

private theorem pathSpaceEvalZero_comp_const (Y : Type uY) [TopologicalSpace Y] :
    (pathSpaceEval Y 0).comp (pathSpaceConst Y) = ContinuousMap.id Y := by
  apply ContinuousMap.ext
  intro y
  rfl

private theorem pathSpaceEvalZero_loopPi_surjective
    {Y : Type uY} [TopologicalSpace Y] (n : ℕ) (p : C(unitInterval, Y)) :
    Function.Surjective (HomotopyGroup.mapHomOfEq
      (ContinuousMap.strictLoopMap (pathSpaceEval Y 0) p)
      (ContinuousMap.strictLoopMap_refl (pathSpaceEval Y 0) p) n) := by
  intro a
  let A := C(unitInterval, Y)
  let e0 : C(A, Y) :=
    ⟨fun r => r 0, continuous_eval.comp (continuous_id.prodMk continuous_const)⟩
  let cst : C(Y, A) :=
    ⟨fun y => ContinuousMap.const unitInterval y,
      ContinuousMap.continuous_of_continuous_uncurry _ continuous_fst⟩
  let q : Path (cst (p 0)) p := (pathSpaceConstToPoint p).cast rfl rfl
  let target := HomotopyGroup.loopShiftMulEquiv n Y (p 0) a
  let seed := HomotopyGroup.map cst target
  let lifted := TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of A) q seed
  let b := (HomotopyGroup.loopShiftMulEquiv n A p).symm lifted
  have hPath : q.map e0.continuous = Path.refl (p 0) :=
    pathSpaceConstToPoint_evalZero p
  have hEval : HomotopyGroup.map e0 lifted = target := by
    have h := TopCat.homotopyGroupBasepointChangeMulEquiv_naturality
      (n + 1) (TopCat.ofHom e0) q seed
    change HomotopyGroup.map e0 lifted =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y)
        (q.map e0.continuous) (HomotopyGroup.map e0 seed) at h
    have hAction : TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y)
        (q.map e0.continuous) (HomotopyGroup.map e0 seed) =
      HomotopyGroup.map e0 seed :=
      (congrArg (fun r : Path (p 0) (p 0) =>
        TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) r
          (HomotopyGroup.map (x := cst (p 0)) e0 seed)) hPath).trans
      (congrArg (fun e => e (HomotopyGroup.map (x := cst (p 0)) e0 seed))
        (TopCat.homotopyGroupBasepointChangeMulEquiv_refl (n + 1) (TopCat.of Y) (p 0)))
    have hSeed : HomotopyGroup.map e0 seed = target := by
      change HomotopyGroup.map e0 (HomotopyGroup.map cst target) = target
      exact (HomotopyGroup.map_comp cst e0 target).symm.trans
        (HomotopyGroup.map_id target)
    exact h.trans (hAction.trans hSeed)
  refine ⟨b, ?_⟩
  apply (HomotopyGroup.loopShiftMulEquiv n Y (p 0)).injective
  have h := HomotopyGroup.loopShiftMulEquiv_naturality n e0 p b
  exact h.trans ((congrArg (HomotopyGroup.map e0)
    ((HomotopyGroup.loopShiftMulEquiv n A p).apply_symm_apply lifted)).trans hEval)

/-- The original whole root-unit contraction for loop basepoint conjugation. -/
private def conjugationUnitPath {Y : Type uY} [TopologicalSpace Y]
    {a b : Y} (p : Path a b) :
    Path (ContinuousMap.loopBasepointChange p (Path.refl a)) (Path.refl b) :=
  ((ContinuousMap.rootUnitContraction (fun r : Path a b => r)
    continuous_eval).evalAt p).cast
      (ContinuousMap.rootUnitLoopFamily_pathSpace_apply p).symm rfl

/-- Positive loop classes follow the actual conjugation and its original unit contraction. -/
private abbrev conjugationLoopPiMap {Y : Type uY} [TopologicalSpace Y]
    (n : ℕ) {a b : Y} (p : Path a b) :
    HomotopyGroup.Pi (n + 1) (LoopSpace Y a) (Path.refl a) →*
      HomotopyGroup.Pi (n + 1) (LoopSpace Y b) (Path.refl b) :=
  ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
    (⟨ContinuousMap.loopBasepointChange p, conjugationUnitPath p⟩ :
      ContinuousMap.WeaklyPointed (Path.refl a) (Path.refl b))

private theorem conjugationLoopShift_eval
    {Y : Type uY} [TopologicalSpace Y] (n : ℕ) (p : C(unitInterval, Y))
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace Y (p 0)) (Path.refl (p 0))) :
    let q := (pathSpaceEvalHomotopy Y).evalAt p
    HomotopyGroup.loopShiftMulEquiv n Y (p 1) (conjugationLoopPiMap n q a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) q
        (HomotopyGroup.loopShiftMulEquiv n Y (p 0) a) := by
  let A := C(unitInterval, Y)
  let e0 : C(A, Y) :=
    ⟨fun r => r 0, continuous_eval.comp (continuous_id.prodMk continuous_const)⟩
  let e1 : C(A, Y) :=
    ⟨fun r => r 1, continuous_eval.comp (continuous_id.prodMk continuous_const)⟩
  let H : ContinuousMap.Homotopy e0 e1 :=
    { toFun z := z.2 z.1
      continuous_toFun := continuous_eval.comp (continuous_snd.prodMk continuous_fst)
      map_zero_left _ := rfl
      map_one_left _ := rfl }
  let q := H.evalAt p
  let s0 := ContinuousMap.strictLoopMap e0 p
  let s1 := ContinuousMap.strictLoopMap e1 p
  let B := ContinuousMap.loopBasepointChange q
  let L := ContinuousMap.Homotopy.traceConjugationLoopHomotopy H p
  have h0 : s0 (Path.refl p) = Path.refl (p 0) :=
    ContinuousMap.strictLoopMap_refl e0 p
  have h1 : s1 (Path.refl p) = Path.refl (p 1) :=
    ContinuousMap.strictLoopMap_refl e1 p
  have hStart : (B.comp s0) (Path.refl p) = B (Path.refl (p 0)) := congrArg B h0
  obtain ⟨b, hbOld⟩ := pathSpaceEvalZero_loopPi_surjective n p a
  have hb : HomotopyGroup.mapHomOfEq s0 h0 n b = a := hbOld
  have hTrace :
      ((L.evalAt (Path.refl p)).cast hStart.symm h1.symm).Homotopic
        (conjugationUnitPath q) :=
    ContinuousMap.Homotopy.traceConjugationLoopHomotopy_unitTrace_homotopic H p
  have hGroup := TopCat.homotopyGroup_map_homotopy_trace_of_eq
    (X := TopCat.of (LoopSpace A p)) (Y := TopCat.of (LoopSpace Y (p 1))) n
    (f := TopCat.ofHom (B.comp s0)) (g := TopCat.ofHom s1) L (Path.refl p)
    hStart h1 b
  change TopCat.homotopyGroupBasepointChangeMulEquiv n
    (TopCat.of (LoopSpace Y (p 1))) ((L.evalAt (Path.refl p)).cast hStart.symm h1.symm)
      (HomotopyGroup.mapHomOfEq (B.comp s0) hStart n b) =
        HomotopyGroup.mapHomOfEq s1 h1 n b at hGroup
  have hTransport := TopCat.homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic n
    (TopCat.of (LoopSpace Y (p 1))) hTrace
  have hGroupCorrected : TopCat.homotopyGroupBasepointChangeMulEquiv n
      (TopCat.of (LoopSpace Y (p 1))) (conjugationUnitPath q)
        (HomotopyGroup.mapHomOfEq (B.comp s0) hStart n b) =
      HomotopyGroup.mapHomOfEq s1 h1 n b :=
    (congrArg (fun e => e (HomotopyGroup.mapHomOfEq (B.comp s0) hStart n b))
      hTransport).symm.trans hGroup
  have hMap : HomotopyGroup.mapHomOfEq (B.comp s0) hStart n b =
      HomotopyGroup.map B a := by
    have h := HomotopyGroup.mapHomOfEq_comp s0 B h0 rfl hStart n b
    have hBare : HomotopyGroup.mapHomOfEq B rfl n
        (HomotopyGroup.mapHomOfEq s0 h0 n b) =
      HomotopyGroup.map B (HomotopyGroup.mapHomOfEq s0 h0 n b) :=
      HomotopyGroup.mapHomOfEq_apply B rfl n (HomotopyGroup.mapHomOfEq s0 h0 n b)
    exact h.trans (hBare.trans
      (congrArg (HomotopyGroup.map (x := Path.refl (p 0)) B) hb))
  have hConjugation : conjugationLoopPiMap n q a =
      HomotopyGroup.mapHomOfEq s1 h1 n b := by
    rw [conjugationLoopPiMap, ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap_apply]
    change TopCat.homotopyGroupBasepointChangeMulEquiv n
      (TopCat.of (LoopSpace Y (p 1))) (conjugationUnitPath q)
        (HomotopyGroup.map B a) = _
    exact (congrArg
      (TopCat.homotopyGroupBasepointChangeMulEquiv n
        (TopCat.of (LoopSpace Y (p 1))) (conjugationUnitPath q)) hMap).symm.trans
          hGroupCorrected
  have hBQ := TopCat.homotopyGroup_map_homotopy_trace
    (X := TopCat.of A) (Y := TopCat.of Y) (n + 1)
    (f := TopCat.ofHom e0) (g := TopCat.ofHom e1) H p
    (HomotopyGroup.loopShiftMulEquiv n A p b)
  change HomotopyGroup.loopShiftMulEquiv n Y (p 1) (conjugationLoopPiMap n q a) = _
  calc
    _ = HomotopyGroup.loopShiftMulEquiv n Y (p 1)
        (HomotopyGroup.mapHomOfEq s1 h1 n b) :=
      congrArg (HomotopyGroup.loopShiftMulEquiv n Y (p 1)) hConjugation
    _ = HomotopyGroup.map e1
        (HomotopyGroup.loopShiftMulEquiv n A p b) :=
      HomotopyGroup.loopShiftMulEquiv_naturality n e1 p b
    _ = TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) q
        (HomotopyGroup.map e0
          (HomotopyGroup.loopShiftMulEquiv n A p b)) := hBQ.symm
    _ = TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) q
        (HomotopyGroup.loopShiftMulEquiv n Y (p 0)
          (HomotopyGroup.mapHomOfEq s0 h0 n b)) :=
      congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) q)
        (HomotopyGroup.loopShiftMulEquiv_naturality n e0 p b).symm
    _ = _ := congrArg
      (fun x => TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) q
        (HomotopyGroup.loopShiftMulEquiv n Y (p 0) x)) hb

private theorem conjugationLoopShift
    {Y : Type uY} [TopologicalSpace Y] (n : ℕ) {a b : Y} (p : Path a b)
    (x : HomotopyGroup.Pi (n + 1) (LoopSpace Y a) (Path.refl a)) :
    HomotopyGroup.loopShiftMulEquiv n Y b (conjugationLoopPiMap n p x) =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) p
        (HomotopyGroup.loopShiftMulEquiv n Y a x) := by
  rcases p with ⟨p, hs, ht⟩
  subst a
  subst b
  exact conjugationLoopShift_eval n p x

/-- The canonical positive loop shift retains the actual root conjugation and unit correction. -/
private theorem loopShiftMulEquiv_conjugation_naturality
    {Y : Type uY} [TopologicalSpace Y] (n : ℕ) {a b : Y} (p : Path a b)
    (x : HomotopyGroup.Pi (n + 1) (LoopSpace Y a) (Path.refl a)) :
    HomotopyGroup.loopShiftMulEquiv n Y b (conjugationLoopPiMap n p x) =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) p
        (HomotopyGroup.loopShiftMulEquiv n Y a x) :=
  conjugationLoopShift n p x

private theorem mapHomOfEq_congr
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (h : f = g) (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.mapHomOfEq f hf n a = HomotopyGroup.mapHomOfEq g hg n a := by
  cases h
  rfl

private theorem basepointChange_sourceCast
    {Y : Type uY} [TopologicalSpace Y] (n : ℕ) {a a' b : Y}
    (p : Path a b) (h : a' = a) (x : HomotopyGroup.Pi (n + 1) Y a') :
    TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) (p.cast h rfl) x =
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of Y) p (h ▸ x) := by
  cases h
  rfl

private abbrev rootedLoopPiMap
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f : ContinuousMap.WeaklyPointed x y) :
    HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x) →*
      HomotopyGroup.Pi (n + 1) (LoopSpace Y y) (Path.refl y) :=
  ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
    (⟨f.loopMap, ContinuousMap.WeaklyPointed.loopUnitRootPath f⟩ :
      ContinuousMap.WeaklyPointed (Path.refl x) (Path.refl y))

private theorem rootedLoopPiMap_factor
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f : ContinuousMap.WeaklyPointed x y)
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    rootedLoopPiMap n f a = conjugationLoopPiMap n f.rootPath
      (HomotopyGroup.mapHomOfEq (ContinuousMap.strictLoopMap f.hom x)
        (ContinuousMap.strictLoopMap_refl f.hom x) n a) := by
  let S := ContinuousMap.strictLoopMap f.hom x
  let B := ContinuousMap.loopBasepointChange f.rootPath
  have hF : f.loopMap = B.comp S :=
    ContinuousMap.WeaklyPointed.loopMap_eq_loopBasepointChange_comp_strictLoopMap f
  have hS : S (Path.refl x) = Path.refl (f.hom x) :=
    ContinuousMap.strictLoopMap_refl f.hom x
  have hBS : (B.comp S) (Path.refl x) = B (Path.refl (f.hom x)) := congrArg B hS
  have hStart : f.loopMap (Path.refl x) = B (Path.refl (f.hom x)) :=
    (DFunLike.congr_fun hF (Path.refl x)).trans hBS
  have hUnit : ContinuousMap.WeaklyPointed.loopUnitRootPath f =
      (conjugationUnitPath f.rootPath).cast hStart rfl := by
    rw [ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201]
    apply Path.ext
    funext t
    rfl
  have hMap : hStart ▸ HomotopyGroup.map f.loopMap a =
      HomotopyGroup.map B (HomotopyGroup.mapHomOfEq S hS n a) := by
    have hFmap := mapHomOfEq_congr f.loopMap (B.comp S) hStart hBS hF n a
    have hComp := HomotopyGroup.mapHomOfEq_comp S B hS rfl hBS n a
    have hBare := HomotopyGroup.mapHomOfEq_apply B rfl n
      (HomotopyGroup.mapHomOfEq S hS n a)
    exact (HomotopyGroup.mapHomOfEq_apply f.loopMap hStart n a).symm.trans
      (hFmap.trans (hComp.trans hBare))
  simp only [rootedLoopPiMap, conjugationLoopPiMap,
    ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap_apply]
  change TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (LoopSpace Y y))
    (ContinuousMap.WeaklyPointed.loopUnitRootPath f) (HomotopyGroup.map f.loopMap a) = _
  exact (congrArg (fun p =>
      TopCat.homotopyGroupBasepointChangeMulEquiv n (TopCat.of (LoopSpace Y y)) p
        (HomotopyGroup.map f.loopMap a)) hUnit).trans
    ((basepointChange_sourceCast n (conjugationUnitPath f.rootPath) hStart
      (HomotopyGroup.map f.loopMap a)).trans
      (congrArg (TopCat.homotopyGroupBasepointChangeMulEquiv n
        (TopCat.of (LoopSpace Y y)) (conjugationUnitPath f.rootPath)) hMap))

private theorem rootedLoopShiftComputed
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f : ContinuousMap.WeaklyPointed x y)
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    HomotopyGroup.loopShiftMulEquiv n Y y (rootedLoopPiMap n f a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) f.rootPath
        (HomotopyGroup.map f.hom (HomotopyGroup.loopShiftMulEquiv n X x a)) := by
  have hFactor := rootedLoopPiMap_factor n f a
  have hConjugation := loopShiftMulEquiv_conjugation_naturality n f.rootPath
    (HomotopyGroup.mapHomOfEq (ContinuousMap.strictLoopMap f.hom x)
      (ContinuousMap.strictLoopMap_refl f.hom x) n a)
  have hStrict := HomotopyGroup.loopShiftMulEquiv_naturality n f.hom x a
  exact (congrArg (HomotopyGroup.loopShiftMulEquiv n Y y) hFactor).trans
    (hConjugation.trans (congrArg
      (TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) f.rootPath) hStrict))

/-- The canonical shift commutes with the actual map and its entire chosen root. -/
theorem loopShiftMulEquiv_rooted_naturality
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f : ContinuousMap.WeaklyPointed x y)
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    HomotopyGroup.loopShiftMulEquiv n Y y
        (ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
          (⟨f.loopMap, ContinuousMap.WeaklyPointed.loopUnitRootPath f⟩ :
            ContinuousMap.WeaklyPointed (Path.refl x) (Path.refl y)) a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) f.rootPath
        (HomotopyGroup.map f.hom (HomotopyGroup.loopShiftMulEquiv n X x a)) :=
  rootedLoopShiftComputed n f a

/-- The existing positive-loop group map satisfies the same chosen-root
shift square. Its original unit path is compared with the original own-unit
path by the canonical endpoint-fixed homotopy; no root is replaced. -/
theorem loopShiftMulEquiv_positiveLoop_naturality
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f : ContinuousMap.WeaklyPointed x y)
    (a : HomotopyGroup.Pi (n + 1) (LoopSpace X x) (Path.refl x)) :
    HomotopyGroup.loopShiftMulEquiv n Y y
        (ContinuousMap.WeaklyPointed.positiveLoopHomotopyGroupMap n f a) =
      TopCat.homotopyGroupBasepointChangeMulEquiv (n + 1) (TopCat.of Y) f.rootPath
        (HomotopyGroup.map f.hom (HomotopyGroup.loopShiftMulEquiv n X x a)) := by
  have hUnit : (ContinuousMap.WeaklyPointed.loopMapUnitPath f).Homotopic
      (ContinuousMap.WeaklyPointed.loopUnitRootPath f) := by
    rw [ContinuousMap.WeaklyPointed.originalLoopOwnUnit_eq201]
    exact ContinuousMap.WeaklyPointed.loopMapUnitPath_homotopic_rootUnit f
  have hMap : ContinuousMap.WeaklyPointed.positiveLoopHomotopyGroupMap n f a =
      ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap n
        (⟨f.loopMap, ContinuousMap.WeaklyPointed.loopUnitRootPath f⟩ :
          ContinuousMap.WeaklyPointed (Path.refl x) (Path.refl y)) a := by
    rw [ContinuousMap.WeaklyPointed.positiveLoopHomotopyGroupMap_apply,
      ContinuousMap.WeaklyPointed.positiveHomotopyGroupMap_apply]
    exact congrArg (fun e => e (HomotopyGroup.map f.loopMap a))
      (TopCat.homotopyGroupBasepointChangeMulEquiv_eq_of_homotopic n
        (TopCat.of (LoopSpace Y y)) hUnit)
  exact (congrArg (HomotopyGroup.loopShiftMulEquiv n Y y) hMap).trans
    (loopShiftMulEquiv_rooted_naturality n f a)

end HomotopyGroup

end
