/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.IntervalMiddleUnitTriangle
public import MathlibExt.Topology.Homotopy.MappedRootUnitTransports

/-!
# Original generic middle unit triangle

The actual interval middle boundary is mapped through the same original
concatenation. Its actual half roots, unit contractions and joining-point
transports recover the original three-stage middle boundary.
-/

public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap

private def actualRootUnitPath {X : Type u} [TopologicalSpace X] {x y : X}
    (p : Path x y) : Path (loopBasepointChange p (Path.refl x)) (Path.refl y) :=
  ((rootUnitContraction (fun r : Path x y => r) continuous_eval).evalAt p).cast
    (rootUnitLoopFamily_pathSpace_apply p).symm rfl

private def actualMappedLoop {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X} {a : Y}
    (ha : a = f x) : C(LoopSpace X x, LoopSpace Y a) where
  toFun gamma := (gamma.map f.continuous).cast (x' := a) (y' := a) ha ha
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact f.continuous.comp
      (continuous_eval.comp (continuous_fst.prodMk continuous_snd))

private theorem actualConjugationCast {Y : Type u} [TopologicalSpace Y]
    {x y a b : Y} (p : Path x y) (gamma : LoopSpace Y x) (ha : a = x) (hb : b = y) :
    (loopBasepointChange p gamma).cast (x' := b) (y' := b) hb hb =
      loopBasepointChange (p.cast (x' := a) (y' := b) ha hb)
        (gamma.cast (x' := a) (y' := a) ha ha) := by
  cases ha
  cases hb
  rfl

private theorem actualMappedRefl {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X} {a : Y}
    (ha : a = f x) : actualMappedLoop f ha (Path.refl x) = Path.refl a := by
  apply Path.ext
  funext s
  exact ha.symm

private theorem actualMappedConjugation {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {x y : X} {a b : Y} (p : Path x y) (r : Path a b)
    (ha : a = f x) (hb : b = f y)
    (hr : (p.map f.continuous).cast (x' := a) (y' := b) ha hb = r)
    (gamma : LoopSpace X x) :
    actualMappedLoop f hb (loopBasepointChange p gamma) =
      loopBasepointChange r (actualMappedLoop f ha gamma) := by
  have h := congrArg (fun k : C(LoopSpace X x, LoopSpace Y (f y)) => k gamma)
    (loopBasepointChangeMap_naturality f p)
  have hCast := (congrArg (fun z : LoopSpace Y (f y) =>
      z.cast (x' := b) (y' := b) hb hb) h).trans
    (actualConjugationCast (p.map f.continuous) (gamma.map f.continuous) ha hb)
  exact hCast.trans (congrArg (fun p : Path a b =>
    loopBasepointChange p (actualMappedLoop f ha gamma)) hr)

private theorem actualMappedUnitValue {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {x y : X} {a b : Y} (p : Path x y) (r : Path a b)
    (ha : a = f x) (hb : b = f y)
    (hr : (p.map f.continuous).cast (x' := a) (y' := b) ha hb = r) (t : I) :
    actualMappedLoop f hb (actualRootUnitPath p t) = actualRootUnitPath r t :=
  (rootUnitContraction_mappedPath_cast f p ha hb t).trans
    (congrArg (fun r : Path a b =>
      rootUnitContraction (fun r : Path a b => r) continuous_eval (t, r)) hr)

private theorem actualMappedMiddleValue {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {x y z : X} {a b c : Y} (p : Path x y) (q : Path y z)
    (r : Path a b) (s : Path b c) (ha : a = f x) (hb : b = f y) (hc : c = f z)
    (hr : (p.map f.continuous).cast (x' := a) (y' := b) ha hb = r)
    (hs : (q.map f.continuous).cast (x' := b) (y' := c) hb hc = s) (t : I) :
    actualMappedLoop f hc (loopBasepointChangeTransHomotopy p q (t, Path.refl x)) =
      loopBasepointChangeTransHomotopy r s (t, Path.refl a) := by
  have h := loopBasepointChangeTransHomotopy_mappedRoots_cast f p q ha hb hc t (Path.refl x)
  let pMapped : Path a b := (p.map f.continuous).cast (x' := a) (y' := b) ha hb
  let qMapped : Path b c := (q.map f.continuous).cast (x' := b) (y' := c) hb hc
  let gamma : LoopSpace Y a := actualMappedLoop f ha (Path.refl x)
  have hFirst : loopBasepointChangeTransHomotopy pMapped qMapped (t, gamma) =
      loopBasepointChangeTransHomotopy r qMapped (t, gamma) :=
    congrArg (fun p₀ : Path a b => loopBasepointChangeTransHomotopy p₀ qMapped
      (t, gamma)) hr
  have hSecond : loopBasepointChangeTransHomotopy r qMapped (t, gamma) =
      loopBasepointChangeTransHomotopy r s (t, gamma) :=
    congrArg (fun q₀ : Path b c => loopBasepointChangeTransHomotopy r q₀
      (t, gamma)) hs
  exact h.trans (hFirst.trans (hSecond.trans (congrArg (fun gamma : LoopSpace Y a =>
    loopBasepointChangeTransHomotopy r s (t, gamma)) (actualMappedRefl f ha))))

private theorem actualMiddleUnitTriangleComputed {Y : Type u} [TopologicalSpace Y]
    {a b c : Y} (p : Path a b) (q : Path b c) :
    let Up := ((rootUnitContraction (fun r : Path a b => r) continuous_eval).evalAt p).cast
      (rootUnitLoopFamily_pathSpace_apply p).symm rfl
    let Uq := ((rootUnitContraction (fun r : Path b c => r) continuous_eval).evalAt q).cast
      (rootUnitLoopFamily_pathSpace_apply q).symm rfl
    let Uc := ((rootUnitContraction (fun r : Path a c => r)
      continuous_eval).evalAt (p.trans q)).cast
        (rootUnitLoopFamily_pathSpace_apply (p.trans q)).symm rfl
    (((loopBasepointChangeTransHomotopy p q).evalAt (Path.refl a)).trans
      ((Up.map (loopBasepointChange q).continuous).trans Uq)).Homotopic Uc := by
  let f : C(I, Y) := (p.trans q).toContinuousMap
  let ha : a = f 0 := (p.trans q).source.symm
  let hb : b = f pathHalfPoint := (Path.trans_pathHalfPoint p q).symm
  let hc : c = f 1 := (p.trans q).target.symm
  let Lc := actualMappedLoop f hc
  let Lb := actualMappedLoop f hb
  let T := (loopBasepointChangeTransHomotopy p q).evalAt (Path.refl a)
  let Ti := (loopBasepointChangeTransHomotopy pathHalfLeft pathHalfRight).evalAt
    (Path.refl (0 : I))
  let Up := actualRootUnitPath p
  let Uq := actualRootUnitPath q
  let Uc := actualRootUnitPath (p.trans q)
  let Upi := actualRootUnitPath pathHalfLeft
  let Uqi := actualRootUnitPath pathHalfRight
  let Uci := actualRootUnitPath (pathHalfLeft.trans pathHalfRight)
  have hp : (pathHalfLeft.map f.continuous).cast
      (x' := a) (y' := b) ha hb = p := Path.intervalHalfLeft_map_trans p q
  have hq : (pathHalfRight.map f.continuous).cast
      (x' := b) (y' := c) hb hc = q := Path.intervalHalfRight_map_trans p q
  have hcomp : ((pathHalfLeft.trans pathHalfRight).map f.continuous).cast
      (x' := a) (y' := c) ha hc = p.trans q := by
    apply Path.ext
    funext t
    exact congrArg (p.trans q) (congrArg (fun r : Path (0 : I) (1 : I) => r t)
      pathHalfLeft_trans_right)
  have hTvalue (t : I) : Lc (Ti t) = T t :=
    actualMappedMiddleValue f pathHalfLeft pathHalfRight p q ha hb hc hp hq t
  have hUpvalue (t : I) : Lb (Upi t) = Up t :=
    actualMappedUnitValue f pathHalfLeft p ha hb hp t
  have hUqvalue (t : I) : Lc (Uqi t) = Uq t :=
    actualMappedUnitValue f pathHalfRight q hb hc hq t
  have hUcvalue (t : I) : Lc (Uci t) = Uc t :=
    actualMappedUnitValue f (pathHalfLeft.trans pathHalfRight) (p.trans q) ha hc hcomp t
  have hSource : loopBasepointChange (p.trans q) (Path.refl a) =
      Lc (loopBasepointChange (pathHalfLeft.trans pathHalfRight) (Path.refl (0 : I))) :=
    ((congrArg Lc Uci.source).symm.trans ((hUcvalue 0).trans Uc.source)).symm
  have hMiddle : loopBasepointChange q (loopBasepointChange p (Path.refl a)) =
      Lc (loopBasepointChange pathHalfRight
        (loopBasepointChange pathHalfLeft (Path.refl (0 : I)))) :=
    ((congrArg Lc Ti.target).symm.trans ((hTvalue 1).trans T.target)).symm
  have hJoin : loopBasepointChange q (Path.refl b) =
      Lc (loopBasepointChange pathHalfRight (Path.refl pathHalfPoint)) :=
    ((actualMappedConjugation f pathHalfRight q hb hc hq (Path.refl pathHalfPoint)).trans
      (congrArg (loopBasepointChange q) (actualMappedRefl f hb))).symm
  have hTarget : Path.refl c = Lc (Path.refl (1 : I)) := (actualMappedRefl f hc).symm
  have hMappedT : (Ti.map Lc.continuous).cast
      (x' := loopBasepointChange (p.trans q) (Path.refl a))
      (y' := loopBasepointChange q (loopBasepointChange p (Path.refl a)))
      hSource hMiddle = T := by
    apply Path.ext
    funext t
    exact hTvalue t
  have hMappedUp : ((Upi.map (loopBasepointChange pathHalfRight).continuous).map
      Lc.continuous).cast
        (x' := loopBasepointChange q (loopBasepointChange p (Path.refl a)))
        (y' := loopBasepointChange q (Path.refl b)) hMiddle hJoin =
      Up.map (loopBasepointChange q).continuous := by
    apply Path.ext
    funext t
    exact (actualMappedConjugation f pathHalfRight q hb hc hq (Upi t)).trans
      (congrArg (loopBasepointChange q) (hUpvalue t))
  have hMappedUq : (Uqi.map Lc.continuous).cast
      (x' := loopBasepointChange q (Path.refl b)) (y' := Path.refl c)
      hJoin hTarget = Uq := by
    apply Path.ext
    funext t
    exact hUqvalue t
  have hMappedUc : (Uci.map Lc.continuous).cast
      (x' := loopBasepointChange (p.trans q) (Path.refl a)) (y' := Path.refl c)
      hSource hTarget = Uc := by
    apply Path.ext
    funext t
    exact hUcvalue t
  have hPieces : intervalMiddleUnitBoundary =
      Ti.trans ((Upi.map (loopBasepointChange pathHalfRight).continuous).trans Uqi) :=
    intervalMiddleUnitBoundary_eq_actualPieces
  have hContract : intervalMiddleUnitContraction = Uci :=
    intervalMiddleUnitContraction_eq_actualRoot
  have hMappedBoundary : (intervalMiddleUnitBoundary.map Lc.continuous).cast
      (x' := loopBasepointChange (p.trans q) (Path.refl a)) (y' := Path.refl c)
      hSource hTarget = T.trans ((Up.map (loopBasepointChange q).continuous).trans Uq) := by
    rw [hPieces, Path.map_trans, Path.map_trans]
    rw [Path.cast_trans _ _ hSource hMiddle hTarget]
    rw [Path.cast_trans _ _ hMiddle hJoin hTarget]
    rw [hMappedT, hMappedUp, hMappedUq]
  have hMappedContract : (intervalMiddleUnitContraction.map Lc.continuous).cast
      (x' := loopBasepointChange (p.trans q) (Path.refl a)) (y' := Path.refl c)
      hSource hTarget = Uc :=
    (congrArg (fun P : Path
      (loopBasepointChange (pathHalfLeft.trans pathHalfRight) (Path.refl (0 : I)))
      (Path.refl (1 : I)) => (P.map Lc.continuous).cast hSource hTarget) hContract).trans
        hMappedUc
  let K := (intervalMiddleUnitTriangleHomotopy.map Lc).pathCast hSource hTarget
  exact ⟨K.cast hMappedBoundary hMappedContract⟩

/-- The actual original middle unit boundary compares with the same
composite-root contraction after mapping the concrete interval triangle. -/
theorem loopBasepointChangeTransHomotopy_unitTriangle_homotopic
    {Y : Type u} [TopologicalSpace Y] {a b c : Y} (p : Path a b) (q : Path b c) :
    let Up := ((rootUnitContraction (fun r : Path a b => r) continuous_eval).evalAt p).cast
      (rootUnitLoopFamily_pathSpace_apply p).symm rfl
    let Uq := ((rootUnitContraction (fun r : Path b c => r) continuous_eval).evalAt q).cast
      (rootUnitLoopFamily_pathSpace_apply q).symm rfl
    let Uc := ((rootUnitContraction (fun r : Path a c => r)
      continuous_eval).evalAt (p.trans q)).cast
        (rootUnitLoopFamily_pathSpace_apply (p.trans q)).symm rfl
    (((loopBasepointChangeTransHomotopy p q).evalAt (Path.refl a)).trans
      ((Up.map (loopBasepointChange q).continuous).trans Uq)).Homotopic Uc :=
  actualMiddleUnitTriangleComputed p q

end ContinuousMap

end
