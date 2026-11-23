/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.WeaklyPointedLoopHomotopies

/-!
# Loop-space equivalences with actual point paths

An ordinary homotopy gives a joint loop family by mapping each loop through
the homotopy and conjugating with the remaining segment of its point trace.
The variable endpoints are handled by the existing continuous-family laws
for paths. This yields a homotopy of the complete continuous loop maps.

An unbased homotopy equivalence then induces a loop-space homotopy equivalence
for any specified source point and path to the target point. A conjugation
correction supplies both inverse families without requiring triangle data,
CW models, or additional structure on either raw loop space.
-/

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap

namespace Homotopy

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}

private def traceTail (H : Homotopy f g) (x : X) (t : I) :
    Path (H (t, x)) (g x) where
  toFun s := H (Set.Icc.convexComb t 1 s, x)
  continuous_toFun := H.continuous.comp
    ((Set.Icc.continuous_convexComb_prod.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))).prodMk continuous_const)
  source' := by rw [Set.Icc.convexComb_zero]
  target' := by
    rw [Set.Icc.convexComb_one]
    exact H.apply_one x

private def mappedAt (H : Homotopy f g) (x : X)
    (gamma : LoopSpace X x) (t : I) : Path (H (t, x)) (H (t, x)) where
  toFun s := H (t, gamma s)
  continuous_toFun := H.continuous.comp (continuous_const.prodMk gamma.continuous)
  source' := congrArg (fun z => H (t, z)) gamma.source
  target' := congrArg (fun z => H (t, z)) gamma.target

private theorem traceTail_zero (H : Homotopy f g) (x : X) :
    (traceTail H x 0).cast (H.apply_zero x).symm rfl = H.evalAt x := by
  apply Path.ext
  funext s
  change H (Set.Icc.convexComb 0 1 s, x) = H (s, x)
  rw [Set.Icc.convexComb_zero_one]

private theorem traceTail_one (H : Homotopy f g) (x : X) :
    (traceTail H x 1).cast (H.apply_one x).symm rfl = Path.refl (g x) := by
  apply Path.ext
  funext s
  change H (Set.Icc.convexComb 1 1 s, x) = g x
  rw [Set.Icc.convexComb_eq]
  exact H.apply_one x

/-- The actual remaining point trace used in the original loop family,
with its original moving source and fixed target. -/
public def pointTraceTail (H : Homotopy f g) (x : X) (t : I) :
    Path (H (t, x)) (g x) := traceTail H x t

private theorem originalPointTraceTailValueComputed
    (H : Homotopy f g) (x : X) (t s : I) :
    pointTraceTail H x t s = H (Set.Icc.convexComb t 1 s, x) := rfl

/-- Both original point-trace times have the actual original affine
tail coordinate, on the same entire ordinary homotopy. -/
public theorem pointTraceTail_apply (H : Homotopy f g) (x : X) (t s : I) :
    pointTraceTail H x t s = H (Set.Icc.convexComb t 1 s, x) :=
  originalPointTraceTailValueComputed H x t s

private theorem originalPointTraceTailZeroComputed (H : Homotopy f g) (x : X) :
    (pointTraceTail H x 0).cast (H.apply_zero x).symm rfl = H.evalAt x :=
  traceTail_zero H x

private theorem originalPointTraceTailOneComputed (H : Homotopy f g) (x : X) :
    (pointTraceTail H x 1).cast (H.apply_one x).symm rfl = Path.refl (g x) :=
  traceTail_one H x

/-- The whole original zero-time tail is the same original full point
trace, with its actual source endpoint cast. -/
public theorem pointTraceTail_zero (H : Homotopy f g) (x : X) :
    (pointTraceTail H x 0).cast (H.apply_zero x).symm rfl = H.evalAt x :=
  originalPointTraceTailZeroComputed H x

/-- The whole original final tail is the literal original reflexive
path, with its derived actual source endpoint cast. -/
public theorem pointTraceTail_one (H : Homotopy f g) (x : X) :
    (pointTraceTail H x 1).cast (H.apply_one x).symm rfl = Path.refl (g x) :=
  originalPointTraceTailOneComputed H x

private theorem originalPointTraceTailContinuousComputed (H : Homotopy f g) (x : X) :
    Continuous (fun z : I × I => pointTraceTail H x z.1 z.2) := by
  have hTime : Continuous (fun z : I × I => Set.Icc.convexComb z.1 1 z.2) :=
    Set.Icc.continuous_convexComb_prod.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  have h : Continuous (fun z : I × I => H (Set.Icc.convexComb z.1 1 z.2, x)) :=
    H.continuous.comp (hTime.prodMk continuous_const)
  exact h.congr (fun z => (pointTraceTail_apply H x z.1 z.2).symm)

/-- The actual whole remaining-root family is jointly continuous in
both original times, even though its source point moves. -/
public theorem pointTraceTail_continuous (H : Homotopy f g) (x : X) :
    Continuous (fun z : I × I => pointTraceTail H x z.1 z.2) :=
  originalPointTraceTailContinuousComputed H x

private theorem mappedAt_zero (H : Homotopy f g) (x : X) (gamma : LoopSpace X x) :
    (mappedAt H x gamma 0).cast (H.apply_zero x).symm (H.apply_zero x).symm =
      gamma.map f.continuous := by
  apply Path.ext
  funext s
  exact H.apply_zero (gamma s)

private theorem mappedAt_one (H : Homotopy f g) (x : X) (gamma : LoopSpace X x) :
    (mappedAt H x gamma 1).cast (H.apply_one x).symm (H.apply_one x).symm =
      gamma.map g.continuous := by
  apply Path.ext
  funext s
  exact H.apply_one (gamma s)

private def traceLoopFamilyAux (H : Homotopy f g) (x : X) :
    C(I × LoopSpace X x, LoopSpace Y (g x)) where
  toFun s := (traceTail H x s.1).symm.trans
    ((mappedAt H x s.2 s.1).trans (traceTail H x s.1))
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    let A := I × LoopSpace X x
    let T : ∀ s : A, Path (H (s.1, x)) (g x) := fun s => traceTail H x s.1
    let M : ∀ s : A, Path (H (s.1, x)) (H (s.1, x)) :=
      fun s => mappedAt H x s.2 s.1
    have hParameter : Continuous (fun s : A × I => Set.Icc.convexComb s.1.1 1 s.2) :=
      Set.Icc.continuous_convexComb_prod.comp
        ((continuous_fst.comp continuous_fst).prodMk
          (continuous_const.prodMk continuous_snd))
    have hT : Continuous ↿T := H.continuous.comp (hParameter.prodMk continuous_const)
    have hM : Continuous ↿M := H.continuous.comp
      ((continuous_fst.comp continuous_fst).prodMk
        (continuous_eval.comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
    have hTSymm := Path.symm_continuous_family T hT
    have hMT := Path.trans_continuous_family M hM T hT
    exact Path.trans_continuous_family (fun s => (T s).symm) hTSymm
      (fun s => (M s).trans (T s)) hMT

/-- The actual joint loop family of an ordinary homotopy, conjugated by
the remaining point trace so that its target basepoint is fixed. -/
public def traceLoopFamily (H : Homotopy f g) (x : X) :
    C(I × LoopSpace X x, LoopSpace Y (g x)) := traceLoopFamilyAux H x

private theorem originalTraceLoopFamilyReflTailComputed
    (H : Homotopy f g) (x : X) (t : I) :
    traceLoopFamily H x (t, Path.refl x) =
      (pointTraceTail H x t).symm.trans
        ((Path.refl (H (t, x))).trans (pointTraceTail H x t)) := by
  have hMapped : mappedAt H x (Path.refl x) t = Path.refl (H (t, x)) := by
    apply Path.ext
    funext s
    rfl
  change (traceTail H x t).symm.trans
      ((mappedAt H x (Path.refl x) t).trans (traceTail H x t)) =
    (traceTail H x t).symm.trans ((Path.refl (H (t, x))).trans (traceTail H x t))
  exact congrArg (fun gamma : Path (H (t, x)) (H (t, x)) =>
    (traceTail H x t).symm.trans (gamma.trans (traceTail H x t))) hMapped

/-- The whole actual unit-loop trace is the original three-piece unit
loop of the same actual moving-source point tail. -/
public theorem traceLoopFamily_refl_eq_pointTraceTail
    (H : Homotopy f g) (x : X) (t : I) :
    traceLoopFamily H x (t, Path.refl x) =
      (pointTraceTail H x t).symm.trans
        ((Path.refl (H (t, x))).trans (pointTraceTail H x t)) :=
  originalTraceLoopFamilyReflTailComputed H x t

private theorem conjugation_cast {a a' b : Y} (p : Path a b)
    (q : Path a a) (h : a' = a) :
    (p.cast h rfl).symm.trans ((q.cast h h).trans (p.cast h rfl)) =
      p.symm.trans (q.trans p) := by
  cases h
  rfl

private theorem traceLoopFamily_zero_computed (H : Homotopy f g) (x : X)
    (gamma : LoopSpace X x) :
    traceLoopFamily H x (0, gamma) =
      loopBasepointChange (H.evalAt x) (strictLoopMap f x gamma) := by
  change (traceTail H x 0).symm.trans
    ((mappedAt H x gamma 0).trans (traceTail H x 0)) = _
  rw [← conjugation_cast (traceTail H x 0) (mappedAt H x gamma 0)
    (H.apply_zero x).symm]
  rw [traceTail_zero, mappedAt_zero, loopBasepointChange_apply, strictLoopMap_apply]

/-- At the first endpoint the family is the original mapped loop
conjugated along the full point trace. -/
public theorem traceLoopFamily_zero (H : Homotopy f g) (x : X)
    (gamma : LoopSpace X x) :
    traceLoopFamily H x (0, gamma) =
      loopBasepointChange (H.evalAt x) (strictLoopMap f x gamma) :=
  traceLoopFamily_zero_computed H x gamma

private theorem traceLoopFamily_one_computed (H : Homotopy f g) (x : X)
    (gamma : LoopSpace X x) :
    traceLoopFamily H x (1, gamma) =
      loopBasepointChange (Path.refl (g x)) (strictLoopMap g x gamma) := by
  change (traceTail H x 1).symm.trans
    ((mappedAt H x gamma 1).trans (traceTail H x 1)) = _
  rw [← conjugation_cast (traceTail H x 1) (mappedAt H x gamma 1)
    (H.apply_one x).symm]
  rw [traceTail_one, mappedAt_one, loopBasepointChange_apply, strictLoopMap_apply]

/-- At the second endpoint only reflexive conjugation of the original
second mapped loop remains. -/
public theorem traceLoopFamily_one (H : Homotopy f g) (x : X)
    (gamma : LoopSpace X x) :
    traceLoopFamily H x (1, gamma) =
      loopBasepointChange (Path.refl (g x)) (strictLoopMap g x gamma) :=
  traceLoopFamily_one_computed H x gamma

/-- The ordinary homotopy trace gives a genuine homotopy between the
whole conjugated first loop map and the whole second loop map. -/
public def traceConjugationLoopHomotopy (H : Homotopy f g) (x : X) :
    Homotopy ((loopBasepointChange (H.evalAt x)).comp (strictLoopMap f x))
      (strictLoopMap g x) := by
  let K : Homotopy
      ((loopBasepointChange (H.evalAt x)).comp (strictLoopMap f x))
      ((loopBasepointChange (Path.refl (g x))).comp (strictLoopMap g x)) :=
    { toContinuousMap := traceLoopFamily H x
      map_zero_left gamma := traceLoopFamily_zero H x gamma
      map_one_left gamma := traceLoopFamily_one H x gamma }
  let U := (loopBasepointChangeReflHomotopy (g x)).compContinuousMap (strictLoopMap g x)
  exact K.trans (U.cast rfl rfl)

private theorem originalTraceConjugationUnitPiecewiseComputed
    (H : Homotopy f g) (x : X) (t : I) :
    traceConjugationLoopHomotopy H x (t, Path.refl x) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        traceLoopFamily H x
          (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩,
            Path.refl x)
      else Path.refl (g x) := by
  let K : Homotopy
      ((loopBasepointChange (H.evalAt x)).comp (strictLoopMap f x))
      ((loopBasepointChange (Path.refl (g x))).comp (strictLoopMap g x)) :=
    { toContinuousMap := traceLoopFamily H x
      map_zero_left gamma := traceLoopFamily_zero H x gamma
      map_one_left gamma := traceLoopFamily_one H x gamma }
  let U := (loopBasepointChangeReflHomotopy (g x)).compContinuousMap (strictLoopMap g x)
  have hValue : traceConjugationLoopHomotopy H x (t, Path.refl x) =
      (K.trans (U.cast rfl rfl)) (t, Path.refl x) := rfl
  refine hValue.trans ?_
  rw [Homotopy.trans_apply]
  split_ifs with ht
  · rfl
  · let r : I := ⟨2 * (t : ℝ) - 1,
      unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
    change loopBasepointChangeReflHomotopy (g x)
      (r, strictLoopMap g x (Path.refl x)) = Path.refl (g x)
    exact (congrArg (fun gamma : LoopSpace Y (g x) =>
      loopBasepointChangeReflHomotopy (g x) (r, gamma)) (strictLoopMap_refl g x)).trans
        (loopBasepointChangeReflHomotopy_refl (g x) r)

/-- The actual unit trace keeps the original two clock branches; its
final branch is constant by the original reflexive-conjugation unit equation. -/
public theorem traceConjugationLoopHomotopy_refl_piecewise
    (H : Homotopy f g) (x : X) (t : I) :
    traceConjugationLoopHomotopy H x (t, Path.refl x) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        traceLoopFamily H x
          (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩,
            Path.refl x)
      else Path.refl (g x) :=
  originalTraceConjugationUnitPiecewiseComputed H x t

/-- The literal interval-coordinate homotopy, with value equal to its
time coordinate and constant spatial endpoint maps. -/
public def intervalCoordinateHomotopy :
    Homotopy (ContinuousMap.const I (0 : I)) (ContinuousMap.const I (1 : I)) where
  toFun p := p.1
  continuous_toFun := continuous_fst
  map_zero_left _ := rfl
  map_one_left _ := rfl

private theorem intervalCoordinateHomotopy_apply_computed (t s : I) :
    intervalCoordinateHomotopy (t, s) = t := rfl

/-- The coordinate template retains the actual time parameter. -/
public theorem intervalCoordinateHomotopy_apply (t s : I) :
    intervalCoordinateHomotopy (t, s) = t :=
  intervalCoordinateHomotopy_apply_computed t s

private theorem traceLoopFamily_refl_template_computed
    (H : Homotopy f g) (x : X) (t s : I) :
    traceLoopFamily H x (t, Path.refl x) s =
      H.evalAt x (traceLoopFamily intervalCoordinateHomotopy (0 : I)
        (t, Path.refl (0 : I)) s) := by
  change (traceTail H x t).symm.trans
      ((mappedAt H x (Path.refl x) t).trans (traceTail H x t)) s =
    H.evalAt x ((traceTail intervalCoordinateHomotopy (0 : I) t).symm.trans
      ((mappedAt intervalCoordinateHomotopy (0 : I) (Path.refl (0 : I)) t).trans
        (traceTail intervalCoordinateHomotopy (0 : I) t)) s)
  simp only [Path.trans_apply, Path.symm_apply]
  split_ifs <;> rfl

private theorem traceConjugationLoopHomotopy_refl_template_computed
    (H : Homotopy f g) (x : X) (t s : I) :
    traceConjugationLoopHomotopy H x (t, Path.refl x) s =
      H.evalAt x (traceConjugationLoopHomotopy intervalCoordinateHomotopy (0 : I)
        (t, Path.refl (0 : I)) s) := by
  unfold traceConjugationLoopHomotopy
  simp only [Homotopy.trans_apply]
  split_ifs with h
  · exact traceLoopFamily_refl_template_computed H x _ s
  · let r : I := ⟨2 * (t : ℝ) - 1,
      unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩
    change loopBasepointChangeReflHomotopy (g x)
        (r, strictLoopMap g x (Path.refl x)) s =
      H.evalAt x (loopBasepointChangeReflHomotopy (1 : I)
        (r, strictLoopMap (ContinuousMap.const I (1 : I)) (0 : I) (Path.refl (0 : I))) s)
    have hMapped : strictLoopMap g x (Path.refl x) = Path.refl (g x) :=
      strictLoopMap_refl g x
    have hUnit : loopBasepointChangeReflHomotopy (g x)
        (r, strictLoopMap g x (Path.refl x)) = Path.refl (g x) :=
      (congrArg (fun gamma : LoopSpace Y (g x) =>
        loopBasepointChangeReflHomotopy (g x) (r, gamma)) hMapped).trans
          (loopBasepointChangeReflHomotopy_refl (g x) r)
    have hCoordinateMapped :
        strictLoopMap (ContinuousMap.const I (1 : I)) (0 : I) (Path.refl (0 : I)) =
          Path.refl (1 : I) := strictLoopMap_refl (ContinuousMap.const I (1 : I)) (0 : I)
    have hCoordinateUnit : loopBasepointChangeReflHomotopy (1 : I)
        (r, strictLoopMap (ContinuousMap.const I (1 : I)) (0 : I) (Path.refl (0 : I))) =
          Path.refl (1 : I) :=
      (congrArg (fun gamma : LoopSpace I (1 : I) =>
        loopBasepointChangeReflHomotopy (1 : I) (r, gamma)) hCoordinateMapped).trans
          (loopBasepointChangeReflHomotopy_refl (1 : I) r)
    have hLeft : loopBasepointChangeReflHomotopy (g x)
        (r, strictLoopMap g x (Path.refl x)) s = g x :=
      congrArg (fun gamma : LoopSpace Y (g x) => gamma s) hUnit
    have hRight : H.evalAt x (loopBasepointChangeReflHomotopy (1 : I)
        (r, strictLoopMap (ContinuousMap.const I (1 : I)) (0 : I) (Path.refl (0 : I))) s) =
          H.evalAt x 1 :=
      congrArg (H.evalAt x) (congrArg (fun gamma : LoopSpace I (1 : I) => gamma s)
        hCoordinateUnit)
    have hEndpoint : g x = H.evalAt x 1 := (H.apply_one x).symm
    exact hLeft.trans (hEndpoint.trans hRight.symm)

/-- The actual constant-loop trace is the point-trace image of the fixed
interval template, including the chosen unit-homotopy branch at every time. -/
public theorem traceConjugationLoopHomotopy_refl_template_value
    (H : Homotopy f g) (x : X) (t s : I) :
    traceConjugationLoopHomotopy H x (t, Path.refl x) s =
      H.evalAt x (traceConjugationLoopHomotopy intervalCoordinateHomotopy (0 : I)
        (t, Path.refl (0 : I)) s) :=
  traceConjugationLoopHomotopy_refl_template_computed H x t s

end Homotopy

namespace WeaklyPointed

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- An ordinary homotopy and its compatible chosen point trace give a
joint homotopy of the complete weakly pointed loop maps. -/
public def loopMapHomotopyOfMap (f g : WeaklyPointed x y)
    (H : Homotopy f.hom g.hom)
    (Hp : f.rootPath.Homotopy ((H.evalAt x).trans g.rootPath)) :
    Homotopy f.loopMap g.loopMap := by
  let m : WeaklyPointed x y := ⟨f.hom, (H.evalAt x).trans g.rootPath⟩
  let H1 : Homotopy f.loopMap m.loopMap := loopMapRootPathHomotopy f.hom Hp
  let H2 := (loopBasepointChangeTransHomotopy (H.evalAt x) g.rootPath).compContinuousMap
    (strictLoopMap f.hom x)
  let H2' : Homotopy m.loopMap
      (((loopBasepointChange g.rootPath).comp (loopBasepointChange (H.evalAt x))).comp
        (strictLoopMap f.hom x)) :=
    H2.cast (loopMap_eq_loopBasepointChange_comp_strictLoopMap m).symm rfl
  let H3 := (Homotopy.refl (loopBasepointChange g.rootPath)).comp
    (Homotopy.traceConjugationLoopHomotopy H x)
  have hsource : (loopBasepointChange g.rootPath).comp
      ((loopBasepointChange (H.evalAt x)).comp (strictLoopMap f.hom x)) =
        ((loopBasepointChange g.rootPath).comp (loopBasepointChange (H.evalAt x))).comp
          (strictLoopMap f.hom x) := by
    apply ContinuousMap.ext
    intro gamma
    rfl
  let H3' : Homotopy
      (((loopBasepointChange g.rootPath).comp (loopBasepointChange (H.evalAt x))).comp
        (strictLoopMap f.hom x)) g.loopMap :=
    H3.cast hsource (loopMap_eq_loopBasepointChange_comp_strictLoopMap g).symm
  exact H1.trans (H2'.trans H3')

private theorem originalLoopMapHomotopyOfMapValueComputed (f g : WeaklyPointed x y)
    (H : Homotopy f.hom g.hom)
    (Hp : f.rootPath.Homotopy ((H.evalAt x).trans g.rootPath))
    (t : I) (gamma : LoopSpace X x) :
    loopMapHomotopyOfMap f g H Hp (t, gamma) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        loopMapRootPathHomotopy f.hom Hp
          (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨unitInterval.nonneg t, ht⟩⟩, gamma)
      else
        let r : I := ⟨2 * (t : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩
        if hr : (r : ℝ) ≤ 1 / 2 then
          loopBasepointChangeTransHomotopy (H.evalAt x) g.rootPath
            (⟨2 * (r : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨unitInterval.nonneg r, hr⟩⟩, strictLoopMap f.hom x gamma)
        else
          loopBasepointChange g.rootPath
            (Homotopy.traceConjugationLoopHomotopy H x
              (⟨2 * (r : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 hr).le, unitInterval.le_one r⟩⟩, gamma)) := by
  let m : WeaklyPointed x y := ⟨f.hom, (H.evalAt x).trans g.rootPath⟩
  let H1 : Homotopy f.loopMap m.loopMap := loopMapRootPathHomotopy f.hom Hp
  let H2 := (loopBasepointChangeTransHomotopy (H.evalAt x) g.rootPath).compContinuousMap
    (strictLoopMap f.hom x)
  let H2' : Homotopy m.loopMap
      (((loopBasepointChange g.rootPath).comp (loopBasepointChange (H.evalAt x))).comp
        (strictLoopMap f.hom x)) :=
    H2.cast (loopMap_eq_loopBasepointChange_comp_strictLoopMap m).symm rfl
  let H3 := (Homotopy.refl (loopBasepointChange g.rootPath)).comp
    (Homotopy.traceConjugationLoopHomotopy H x)
  have hsource : (loopBasepointChange g.rootPath).comp
      ((loopBasepointChange (H.evalAt x)).comp (strictLoopMap f.hom x)) =
        ((loopBasepointChange g.rootPath).comp (loopBasepointChange (H.evalAt x))).comp
          (strictLoopMap f.hom x) := by
    apply ContinuousMap.ext
    intro gamma
    rfl
  let H3' : Homotopy
      (((loopBasepointChange g.rootPath).comp (loopBasepointChange (H.evalAt x))).comp
        (strictLoopMap f.hom x)) g.loopMap :=
    H3.cast hsource (loopMap_eq_loopBasepointChange_comp_strictLoopMap g).symm
  have hValue : loopMapHomotopyOfMap f g H Hp (t, gamma) =
      (H1.trans (H2'.trans H3')) (t, gamma) := rfl
  refine hValue.trans ?_
  rw [Homotopy.trans_apply]
  split_ifs with ht
  · rfl
  · rw [Homotopy.trans_apply]
    dsimp only
    split_ifs with hr <;> rfl

/-- The whole original loop-map homotopy retains its actual first root
homotopy and original middle and final families, with the two original
nested half clocks and all endpoint transports. -/
public theorem loopMapHomotopyOfMap_apply (f g : WeaklyPointed x y)
    (H : Homotopy f.hom g.hom)
    (Hp : f.rootPath.Homotopy ((H.evalAt x).trans g.rootPath))
    (t : I) (gamma : LoopSpace X x) :
    loopMapHomotopyOfMap f g H Hp (t, gamma) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        loopMapRootPathHomotopy f.hom Hp
          (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨unitInterval.nonneg t, ht⟩⟩, gamma)
      else
        let r : I := ⟨2 * (t : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩
        if hr : (r : ℝ) ≤ 1 / 2 then
          loopBasepointChangeTransHomotopy (H.evalAt x) g.rootPath
            (⟨2 * (r : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
              ⟨unitInterval.nonneg r, hr⟩⟩, strictLoopMap f.hom x gamma)
        else
          loopBasepointChange g.rootPath
            (Homotopy.traceConjugationLoopHomotopy H x
              (⟨2 * (r : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 hr).le, unitInterval.le_one r⟩⟩, gamma)) :=
  originalLoopMapHomotopyOfMapValueComputed f g H Hp t gamma

end WeaklyPointed

namespace HomotopyEquiv

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

private theorem rootCancelHomotopic {Z : Type*} [TopologicalSpace Z]
    {a b c : Z} (p : Path a b) (r : Path a c) :
    (p.trans (p.symm.trans r)).Homotopic r :=
  (Path.Homotopic.trans_assoc p p.symm r).symm.trans
    (((Path.Homotopic.trans_symm p).hcomp (Path.Homotopic.refl r)).trans
      (Path.Homotopic.refl_trans r))

/-- An unbased homotopy equivalence lifts to loop spaces using the actual
chosen point path. Both inverse families are constructed without loop-space
CW assumptions or extra coherence supplied by a caller. -/
public def weaklyPointedLoopHomotopyEquiv (e : X ≃ₕ Y) (x : X) {y : Y}
    (p : Path (e.toFun x) y) : LoopSpace X x ≃ₕ LoopSpace Y y := by
  let L := e.left_inv.some
  let R := e.right_inv.some
  let ell := L.evalAt x
  let pg := p.map e.invFun.continuous
  let q : Path (e.invFun y) x := pg.symm.trans ell
  let f : WeaklyPointed x y := ⟨e.toFun, p⟩
  let g : WeaklyPointed y x := ⟨e.invFun, q⟩
  let F := f.loopMap
  let G := g.loopMap
  have hPointL : (WeaklyPointed.comp f g).rootPath.Homotopic
      ((L.evalAt x).trans (WeaklyPointed.id x).rootPath) := by
    change (pg.trans (pg.symm.trans ell)).Homotopic (ell.trans (Path.refl x))
    exact (rootCancelHomotopic pg ell).trans (Path.Homotopic.trans_refl ell).symm
  let KL := WeaklyPointed.loopMapHomotopyOfMap (WeaklyPointed.comp f g)
    (WeaklyPointed.id x) L hPointL.some
  let HL : Homotopy (G.comp F) (ContinuousMap.id (LoopSpace X x)) :=
    (WeaklyPointed.loopMapCompHomotopy f g).symm.trans
      (KL.trans (WeaklyPointed.loopMapIdHomotopy x))
  let rho := R.evalAt y
  let r := (WeaklyPointed.comp g f).rootPath
  let d : Path y y := rho.symm.trans r
  let i : WeaklyPointed y y := ⟨ContinuousMap.id Y, d⟩
  have hPointR : (WeaklyPointed.comp g f).rootPath.Homotopic
      ((R.evalAt y).trans i.rootPath) := by
    change r.Homotopic (rho.trans (rho.symm.trans r))
    exact (rootCancelHomotopic rho r).symm
  let KR := WeaklyPointed.loopMapHomotopyOfMap (WeaklyPointed.comp g f) i R hPointR.some
  have hIdMap : i.loopMap = loopBasepointChange d := by
    have hFactor : i.loopMap =
        (loopBasepointChange d).comp (strictLoopMap (ContinuousMap.id Y) y) :=
      WeaklyPointed.loopMap_eq_loopBasepointChange_comp_strictLoopMap i
    have hStrict : (loopBasepointChange d).comp (strictLoopMap (ContinuousMap.id Y) y) =
        (loopBasepointChange d).comp (ContinuousMap.id (LoopSpace Y y)) :=
      congrArg (fun f : C(LoopSpace Y y, LoopSpace Y y) =>
        (loopBasepointChange d).comp f) (strictLoopMap_id y)
    have hIdentity : (loopBasepointChange d).comp (ContinuousMap.id (LoopSpace Y y)) =
        loopBasepointChange d := by
      apply ContinuousMap.ext
      intro gamma
      rfl
    exact hFactor.trans (hStrict.trans hIdentity)
  let J := loopBasepointChangeHomotopyEquiv d
  let HR : Homotopy (F.comp G) J.toFun :=
    ((WeaklyPointed.loopMapCompHomotopy g f).symm.trans KR).cast rfl
      (hIdMap.trans (loopBasepointChangeHomotopyEquiv_toFun d).symm)
  let G2 := G.comp J.invFun
  let HR2 : Homotopy (F.comp G2) (ContinuousMap.id (LoopSpace Y y)) :=
    (HR.compContinuousMap J.invFun).trans J.right_inv.some
  let H1 := (Homotopy.refl G).comp HR2.symm
  have hstart : G.comp (ContinuousMap.id (LoopSpace Y y)) = G := by
    apply ContinuousMap.ext
    intro gamma
    rfl
  have hmiddle : G.comp (F.comp G2) = (G.comp F).comp G2 := by
    apply ContinuousMap.ext
    intro gamma
    rfl
  let H1' : Homotopy G ((G.comp F).comp G2) := H1.cast hstart hmiddle
  let H2 := HL.compContinuousMap G2
  have hend : (ContinuousMap.id (LoopSpace X x)).comp G2 = G2 := by
    apply ContinuousMap.ext
    intro gamma
    rfl
  let H2' : Homotopy ((G.comp F).comp G2) G2 := H2.cast rfl hend
  let HG := H1'.trans H2'
  let HL2 : Homotopy (G2.comp F) (ContinuousMap.id (LoopSpace X x)) :=
    (HG.symm.compContinuousMap F).trans HL
  exact
    { toFun := F
      invFun := G2
      left_inv := ⟨HL2⟩
      right_inv := ⟨HR2⟩ }

private theorem weaklyPointedLoopHomotopyEquiv_toFun_computed (e : X ≃ₕ Y)
    (x : X) {y : Y} (p : Path (e.toFun x) y) :
    (weaklyPointedLoopHomotopyEquiv e x p).toFun =
      (⟨e.toFun, p⟩ : WeaklyPointed x y).loopMap := rfl

/-- The lifted equivalence's forward map is the original weakly pointed
loop map along the specified point path, without retuning its values. -/
public theorem weaklyPointedLoopHomotopyEquiv_toFun (e : X ≃ₕ Y)
    (x : X) {y : Y} (p : Path (e.toFun x) y) :
    (weaklyPointedLoopHomotopyEquiv e x p).toFun =
      (⟨e.toFun, p⟩ : WeaklyPointed x y).loopMap :=
  weaklyPointedLoopHomotopyEquiv_toFun_computed e x p

end HomotopyEquiv

end ContinuousMap

end


noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v

namespace ContinuousMap.HomotopyEquiv

private theorem originalWeakLoopInverseProgramComputed
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) {y : Y} (p : Path (e.toFun x) y) :
    let L := e.left_inv.some
    let R := e.right_inv.some
    let q := (p.map e.invFun.continuous).symm.trans (L.evalAt x)
    let f : WeaklyPointed x y := ⟨e.toFun, p⟩
    let g : WeaklyPointed y x := ⟨e.invFun, q⟩
    let d := (R.evalAt y).symm.trans (WeaklyPointed.comp g f).rootPath
    (weaklyPointedLoopHomotopyEquiv e x p).invFun =
      g.loopMap.comp (loopBasepointChangeHomotopyEquiv d).invFun := rfl

/-- The ENTIRE original weak-loop inverse keeps EXACT original L/R.some,
chosen point path and defect-J correction. No inverse choice is replaced. -/
public theorem weaklyPointedLoopHomotopyEquiv_invFun_recipe
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) {y : Y} (p : Path (e.toFun x) y) :
    let L := e.left_inv.some
    let R := e.right_inv.some
    let q := (p.map e.invFun.continuous).symm.trans (L.evalAt x)
    let f : WeaklyPointed x y := ⟨e.toFun, p⟩
    let g : WeaklyPointed y x := ⟨e.invFun, q⟩
    let d := (R.evalAt y).symm.trans (WeaklyPointed.comp g f).rootPath
    (weaklyPointedLoopHomotopyEquiv e x p).invFun =
      g.loopMap.comp (loopBasepointChangeHomotopyEquiv d).invFun :=
  originalWeakLoopInverseProgramComputed e x p

private def originalWeakLoopInverseToRawFamily
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) {y : Y} (p : Path (e.toFun x) y) :
    let L := e.left_inv.some
    let q := (p.map e.invFun.continuous).symm.trans (L.evalAt x)
    let g : WeaklyPointed y x := ⟨e.invFun, q⟩
    Homotopy (weaklyPointedLoopHomotopyEquiv e x p).invFun g.loopMap := by
  let L := e.left_inv.some
  let R := e.right_inv.some
  let ell := L.evalAt x
  let pg := p.map e.invFun.continuous
  let q : Path (e.invFun y) x := pg.symm.trans ell
  let f : WeaklyPointed x y := ⟨e.toFun, p⟩
  let g : WeaklyPointed y x := ⟨e.invFun, q⟩
  let F := f.loopMap
  let G := g.loopMap
  have hPointL : (WeaklyPointed.comp f g).rootPath.Homotopic
      ((L.evalAt x).trans (WeaklyPointed.id x).rootPath) := by
    change (pg.trans (pg.symm.trans ell)).Homotopic (ell.trans (Path.refl x))
    exact (rootCancelHomotopic pg ell).trans (Path.Homotopic.trans_refl ell).symm
  let KL := WeaklyPointed.loopMapHomotopyOfMap (WeaklyPointed.comp f g)
    (WeaklyPointed.id x) L hPointL.some
  let HL : Homotopy (G.comp F) (ContinuousMap.id (LoopSpace X x)) :=
    (WeaklyPointed.loopMapCompHomotopy f g).symm.trans
      (KL.trans (WeaklyPointed.loopMapIdHomotopy x))
  let rho := R.evalAt y
  let r := (WeaklyPointed.comp g f).rootPath
  let d : Path y y := rho.symm.trans r
  let i : WeaklyPointed y y := ⟨ContinuousMap.id Y, d⟩
  have hPointR : (WeaklyPointed.comp g f).rootPath.Homotopic
      ((R.evalAt y).trans i.rootPath) := by
    change r.Homotopic (rho.trans (rho.symm.trans r))
    exact (rootCancelHomotopic rho r).symm
  let KR := WeaklyPointed.loopMapHomotopyOfMap (WeaklyPointed.comp g f) i R hPointR.some
  have hIdMap : i.loopMap = loopBasepointChange d := by
    have hFactor : i.loopMap =
        (loopBasepointChange d).comp (strictLoopMap (ContinuousMap.id Y) y) :=
      WeaklyPointed.loopMap_eq_loopBasepointChange_comp_strictLoopMap i
    have hStrict : (loopBasepointChange d).comp (strictLoopMap (ContinuousMap.id Y) y) =
        (loopBasepointChange d).comp (ContinuousMap.id (LoopSpace Y y)) :=
      congrArg (fun f : C(LoopSpace Y y, LoopSpace Y y) =>
        (loopBasepointChange d).comp f) (strictLoopMap_id y)
    have hIdentity : (loopBasepointChange d).comp (ContinuousMap.id (LoopSpace Y y)) =
        loopBasepointChange d := by
      apply ContinuousMap.ext
      intro gamma
      rfl
    exact hFactor.trans (hStrict.trans hIdentity)
  let J := loopBasepointChangeHomotopyEquiv d
  let HR : Homotopy (F.comp G) J.toFun :=
    ((WeaklyPointed.loopMapCompHomotopy g f).symm.trans KR).cast rfl
      (hIdMap.trans (loopBasepointChangeHomotopyEquiv_toFun d).symm)
  let G2 := G.comp J.invFun
  let HR2 : Homotopy (F.comp G2) (ContinuousMap.id (LoopSpace Y y)) :=
    (HR.compContinuousMap J.invFun).trans J.right_inv.some
  let H1 := (Homotopy.refl G).comp HR2.symm
  have hstart : G.comp (ContinuousMap.id (LoopSpace Y y)) = G := by
    apply ContinuousMap.ext
    intro gamma
    rfl
  have hmiddle : G.comp (F.comp G2) = (G.comp F).comp G2 := by
    apply ContinuousMap.ext
    intro gamma
    rfl
  let H1' : Homotopy G ((G.comp F).comp G2) := H1.cast hstart hmiddle
  let H2 := HL.compContinuousMap G2
  have hend : (ContinuousMap.id (LoopSpace X x)).comp G2 = G2 := by
    apply ContinuousMap.ext
    intro gamma
    rfl
  let H2' : Homotopy ((G.comp F).comp G2) G2 := H2.cast rfl hend
  let HG := H1'.trans H2'
  have hInverse : (weaklyPointedLoopHomotopyEquiv e x p).invFun = G2 :=
    weaklyPointedLoopHomotopyEquiv_invFun_recipe e x p
  exact HG.symm.cast hInverse.symm rfl

/-- The ACTUAL complete original inverse correction family returns G2 to G,
retaining the original program's BOTH inverse families and all Some/J choices. -/
public def weaklyPointedLoopHomotopyEquivInvFunToRawHomotopy
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) {y : Y} (p : Path (e.toFun x) y) :
    let L := e.left_inv.some
    let q := (p.map e.invFun.continuous).symm.trans (L.evalAt x)
    let g : WeaklyPointed y x := ⟨e.invFun, q⟩
    Homotopy (weaklyPointedLoopHomotopyEquiv e x p).invFun g.loopMap :=
  originalWeakLoopInverseToRawFamily e x p

end ContinuousMap.HomotopyEquiv

end
