/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.PathReparametrization
public import MathlibExt.Topology.Homotopy.WeaklyPointed.WeaklyPointedLoopMapFactorization
public import MathlibExt.Topology.Homotopy.ContinuousMappedLoopHomotopy

/-!
# Jointly continuous coherence for weakly pointed loop maps

Uniform path reparameterizations give associativity and unit homotopies on
entire path spaces. They supply identity and composition homotopies for the
actual conjugation maps on loops. A homotopy of chosen point paths also gives
one continuous family over homotopy time and every original source loop.

The existing jointly continuous mapped-loop family is reused when the
underlying map varies relative to its source point. No family of separately
chosen loop homotopies is promoted to continuity, and no topology or model
structure on a raw loop space is assumed beyond its ordinary path topology.
-/

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe u v w

namespace ContinuousMap

section Paths

variable {X : Type u} [TopologicalSpace X]

/-- Left-associated concatenation on the whole space of three composable paths. -/
public abbrev pathTripleAssocLeft (a b c d : X) :
    C((Path a b × Path b c) × Path c d, Path a d) where
  toFun p := (p.1.1.trans p.1.2).trans p.2
  continuous_toFun :=
    Continuous.path_trans
      (Continuous.path_trans (continuous_fst.comp continuous_fst)
        (continuous_snd.comp continuous_fst)) continuous_snd

/-- Right-associated concatenation on the same whole space of paths. -/
public abbrev pathTripleAssocRight (a b c d : X) :
    C((Path a b × Path b c) × Path c d, Path a d) where
  toFun p := p.1.1.trans (p.1.2.trans p.2)
  continuous_toFun :=
    Continuous.path_trans (continuous_fst.comp continuous_fst)
      (Continuous.path_trans (continuous_snd.comp continuous_fst) continuous_snd)

private def assocReparam : I → I := fun t =>
  ⟨Path.Homotopy.transAssocReparamAux t,
    Path.Homotopy.transAssocReparamAux_mem_I t⟩

private theorem assocReparam_continuous : Continuous (assocReparam : I → I) := by
  apply Continuous.subtype_mk
  exact Path.Homotopy.continuous_transAssocReparamAux

private theorem assocReparam_zero : assocReparam 0 = 0 := by
  apply Subtype.ext
  exact Path.Homotopy.transAssocReparamAux_zero

private theorem assocReparam_one : assocReparam 1 = 1 := by
  apply Subtype.ext
  exact Path.Homotopy.transAssocReparamAux_one

/-- Associativity is a jointly continuous homotopy of the two complete
concatenation maps, using the same uniform interval reparameterization. -/
public def pathTripleAssocHomotopy (a b c d : X) :
    Homotopy (pathTripleAssocLeft a b c d) (pathTripleAssocRight a b c d) := by
  let H := (pathReparamMapHomotopy (a := a) (b := d) assocReparam
    assocReparam_continuous assocReparam_zero assocReparam_one).compContinuousMap
      (pathTripleAssocRight a b c d)
  have hsource : (pathReparamMap assocReparam assocReparam_continuous
      assocReparam_zero assocReparam_one).comp (pathTripleAssocRight a b c d) =
        pathTripleAssocLeft a b c d := by
    apply ContinuousMap.ext
    intro p
    exact (Path.Homotopy.trans_assoc_reparam p.1.1 p.1.2 p.2).symm
  exact H.cast hsource rfl

private theorem originalPathTripleAssocValueComputed
    {a b c d : X} (p : Path a b) (q : Path b c) (r : Path c d) (t s : I) :
    pathTripleAssocHomotopy a b c d (t, ((p, q), r)) s =
      (p.trans (q.trans r)) (Set.Icc.convexComb
        (⟨Path.Homotopy.transAssocReparamAux s,
          Path.Homotopy.transAssocReparamAux_mem_I s⟩ : I) s t) :=
  pathReparamMapHomotopy_apply assocReparam assocReparam_continuous
    assocReparam_zero assocReparam_one (p.trans (q.trans r)) t s

/-- Every original association time and path time have the actual
uniform affine reparameterization, using the public bounded interval coordinate. -/
public theorem pathTripleAssocHomotopy_apply
    {a b c d : X} (p : Path a b) (q : Path b c) (r : Path c d) (t s : I) :
    pathTripleAssocHomotopy a b c d (t, ((p, q), r)) s =
      (p.trans (q.trans r)) (Set.Icc.convexComb
        (⟨Path.Homotopy.transAssocReparamAux s,
          Path.Homotopy.transAssocReparamAux_mem_I s⟩ : I) s t) :=
  originalPathTripleAssocValueComputed p q r t s

/-- Append the reflexive endpoint path to every path. -/
public abbrev pathAppendRefl (a b : X) : C(Path a b, Path a b) where
  toFun p := p.trans (Path.refl b)
  continuous_toFun := Continuous.path_trans continuous_id continuous_const

/-- Prepend the reflexive initial path to every path. -/
public abbrev pathPrependRefl (a b : X) : C(Path a b, Path a b) where
  toFun p := (Path.refl a).trans p
  continuous_toFun := Continuous.path_trans continuous_const continuous_id

/-- Reverse every path continuously. -/
public abbrev pathSymmMap (a b : X) : C(Path a b, Path b a) :=
  ⟨Path.symm, Path.continuous_symm⟩

private def appendReflReparam : I → I := fun t =>
  ⟨Path.Homotopy.transReflReparamAux t,
    Path.Homotopy.transReflReparamAux_mem_I t⟩

private theorem appendReflReparam_continuous :
    Continuous (appendReflReparam : I → I) := by
  apply Continuous.subtype_mk
  exact Path.Homotopy.continuous_transReflReparamAux

private theorem appendReflReparam_zero : appendReflReparam 0 = 0 := by
  apply Subtype.ext
  exact Path.Homotopy.transReflReparamAux_zero

private theorem appendReflReparam_one : appendReflReparam 1 = 1 := by
  apply Subtype.ext
  exact Path.Homotopy.transReflReparamAux_one

/-- Appending a reflexive path is homotopic to the identity by one
continuous family on the entire original path space. -/
public def pathAppendReflHomotopy (a b : X) :
    Homotopy (pathAppendRefl a b) (ContinuousMap.id (Path a b)) := by
  let H := pathReparamMapHomotopy (a := a) (b := b) appendReflReparam
    appendReflReparam_continuous appendReflReparam_zero appendReflReparam_one
  have hsource : pathReparamMap appendReflReparam appendReflReparam_continuous
      appendReflReparam_zero appendReflReparam_one = pathAppendRefl a b := by
    apply ContinuousMap.ext
    intro p
    exact (Path.Homotopy.trans_refl_reparam p).symm
  exact H.cast hsource rfl

/-- Prepending a reflexive path is also homotopic to the identity on the
whole path space, by reversing the preceding continuous unit family. -/
public def pathPrependReflHomotopy (a b : X) :
    Homotopy (pathPrependRefl a b) (ContinuousMap.id (Path a b)) := by
  let S := pathSymmMap a b
  let T := pathSymmMap b a
  let H := (Homotopy.refl T).comp
    ((pathAppendReflHomotopy b a).compContinuousMap S)
  have hsource : T.comp ((pathAppendRefl b a).comp S) = pathPrependRefl a b := by
    apply ContinuousMap.ext
    intro p
    change (p.symm.trans (Path.refl a)).symm = (Path.refl a).trans p
    rw [Path.trans_symm, Path.refl_symm, Path.symm_symm]
  have htarget : T.comp ((ContinuousMap.id (Path b a)).comp S) =
      ContinuousMap.id (Path a b) := by
    apply ContinuousMap.ext
    intro p
    exact Path.symm_symm p
  exact H.cast hsource htarget

/-- Conjugation along homotopic point paths gives a jointly continuous
homotopy on every loop, with the original target point fixed. -/
public def loopBasepointChangePathHomotopy {x y : X} {p q : Path x y}
    (H : p.Homotopy q) : Homotopy (loopBasepointChange p) (loopBasepointChange q) where
  toFun s := (H.eval s.1).symm.trans (s.2.trans (H.eval s.1))
  map_zero_left gamma := by
    rw [Path.Homotopy.eval_zero]
    rfl
  map_one_left gamma := by
    rw [Path.Homotopy.eval_one]
    rfl
  continuous_toFun := by
    let E : C(I, Path x y) :=
      ⟨H.eval, Path.continuous_uncurry_iff.mp H.continuous_toFun⟩
    have hRoot : Continuous (fun s : I × LoopSpace X x => H.eval s.1) :=
      E.continuous.comp continuous_fst
    exact Continuous.path_trans (Path.continuous_symm.comp hRoot)
      (Continuous.path_trans continuous_snd hRoot)

private theorem originalLoopBasepointChangePathHomotopyValueComputed
    {x y : X} {p q : Path x y} (H : p.Homotopy q)
    (t : I) (gamma : LoopSpace X x) :
    loopBasepointChangePathHomotopy H (t, gamma) =
      (H.eval t).symm.trans (gamma.trans (H.eval t)) := rfl

/-- Every actual root-homotopy time gives the original three-piece
conjugation loop, with the same chosen root homotopy and whole input loop. -/
public theorem loopBasepointChangePathHomotopy_apply
    {x y : X} {p q : Path x y} (H : p.Homotopy q)
    (t : I) (gamma : LoopSpace X x) :
    loopBasepointChangePathHomotopy H (t, gamma) =
      (H.eval t).symm.trans (gamma.trans (H.eval t)) :=
  originalLoopBasepointChangePathHomotopyValueComputed H t gamma

/-- Conjugation along the reflexive point path is continuously homotopic
to the identity on the whole based loop space. -/
public def loopBasepointChangeReflHomotopy (x : X) :
    Homotopy (loopBasepointChange (Path.refl x)) (ContinuousMap.id (LoopSpace X x)) := by
  let H := (pathPrependReflHomotopy x x).compContinuousMap (pathAppendRefl x x)
  have hsource : (pathPrependRefl x x).comp (pathAppendRefl x x) =
      loopBasepointChange (Path.refl x) := by
    apply ContinuousMap.ext
    intro gamma
    change (Path.refl x).trans (gamma.trans (Path.refl x)) =
      (Path.refl x).symm.trans (gamma.trans (Path.refl x))
    rw [Path.refl_symm]
  exact (H.cast hsource rfl).trans (pathAppendReflHomotopy x x)

/-- Successive changes of loop basepoint agree with change along the
concatenated point path by a jointly continuous reassociation family. -/
public def loopBasepointChangeTransHomotopy {x y z : X}
    (p : Path x y) (q : Path y z) :
    Homotopy (loopBasepointChange (p.trans q))
      ((loopBasepointChange q).comp (loopBasepointChange p)) := by
  let c1 : C(LoopSpace X x, (Path z y × Path y x) × Path x z) :=
    ⟨fun gamma => ((q.symm, p.symm), gamma.trans (p.trans q)), by fun_prop⟩
  let c2 : C(LoopSpace X x, (Path x x × Path x y) × Path y z) :=
    ⟨fun gamma => ((gamma, p), q), by fun_prop⟩
  let c3 : C(LoopSpace X x, (Path y x × Path x y) × Path y z) :=
    ⟨fun gamma => ((p.symm, gamma.trans p), q), by fun_prop⟩
  let prefix2 : C(Path x z, LoopSpace X z) :=
    ⟨fun r => q.symm.trans (p.symm.trans r), by fun_prop⟩
  let prefix1 : C(Path y z, LoopSpace X z) :=
    ⟨fun r => q.symm.trans r, by fun_prop⟩
  let A1 : C(LoopSpace X x, LoopSpace X z) :=
    ⟨fun gamma => q.symm.trans (p.symm.trans (gamma.trans (p.trans q))), by fun_prop⟩
  let A2 : C(LoopSpace X x, LoopSpace X z) :=
    ⟨fun gamma => q.symm.trans (p.symm.trans ((gamma.trans p).trans q)), by fun_prop⟩
  let H1 := (pathTripleAssocHomotopy z y x z).compContinuousMap c1
  have hsource : (pathTripleAssocLeft z y x z).comp c1 =
      loopBasepointChange (p.trans q) := by
    apply ContinuousMap.ext
    intro gamma
    change (q.symm.trans p.symm).trans (gamma.trans (p.trans q)) =
      (p.trans q).symm.trans (gamma.trans (p.trans q))
    rw [Path.trans_symm]
  let H1' : Homotopy (loopBasepointChange (p.trans q)) A1 := H1.cast hsource rfl
  let H2 := (Homotopy.refl prefix2).comp
    (((pathTripleAssocHomotopy x x y z).compContinuousMap c2).symm)
  let H2' : Homotopy A1 A2 := H2.cast rfl rfl
  let H3 := (Homotopy.refl prefix1).comp
    (((pathTripleAssocHomotopy y x y z).compContinuousMap c3).symm)
  let H3' : Homotopy A2 ((loopBasepointChange q).comp (loopBasepointChange p)) :=
    H3.cast rfl rfl
  exact H1'.trans (H2'.trans H3')

private theorem originalLoopBasepointTransPointComputed {x y z : X}
    (p : Path x y) (q : Path y z) (t : I) (gamma : LoopSpace X x) :
    loopBasepointChangeTransHomotopy p q (t, gamma) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        pathTripleAssocHomotopy z y x z
          (⟨2 * (t : ℝ), (mul_pos_mem_iff zero_lt_two).2 ⟨unitInterval.nonneg t, ht⟩⟩,
            ((q.symm, p.symm), gamma.trans (p.trans q)))
      else
        let r : I := ⟨2 * (t : ℝ) - 1,
          two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩
        if hr : (r : ℝ) ≤ 1 / 2 then
          q.symm.trans (p.symm.trans (pathTripleAssocHomotopy x x y z
            (unitInterval.symm
              ⟨2 * (r : ℝ), (mul_pos_mem_iff zero_lt_two).2 ⟨unitInterval.nonneg r, hr⟩⟩,
                ((gamma, p), q))))
        else
          q.symm.trans (pathTripleAssocHomotopy y x y z
            (unitInterval.symm
              ⟨2 * (r : ℝ) - 1,
                two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hr).le, unitInterval.le_one r⟩⟩,
                ((p.symm, gamma.trans p), q))) := by
  let c1 : C(LoopSpace X x, (Path z y × Path y x) × Path x z) :=
    ⟨fun gamma => ((q.symm, p.symm), gamma.trans (p.trans q)), by fun_prop⟩
  let c2 : C(LoopSpace X x, (Path x x × Path x y) × Path y z) :=
    ⟨fun gamma => ((gamma, p), q), by fun_prop⟩
  let c3 : C(LoopSpace X x, (Path y x × Path x y) × Path y z) :=
    ⟨fun gamma => ((p.symm, gamma.trans p), q), by fun_prop⟩
  let prefix2 : C(Path x z, LoopSpace X z) :=
    ⟨fun r => q.symm.trans (p.symm.trans r), by fun_prop⟩
  let prefix1 : C(Path y z, LoopSpace X z) :=
    ⟨fun r => q.symm.trans r, by fun_prop⟩
  let A1 : C(LoopSpace X x, LoopSpace X z) :=
    ⟨fun gamma => q.symm.trans (p.symm.trans (gamma.trans (p.trans q))), by fun_prop⟩
  let A2 : C(LoopSpace X x, LoopSpace X z) :=
    ⟨fun gamma => q.symm.trans (p.symm.trans ((gamma.trans p).trans q)), by fun_prop⟩
  let H1 := (pathTripleAssocHomotopy z y x z).compContinuousMap c1
  have hsource : (pathTripleAssocLeft z y x z).comp c1 =
      loopBasepointChange (p.trans q) := by
    apply ContinuousMap.ext
    intro gamma
    change (q.symm.trans p.symm).trans (gamma.trans (p.trans q)) =
      (p.trans q).symm.trans (gamma.trans (p.trans q))
    rw [Path.trans_symm]
  let H1' : Homotopy (loopBasepointChange (p.trans q)) A1 := H1.cast hsource rfl
  let H2 := (Homotopy.refl prefix2).comp
    (((pathTripleAssocHomotopy x x y z).compContinuousMap c2).symm)
  let H2' : Homotopy A1 A2 := H2.cast rfl rfl
  let H3 := (Homotopy.refl prefix1).comp
    (((pathTripleAssocHomotopy y x y z).compContinuousMap c3).symm)
  let H3' : Homotopy A2 ((loopBasepointChange q).comp (loopBasepointChange p)) :=
    H3.cast rfl rfl
  have hValue : loopBasepointChangeTransHomotopy p q (t, gamma) =
      (H1'.trans (H2'.trans H3')) (t, gamma) := rfl
  refine hValue.trans ?_
  rw [Homotopy.trans_apply]
  split_ifs with ht
  · rfl
  · rw [Homotopy.trans_apply]
    dsimp only
    split_ifs with hr <;> rfl

/-- Conjugation along a point path and its inverse cancels by one
continuous family on the whole source loop space. -/
public def loopBasepointChangeCancelHomotopy {x y : X} (p : Path x y) :
    Homotopy ((loopBasepointChange p.symm).comp (loopBasepointChange p))
      (ContinuousMap.id (LoopSpace X x)) := by
  let H1 := (loopBasepointChangeTransHomotopy p p.symm).symm
  let H2 := loopBasepointChangePathHomotopy (Path.Homotopy.reflTransSymm p).symm
  exact H1.trans (H2.trans (loopBasepointChangeReflHomotopy x))

end Paths

section Mapping

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

private theorem originalPathTripleAssocMapComputed (f : C(X, Y))
    {a b c d : X} (p : Path a b) (q : Path b c) (r : Path c d) (t : I) :
    (pathTripleAssocHomotopy a b c d (t, ((p, q), r))).map f.continuous =
      pathTripleAssocHomotopy (f a) (f b) (f c) (f d)
        (t, ((p.map f.continuous, q.map f.continuous), r.map f.continuous)) := by
  apply Path.ext
  funext s
  change f (pathTripleAssocHomotopy a b c d (t, ((p, q), r)) s) =
    pathTripleAssocHomotopy (f a) (f b) (f c) (f d)
      (t, ((p.map f.continuous, q.map f.continuous), r.map f.continuous)) s
  rw [pathTripleAssocHomotopy_apply, pathTripleAssocHomotopy_apply]
  have h : (p.trans (q.trans r)).map f.continuous =
      (p.map f.continuous).trans ((q.map f.continuous).trans (r.map f.continuous)) := by
    rw [Path.map_trans, Path.map_trans]
  exact congrArg (fun gamma : Path (f a) (f d) => gamma (Set.Icc.convexComb
    (⟨Path.Homotopy.transAssocReparamAux s,
      Path.Homotopy.transAssocReparamAux_mem_I s⟩ : I) s t)) h

private theorem originalLoopBasepointTransMapComputed (f : C(X, Y))
    {x y z : X} (p : Path x y) (q : Path y z) (t : I) (gamma : LoopSpace X x) :
    (loopBasepointChangeTransHomotopy p q (t, gamma)).map f.continuous =
      loopBasepointChangeTransHomotopy (p.map f.continuous) (q.map f.continuous)
        (t, gamma.map f.continuous) := by
  rw [originalLoopBasepointTransPointComputed, originalLoopBasepointTransPointComputed]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · simp only [dite_eq_left ht]
    let s : I := ⟨2 * (t : ℝ), (mul_pos_mem_iff zero_lt_two).2 ⟨unitInterval.nonneg t, ht⟩⟩
    simpa only [Path.map_symm, Path.map_trans] using
      originalPathTripleAssocMapComputed f q.symm p.symm (gamma.trans (p.trans q)) s
  · let r : I := ⟨2 * (t : ℝ) - 1,
      two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, unitInterval.le_one t⟩⟩
    simp only [dite_eq_right ht]
    by_cases hr : 2 * (t : ℝ) - 1 ≤ 1 / 2
    · have hrTyped : (r : ℝ) ≤ 1 / 2 := hr
      simp only [dite_eq_left hr, ite_eq_left hr]
      let s : I := ⟨2 * (r : ℝ),
        (mul_pos_mem_iff zero_lt_two).2 ⟨unitInterval.nonneg r, hrTyped⟩⟩
      simp only [Path.map_trans, Path.map_symm]
      exact congrArg (fun a : Path (f x) (f z) =>
        (q.map f.continuous).symm.trans ((p.map f.continuous).symm.trans a))
          (originalPathTripleAssocMapComputed f gamma p q (unitInterval.symm s))
    · have hrTyped : ¬(r : ℝ) ≤ 1 / 2 := hr
      simp only [dite_eq_right hr, ite_eq_right hr]
      let s : I := ⟨2 * (r : ℝ) - 1,
        two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hrTyped).le, unitInterval.le_one r⟩⟩
      simp only [Path.map_trans, Path.map_symm]
      apply congrArg (fun a : Path (f y) (f z) => (q.map f.continuous).symm.trans a)
      simpa only [Path.map_symm, Path.map_trans] using
        originalPathTripleAssocMapComputed f p.symm (gamma.trans p) q (unitInterval.symm s)

/-- Every original time of the actual three-stage basepoint-reassociation
family commutes with mapping the original roots and whole input loop. -/
public theorem loopBasepointChangeTransHomotopy_map (f : C(X, Y))
    {x y z : X} (p : Path x y) (q : Path y z) (t : I) (gamma : LoopSpace X x) :
    (loopBasepointChangeTransHomotopy p q (t, gamma)).map f.continuous =
      loopBasepointChangeTransHomotopy (p.map f.continuous) (q.map f.continuous)
        (t, gamma.map f.continuous) :=
  originalLoopBasepointTransMapComputed f p q t gamma

/-- Strict mapping commutes with the actual conjugation formula along a
point path, with the same path mapped to the target space. -/
public theorem loopBasepointChangeMap_naturality (f : C(X, Y))
    {x y : X} (p : Path x y) :
    (strictLoopMap f y).comp (loopBasepointChange p) =
      (loopBasepointChange (p.map f.continuous)).comp (strictLoopMap f x) := by
  apply ContinuousMap.ext
  intro gamma
  change (p.symm.trans (gamma.trans p)).map f.continuous =
    (p.map f.continuous).symm.trans
      ((gamma.map f.continuous).trans (p.map f.continuous))
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm]

end Mapping

namespace WeaklyPointed

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- The weakly pointed identity has a genuine homotopy to the identity
continuous map of the whole source loop space. -/
public def loopMapIdHomotopy (x : X) :
    Homotopy ((id x).loopMap) (ContinuousMap.id (LoopSpace X x)) := by
  let H := (loopBasepointChangeReflHomotopy x).compContinuousMap
    (strictLoopMap (ContinuousMap.id X) x)
  have hsource : (loopBasepointChange (Path.refl x)).comp
      (strictLoopMap (ContinuousMap.id X) x) = (id x).loopMap :=
    (loopMap_eq_loopBasepointChange_comp_strictLoopMap (id x)).symm
  have htarget : (ContinuousMap.id (LoopSpace X x)).comp
      (strictLoopMap (ContinuousMap.id X) x) = ContinuousMap.id (LoopSpace X x) := by
    rw [strictLoopMap_id]
    rfl
  exact H.cast hsource htarget

/-- Weakly pointed composition is respected by one continuous homotopy
over time and all original source loops. -/
public def loopMapCompHomotopy (f : WeaklyPointed x y) (g : WeaklyPointed y z) :
    Homotopy ((comp f g).loopMap) (g.loopMap.comp f.loopMap) := by
  let p := f.rootPath.map g.hom.continuous
  let q := g.rootPath
  let H := (loopBasepointChangeTransHomotopy p q).compContinuousMap
    (strictLoopMap (g.hom.comp f.hom) x)
  have hsource : (loopBasepointChange (p.trans q)).comp
      (strictLoopMap (g.hom.comp f.hom) x) = (comp f g).loopMap :=
    (loopMap_eq_loopBasepointChange_comp_strictLoopMap (comp f g)).symm
  have htarget : ((loopBasepointChange q).comp (loopBasepointChange p)).comp
      (strictLoopMap (g.hom.comp f.hom) x) = g.loopMap.comp f.loopMap := by
    apply ContinuousMap.ext
    intro gamma
    change q.symm.trans
      ((p.symm.trans ((gamma.map (g.hom.comp f.hom).continuous).trans p)).trans q) =
      g.rootPath.symm.trans
        (((f.rootPath.symm.trans
          ((gamma.map f.hom.continuous).trans f.rootPath)).map g.hom.continuous).trans
            g.rootPath)
    rw [Path.map_trans, Path.map_trans, ← Path.map_symm]
    have hmap : gamma.map (g.hom.comp f.hom).continuous =
        (gamma.map f.hom.continuous).map g.hom.continuous := by
      apply Path.ext
      rfl
    rw [hmap]
  exact H.cast hsource htarget

private theorem originalLoopMapCompHomotopyValueComputed (f : WeaklyPointed x y)
    (g : WeaklyPointed y z) (t : I) (gamma : LoopSpace X x) :
    loopMapCompHomotopy f g (t, gamma) =
      loopBasepointChangeTransHomotopy
        (f.rootPath.map g.hom.continuous) g.rootPath
        (t, strictLoopMap (g.hom.comp f.hom) x gamma) := rfl

/-- Every original time and whole source loop of the actual composition
homotopy retains its SAME mapped first root, second root and strict
composite-map input, with the original direction and middle-family clocks. -/
public theorem loopMapCompHomotopy_apply (f : WeaklyPointed x y)
    (g : WeaklyPointed y z) (t : I) (gamma : LoopSpace X x) :
    loopMapCompHomotopy f g (t, gamma) =
      loopBasepointChangeTransHomotopy
        (f.rootPath.map g.hom.continuous) g.rootPath
        (t, strictLoopMap (g.hom.comp f.hom) x gamma) :=
  originalLoopMapCompHomotopyValueComputed f g t gamma

/-- Changing the chosen point path by its actual path homotopy gives a
homotopy of the complete weakly pointed loop maps. -/
public def loopMapRootPathHomotopy (f : C(X, Y))
    {p q : Path (f x) y} (H : p.Homotopy q) :
    Homotopy ((⟨f, p⟩ : WeaklyPointed x y).loopMap)
      ((⟨f, q⟩ : WeaklyPointed x y).loopMap) := by
  let K := (loopBasepointChangePathHomotopy H).compContinuousMap (strictLoopMap f x)
  exact K.cast
    (loopMap_eq_loopBasepointChange_comp_strictLoopMap
      (⟨f, p⟩ : WeaklyPointed x y)).symm
    (loopMap_eq_loopBasepointChange_comp_strictLoopMap
      (⟨f, q⟩ : WeaklyPointed x y)).symm

private theorem originalLoopMapRootPathHomotopyValueComputed (f : C(X, Y))
    {p q : Path (f x) y} (H : p.Homotopy q) (t : I) (gamma : LoopSpace X x) :
    loopMapRootPathHomotopy f H (t, gamma) =
      (H.eval t).symm.trans ((strictLoopMap f x gamma).trans (H.eval t)) := rfl

/-- Every time and whole input loop of the actual root-path homotopy
retain the original chosen root and strict mapped middle loop. -/
public theorem loopMapRootPathHomotopy_apply (f : C(X, Y))
    {p q : Path (f x) y} (H : p.Homotopy q) (t : I) (gamma : LoopSpace X x) :
    loopMapRootPathHomotopy f H (t, gamma) =
      (H.eval t).symm.trans ((strictLoopMap f x gamma).trans (H.eval t)) :=
  originalLoopMapRootPathHomotopyValueComputed f H t gamma

/-- A relative homotopy of the underlying maps and a compatible actual
point-path homotopy give one jointly continuous homotopy of all loop maps. -/
public def loopMapHomotopyOfRelativeMap (f g : WeaklyPointed x y)
    (H : ContinuousMap.HomotopyRel f.hom g.hom {x})
    (Hp : f.rootPath.Homotopy
      (g.rootPath.cast (H.fst_eq_snd (by simp)) rfl)) :
    Homotopy f.loopMap g.loopMap where
  toFun s := (Hp.eval s.1).symm.trans
    ((H.mappedLoopFamily s).trans (Hp.eval s.1))
  map_zero_left gamma := by
    rw [Path.Homotopy.eval_zero, HomotopyRel.mappedLoopFamily_zero]
    exact (loopMap_apply f gamma).symm
  map_one_left gamma := by
    rw [Path.Homotopy.eval_one, HomotopyRel.mappedLoopFamily_one, loopMap_apply]
    apply Path.ext
    rfl
  continuous_toFun := by
    let E : C(I, Path (f.hom x) y) :=
      ⟨Hp.eval, Path.continuous_uncurry_iff.mp Hp.continuous_toFun⟩
    have hRoot : Continuous
        (fun s : I × LoopSpace X x => Hp.eval s.1) := E.continuous.comp continuous_fst
    exact Continuous.path_trans (Path.continuous_symm.comp hRoot)
      (Continuous.path_trans (HomotopyRel.mappedLoopFamily H).continuous hRoot)

end WeaklyPointed

section ConstantLoop

variable {X : Type u} [TopologicalSpace X]

private theorem appendReflConstantComputed (x : X) (t : I) :
    pathAppendReflHomotopy x x (t, Path.refl x) = Path.refl x := by
  apply Path.ext
  funext s
  change pathReparamMapHomotopy (a := x) (b := x) appendReflReparam
    appendReflReparam_continuous appendReflReparam_zero appendReflReparam_one
      (t, Path.refl x) s = x
  rw [pathReparamMapHomotopy_apply]
  rfl

private theorem prependReflConstantComputed (x : X) (t : I) :
    pathPrependReflHomotopy x x (t, Path.refl x) = Path.refl x := by
  change (pathAppendReflHomotopy x x (t, (Path.refl x).symm)).symm = Path.refl x
  rw [Path.refl_symm, appendReflConstantComputed, Path.refl_symm]

private theorem loopReflConstantComputed (x : X) (t : I) :
    loopBasepointChangeReflHomotopy x (t, Path.refl x) = Path.refl x := by
  let A : C(Path x x, Path x x) := pathAppendRefl x x
  let J : C(Path x x, Path x x) := ContinuousMap.id (Path x x)
  have hA : A = J.comp A := by
    apply ContinuousMap.ext
    intro γ
    rfl
  let H0 : Homotopy ((pathPrependRefl x x).comp A) (J.comp A) :=
    (pathPrependReflHomotopy x x).compContinuousMap A
  let H1 : Homotopy (J.comp A) J := (pathAppendReflHomotopy x x).cast hA rfl
  have hValue : loopBasepointChangeReflHomotopy x (t, Path.refl x) =
      (H0.trans H1) (t, Path.refl x) := by
    rfl
  refine hValue.trans ?_
  rw [Homotopy.trans_apply]
  split_ifs with h
  · change pathPrependReflHomotopy x x
      (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩,
        (Path.refl x).trans (Path.refl x)) = Path.refl x
    rw [Path.refl_trans_refl]
    exact prependReflConstantComputed x _
  · change pathAppendReflHomotopy x x
      (⟨2 * (t : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩,
        Path.refl x) = Path.refl x
    exact appendReflConstantComputed x _

/-- The chosen reflexive-conjugation unit homotopy fixes the original
constant loop at every time. Its data and interval reparameterizations are unchanged. -/
public theorem loopBasepointChangeReflHomotopy_refl (x : X) (t : I) :
    loopBasepointChangeReflHomotopy x (t, Path.refl x) = Path.refl x :=
  loopReflConstantComputed x t

end ConstantLoop

end ContinuousMap

end

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe uUnitValue

namespace ContinuousMap

variable {X : Type uUnitValue} [TopologicalSpace X]

/-- The SAME complete append-reflexive homotopy fixes the ORIGINAL
constant loop at every actual homotopy time. -/
public theorem pathAppendReflHomotopy_refl (x : X) (t : I) :
    pathAppendReflHomotopy x x (t, Path.refl x) = Path.refl x :=
  appendReflConstantComputed x t

/-- The SAME complete prepend-reflexive homotopy fixes the ORIGINAL
constant loop at every actual homotopy time. -/
public theorem pathPrependReflHomotopy_refl (x : X) (t : I) :
    pathPrependReflHomotopy x x (t, Path.refl x) = Path.refl x :=
  prependReflConstantComputed x t

end ContinuousMap

end


noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe uLoopIdUnitValue

namespace ContinuousMap.WeaklyPointed

variable {X : Type uLoopIdUnitValue} [TopologicalSpace X]

private theorem originalLoopMapIdHomotopyReflComputed (x : X) (t : I) :
    loopMapIdHomotopy x (t, Path.refl x) = Path.refl x := by
  let H := (ContinuousMap.loopBasepointChangeReflHomotopy x).compContinuousMap
    (ContinuousMap.strictLoopMap (ContinuousMap.id X) x)
  have hValue : loopMapIdHomotopy x (t, Path.refl x) = H (t, Path.refl x) := rfl
  have hMapped : ContinuousMap.strictLoopMap (ContinuousMap.id X) x (Path.refl x) =
      Path.refl x := ContinuousMap.strictLoopMap_refl (ContinuousMap.id X) x
  exact hValue.trans
    ((congrArg (fun gamma : LoopSpace X x =>
      ContinuousMap.loopBasepointChangeReflHomotopy x (t, gamma)) hMapped).trans
        (ContinuousMap.loopBasepointChangeReflHomotopy_refl x t))

/-- The SAME entire weakly pointed identity homotopy fixes the ORIGINAL
constant loop at EVERY actual homotopy time, with its original clock. -/
public theorem loopMapIdHomotopy_refl (x : X) (t : I) :
    loopMapIdHomotopy x (t, Path.refl x) = Path.refl x :=
  originalLoopMapIdHomotopyReflComputed x t

end ContinuousMap.WeaklyPointed

end

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe uOriginalPrependMap vOriginalPrependMap

namespace ContinuousMap

variable {X : Type uOriginalPrependMap} {Y : Type vOriginalPrependMap}
  [TopologicalSpace X] [TopologicalSpace Y]

private theorem originalPathPrependReflHomotopyMapComputed (f : C(X, Y))
    {a b : X} (r : Path a b) (t : I) :
    (pathPrependReflHomotopy a b (t, r)).map f.continuous =
      pathPrependReflHomotopy (f a) (f b) (t, r.map f.continuous) := by
  have hAppend {c d : X} (p : Path c d) :
      (pathAppendReflHomotopy c d (t, p)).map f.continuous =
        pathAppendReflHomotopy (f c) (f d) (t, p.map f.continuous) := by
    apply Path.ext
    funext s
    have hSource : pathAppendReflHomotopy c d (t, p) s =
        p (Set.Icc.convexComb (appendReflReparam s) s t) :=
      pathReparamMapHomotopy_apply appendReflReparam appendReflReparam_continuous
        appendReflReparam_zero appendReflReparam_one p t s
    have hTarget : pathAppendReflHomotopy (f c) (f d) (t, p.map f.continuous) s =
        (p.map f.continuous) (Set.Icc.convexComb (appendReflReparam s) s t) :=
      pathReparamMapHomotopy_apply appendReflReparam appendReflReparam_continuous
        appendReflReparam_zero appendReflReparam_one (p.map f.continuous) t s
    exact (congrArg f hSource).trans hTarget.symm
  have hSource : pathPrependReflHomotopy a b (t, r) =
      (pathAppendReflHomotopy b a (t, r.symm)).symm := rfl
  have hTarget : pathPrependReflHomotopy (f a) (f b) (t, r.map f.continuous) =
      (pathAppendReflHomotopy (f b) (f a) (t, (r.map f.continuous).symm)).symm := rfl
  calc
    (pathPrependReflHomotopy a b (t, r)).map f.continuous =
        (pathAppendReflHomotopy b a (t, r.symm)).symm.map f.continuous :=
      congrArg (fun p : Path a b => p.map f.continuous) hSource
    _ = ((pathAppendReflHomotopy b a (t, r.symm)).map f.continuous).symm :=
      (Path.map_symm (pathAppendReflHomotopy b a (t, r.symm)) f.continuous).symm
    _ = (pathAppendReflHomotopy (f b) (f a) (t, r.symm.map f.continuous)).symm :=
      congrArg (fun p : Path (f b) (f a) => p.symm) (hAppend r.symm)
    _ = (pathAppendReflHomotopy (f b) (f a) (t, (r.map f.continuous).symm)).symm :=
      congrArg (fun p : Path (f b) (f a) =>
        (pathAppendReflHomotopy (f b) (f a) (t, p)).symm) (Path.map_symm r f.continuous).symm
    _ = pathPrependReflHomotopy (f a) (f b) (t, r.map f.continuous) := hTarget.symm

/-- The SAME complete original prepend-reflexive family commutes with
mapping EVERY original path, at EVERY actual time and with unchanged clocks. -/
public theorem pathPrependReflHomotopy_map (f : C(X, Y))
    {a b : X} (r : Path a b) (t : I) :
    (pathPrependReflHomotopy a b (t, r)).map f.continuous =
      pathPrependReflHomotopy (f a) (f b) (t, r.map f.continuous) :=
  originalPathPrependReflHomotopyMapComputed f r t

end ContinuousMap

end

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

universe uOriginalCancelValue

namespace ContinuousMap

variable {X : Type uOriginalCancelValue} [TopologicalSpace X]

private theorem originalLoopBasepointChangeCancelValueComputed
    {x y : X} (p : Path x y) (t : I) (gamma : LoopSpace X x) :
    let H1 := (loopBasepointChangeTransHomotopy p p.symm).symm;
    let H2 := loopBasepointChangePathHomotopy (Path.Homotopy.reflTransSymm p).symm;
    let H3 := loopBasepointChangeReflHomotopy x;
    loopBasepointChangeCancelHomotopy p (t, gamma) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        H1 (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, gamma)
      else
        let r : I := ⟨2 * (t : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩;
        if hr : (r : ℝ) ≤ 1 / 2 then
          H2 (⟨2 * (r : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨r.2.1, hr⟩⟩, gamma)
        else
          H3 (⟨2 * (r : ℝ) - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hr).le, r.2.2⟩⟩, gamma) := by
  let H1 := (loopBasepointChangeTransHomotopy p p.symm).symm
  let H2 := loopBasepointChangePathHomotopy (Path.Homotopy.reflTransSymm p).symm
  let H3 := loopBasepointChangeReflHomotopy x
  have hValue : loopBasepointChangeCancelHomotopy p (t, gamma) =
      (H1.trans (H2.trans H3)) (t, gamma) := rfl
  refine hValue.trans ?_
  rw [Homotopy.trans_apply]
  split_ifs with ht
  · rfl
  · rw [Homotopy.trans_apply]

/-- Every whole source loop and original time of SAME cancellation
homotopy retains its original three stages and nested canonical half clocks. -/
public theorem loopBasepointChangeCancelHomotopy_apply
    {x y : X} (p : Path x y) (t : I) (gamma : LoopSpace X x) :
    let H1 := (loopBasepointChangeTransHomotopy p p.symm).symm;
    let H2 := loopBasepointChangePathHomotopy (Path.Homotopy.reflTransSymm p).symm;
    let H3 := loopBasepointChangeReflHomotopy x;
    loopBasepointChangeCancelHomotopy p (t, gamma) =
      if ht : (t : ℝ) ≤ 1 / 2 then
        H1 (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩, gamma)
      else
        let r : I := ⟨2 * (t : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩;
        if hr : (r : ℝ) ≤ 1 / 2 then
          H2 (⟨2 * (r : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨r.2.1, hr⟩⟩, gamma)
        else
          H3 (⟨2 * (r : ℝ) - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hr).le, r.2.2⟩⟩, gamma) :=
  originalLoopBasepointChangeCancelValueComputed p t gamma

end ContinuousMap

end
