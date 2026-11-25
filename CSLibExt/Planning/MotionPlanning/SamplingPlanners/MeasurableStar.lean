/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.SamplingPlanners.MeasurableStarTable
public import Mathlib.Data.Rat.Encodable

@[expose] public section

/-! # RRT* measurability

The RRT* output (vertices, edges and cost table) is a measurable function
of the sample list, and RRT* skips samples that are not collision free.

Model: planners are deterministic functions of an explicit finite sample
list; the lift reads the first `N` raw samples of a stream with the
product law, applying the existing collision filter. Configuration space
has measurable diagonal; oracles are jointly measurable; discrete types
use discrete σ-algebras; lists use the length-stratified σ-algebra.
Completeness, optimality and path extraction are out of scope. -/

open MeasureTheory

namespace Cslib.Planning.MotionPlanning.SamplingPlanners

/-- Measurable set where a `Bool`-valued measurable function is true. -/
private theorem measurableSet_eq_true {α : Type} [MeasurableSpace α]
    {f : α → Bool} (hf : Measurable f) : MeasurableSet {a | f a = true} := by
  have h := hf (measurableSet_singleton true)
  have heq : f ⁻¹' {true} = {a | f a = true} := by
    ext a
    simp
  rw [heq] at h
  exact h

/-- Measurable set from a measurable `decide`. -/
private theorem measurableSet_of_measurable_decide {α : Type}
    [MeasurableSpace α] {p : α → Prop} [DecidablePred p]
    (h : Measurable (fun a => decide (p a))) : MeasurableSet {a | p a} := by
  have hpre := h (measurableSet_singleton true)
  have heq : (fun a => decide (p a)) ⁻¹' {true} = {a | p a} := by
    ext a
    simp
  rw [heq] at hpre
  exact hpre

/-- A non-free sample leaves the RRT* one-step state unchanged. -/
private theorem extendStar_of_free_false {S : Type} [DecidableEq S]
    (O : Oracles S) (verts : List S) (edges : List (S × S))
    (costs : List (S × (Int × Nat))) (radiusOf : ℕ → ℚ) (start s : S)
    (h : O.free s = false) :
    extendStar O verts edges costs radiusOf start s = (verts, edges, costs) := by
  unfold extendStar
  simp [h]

/-- Filtering non-free samples does not change the RRT* auxiliary run. -/
private theorem rrtStarAux_filter_free {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (samples : List S) (verts : List S)
    (edges : List (S × S)) (costs : List (S × (Int × Nat))) :
    rrtStarAux O radiusOf start verts edges costs (samples.filter O.free) =
      rrtStarAux O radiusOf start verts edges costs samples := by
  induction samples generalizing verts edges costs with
  | nil => simp [rrtStarAux]
  | cons s ss ih =>
      by_cases hb : O.free s = true
      · simp [hb, rrtStarAux, ih]
      · have hbf : O.free s = false := by
          cases h : O.free s <;> simp_all
        simp [hb, rrtStarAux]
        have he := extendStar_of_free_false O verts edges costs radiusOf
          start s hbf
        simp [he]
        exact ih _ _ _

/-- One step of the nearest-vertex fold, as a function of sample and vertices. -/
private def nearestStep {S : Type} (O : Oracles S) (q : S × S × S) : S :=
  if O.cost q.2.2 q.1 < O.cost q.2.1 q.1 then q.2.2 else q.2.1

/-- Single-step update of the nearest-vertex fold is measurable. -/
private theorem measurable_nearest_step {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) : Measurable (nearestStep O) := by
  have hw : Measurable (fun q : S × S × S => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hb : Measurable (fun q : S × S × S => q.2.1) :=
    measurable_fst.comp measurable_snd
  have hs : Measurable (fun q : S × S × S => q.1) := measurable_fst
  have hc1 : Measurable (fun q : S × S × S => O.cost q.2.2 q.1) :=
    hO.cost.comp (hw.prodMk hs)
  have hc2 : Measurable (fun q : S × S × S => O.cost q.2.1 q.1) :=
    hO.cost.comp (hb.prodMk hs)
  have hlt : Measurable (fun r : ℚ × ℚ => decide (r.1 < r.2)) :=
    measurable_of_countable _
  have hdec : Measurable (fun q : S × S × S =>
      decide (O.cost q.2.2 q.1 < O.cost q.2.1 q.1)) :=
    hlt.comp (hc1.prodMk hc2)
  have hset : MeasurableSet
      {q : S × S × S | O.cost q.2.2 q.1 < O.cost q.2.1 q.1} :=
    measurableSet_of_measurable_decide hdec
  have hite : Measurable (fun q : S × S × S =>
      if O.cost q.2.2 q.1 < O.cost q.2.1 q.1 then q.2.2 else q.2.1) :=
    Measurable.ite hset hw hb
  have heq : (fun q : S × S × S =>
      if O.cost q.2.2 q.1 < O.cost q.2.1 q.1 then q.2.2 else q.2.1)
      = nearestStep O := by
    rfl
  rw [heq] at hite
  exact hite

/-- Nearest vertex selector is measurable in vertices, default and sample. -/
private theorem measurable_nearest {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) :
    Measurable (fun p : List S × S × S => nearest O p.1 p.2.1 p.2.2) := by
  have hg := measurable_nearest_step (S := S) hO
  have hfold := measurable_list_foldl (g := nearestStep O) hg
  have hnil : Measurable (fun d : S × S => d.1) := measurable_fst
  have hcons : Measurable (fun p : (S × S) × S × List S × S =>
      p.2.2.1.foldl (fun b a => nearestStep O (p.1.2, b, a)) p.2.1) := by
    have hs : Measurable (fun p : (S × S) × S × List S × S => p.1.2) :=
      measurable_snd.comp measurable_fst
    have hi : Measurable (fun p : (S × S) × S × List S × S => p.2.1) :=
      measurable_fst.comp measurable_snd
    have hl : Measurable (fun p : (S × S) × S × List S × S => p.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have htri : Measurable (fun p : (S × S) × S × List S × S =>
        (p.1.2, p.2.1, p.2.2.1)) :=
      hs.prodMk (hi.prodMk hl)
    have hcomp := hfold.comp htri
    have heqCons : (fun p : (S × S) × S × List S × S =>
        p.2.2.1.foldl (fun b a => nearestStep O (p.1.2, b, a)) p.2.1) =
        (fun p : S × S × List S => p.2.2.foldl
          (fun b a => nearestStep O (p.1, b, a)) p.2.1) ∘
          (fun p : (S × S) × S × List S × S =>
            (p.1.2, p.2.1, p.2.2.1)) := by
      funext p
      simp
    rw [heqCons]
    exact hcomp
  have hrec := measurable_list_rec (α := S) (β := S) (δ := S × S)
    (nil := fun d : S × S => d.1)
    (cons := fun p : (S × S) × S × List S × S =>
      p.2.2.1.foldl (fun b a => nearestStep O (p.1.2, b, a)) p.2.1)
    hnil hcons
  have heq : (fun p : (S × S) × List S => nearest O p.2 p.1.1 p.1.2) =
      (fun p : (S × S) × List S => List.rec (motive := fun _ => S) (p.1.1)
        (fun a l _ => l.foldl (fun b a' => nearestStep O (p.1.2, b, a')) a)
        p.2) := by
    funext p
    cases hverts : p.2 with
    | nil =>
        simp [nearest]
    | cons a l =>
        simp [nearest, nearestStep]
  have hnear : Measurable
      (fun p : (S × S) × List S => nearest O p.2 p.1.1 p.1.2) := by
    rw [heq]
    exact hrec
  have hreo : Measurable (fun p : List S × S × S =>
      ((p.2.1, p.2.2), p.1)) := by
    have h1 : Measurable (fun p : List S × S × S => p.2.1) :=
      measurable_fst.comp measurable_snd
    have h2 : Measurable (fun p : List S × S × S => p.2.2) :=
      measurable_snd.comp measurable_snd
    have h3 : Measurable (fun p : List S × S × S => p.1) := measurable_fst
    exact (h1.prodMk h2).prodMk h3
  have heq2 : (fun p : List S × S × S => nearest O p.1 p.2.1 p.2.2) =
      (fun p : (S × S) × List S => nearest O p.2 p.1.1 p.1.2) ∘
        (fun p : List S × S × S => ((p.2.1, p.2.2), p.1)) := by
    rfl
  rw [heq2]
  exact hnear.comp hreo

/-- Filter test for RRT* candidate vertices. -/
private def candidatesTest {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (p : (List S × S × S) × S) : Bool :=
  O.link p.2 p.1.2.2 &&
    (decide (O.cost p.2 p.1.2.2 ≤ radiusOf p.1.1.length) ||
      decide (p.2 = p.1.2.1))

/-- Candidate filter test is measurable. -/
private theorem measurable_candidatesTest {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) :
    Measurable (candidatesTest O radiusOf) := by
  have hv : Measurable
      (fun p : (List S × S × S) × S => p.2) := measurable_snd
  have hs : Measurable
      (fun p : (List S × S × S) × S => p.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hn : Measurable
      (fun p : (List S × S × S) × S => p.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hlink : Measurable
      (fun p : (List S × S × S) × S => O.link p.2 p.1.2.2) :=
    hO.link.comp (hv.prodMk hs)
  have hcost : Measurable
      (fun p : (List S × S × S) × S => O.cost p.2 p.1.2.2) :=
    hO.cost.comp (hv.prodMk hs)
  have hlen : Measurable
      (fun p : (List S × S × S) × S => p.1.1.length) := by
    have hproj : Measurable
        (fun p : (List S × S × S) × S => p.1.1) :=
      measurable_fst.comp measurable_fst
    exact measurable_list_length.comp hproj
  have hrad : Measurable
      (fun p : (List S × S × S) × S => radiusOf p.1.1.length) :=
    (measurable_of_countable radiusOf).comp hlen
  have hleM : Measurable (fun r : ℚ × ℚ => decide (r.1 ≤ r.2)) :=
    measurable_of_countable _
  have hle : Measurable (fun p : (List S × S × S) × S =>
      decide (O.cost p.2 p.1.2.2 ≤ radiusOf p.1.1.length)) :=
    hleM.comp (hcost.prodMk hrad)
  have heq : Measurable (fun p : (List S × S × S) × S =>
      decide (p.2 = p.1.2.1)) :=
    measurable_decide_eq.comp (hv.prodMk hn)
  have horM : Measurable (fun b : Bool × Bool => b.1 || b.2) :=
    measurable_of_countable _
  have hor : Measurable (fun p : (List S × S × S) × S =>
      (decide (O.cost p.2 p.1.2.2 ≤ radiusOf p.1.1.length) ||
        decide (p.2 = p.1.2.1))) :=
    horM.comp (hle.prodMk heq)
  have handM : Measurable (fun b : Bool × Bool => b.1 && b.2) :=
    measurable_of_countable _
  have hand : Measurable (fun p : (List S × S × S) × S =>
      O.link p.2 p.1.2.2 &&
        (decide (O.cost p.2 p.1.2.2 ≤ radiusOf p.1.1.length) ||
          decide (p.2 = p.1.2.1))) :=
    handM.comp (hlink.prodMk hor)
  have heqDef : (fun p : (List S × S × S) × S =>
      O.link p.2 p.1.2.2 &&
        (decide (O.cost p.2 p.1.2.2 ≤ radiusOf p.1.1.length) ||
          decide (p.2 = p.1.2.1))) = candidatesTest O radiusOf := by
    rfl
  rw [heqDef] at hand
  exact hand

/-- RRT* candidate list is measurable in vertices, near and sample. -/
private theorem measurable_candidates {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) :
    Measurable (fun p : List S × S × S =>
      candidates O p.1 radiusOf p.2.1 p.2.2) := by
  have hq := measurable_candidatesTest (S := S) hO radiusOf
  have hfilter := measurable_list_filter
    (q := candidatesTest O radiusOf) hq
  have hdup : Measurable (fun p : List S × S × S =>
      ((p.1, p.2.1, p.2.2), p.1)) := by
    have h1 : Measurable (fun p : List S × S × S => p.1) := measurable_fst
    have h2 : Measurable (fun p : List S × S × S => p.2.1) :=
      measurable_fst.comp measurable_snd
    have h3 : Measurable (fun p : List S × S × S => p.2.2) :=
      measurable_snd.comp measurable_snd
    have h123 : Measurable (fun p : List S × S × S =>
        (p.1, p.2.1, p.2.2)) :=
      h1.prodMk (h2.prodMk h3)
    exact h123.prodMk h1
  have hcomp := hfilter.comp hdup
  have heq : (fun p : List S × S × S =>
      candidates O p.1 radiusOf p.2.1 p.2.2) =
      (fun p : (List S × S × S) × List S => p.2.filter
        (fun v => candidatesTest O radiusOf (p.1, v))) ∘
        (fun p : List S × S × S => ((p.1, p.2.1, p.2.2), p.1)) := by
    funext p
    simp [candidates, candidatesTest]
  rw [heq]
  exact hcomp

/-- Pair-plus-rational cost addition is measurable on discrete types. -/
private theorem measurable_ccAdd :
    Measurable (fun p : (Int × Nat) × ℚ => ccAdd p.1 p.2) :=
  measurable_of_countable _

/-- Cost-pair comparison is measurable on discrete types. -/
private theorem measurable_ccLt_decide :
    Measurable
      (fun p : (Int × Nat) × (Int × Nat) => decide (ccLt p.1 p.2)) :=
  measurable_of_countable _

/-- One step of the parent-selection fold. -/
private def parentStep {S : Type} [DecidableEq S] (O : Oracles S)
    (q : (List (S × (Int × Nat)) × S) × S × S) : S :=
  let costs := q.1.1
  let s := q.1.2
  let best := q.2.1
  let v := q.2.2
  if ccLt (ccAdd (costToCome costs v) (O.cost v s))
    (ccAdd (costToCome costs best) (O.cost best s)) then v else best

/-- Parent-selection fold step is measurable. -/
private theorem measurable_parentStep {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) : Measurable (parentStep O) := by
  have hcosts : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hs : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S => q.1.2) :=
    measurable_snd.comp measurable_fst
  have hb : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S => q.2.1) :=
    measurable_fst.comp measurable_snd
  have hv : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hctcV : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S =>
        costToCome q.1.1 q.2.2) :=
    measurable_costToCome.comp (hcosts.prodMk hv)
  have hctcB : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S =>
        costToCome q.1.1 q.2.1) :=
    measurable_costToCome.comp (hcosts.prodMk hb)
  have hcostV : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S =>
        O.cost q.2.2 q.1.2) :=
    hO.cost.comp (hv.prodMk hs)
  have hcostB : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S =>
        O.cost q.2.1 q.1.2) :=
    hO.cost.comp (hb.prodMk hs)
  have haddV : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S =>
        ccAdd (costToCome q.1.1 q.2.2) (O.cost q.2.2 q.1.2)) :=
    measurable_ccAdd.comp (hctcV.prodMk hcostV)
  have haddB : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S =>
        ccAdd (costToCome q.1.1 q.2.1) (O.cost q.2.1 q.1.2)) :=
    measurable_ccAdd.comp (hctcB.prodMk hcostB)
  have hdec : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S => decide (ccLt
        (ccAdd (costToCome q.1.1 q.2.2) (O.cost q.2.2 q.1.2))
        (ccAdd (costToCome q.1.1 q.2.1) (O.cost q.2.1 q.1.2)))) :=
    measurable_ccLt_decide.comp (haddV.prodMk haddB)
  have hset : MeasurableSet {q : (List (S × (Int × Nat)) × S) × S × S |
      ccLt (ccAdd (costToCome q.1.1 q.2.2) (O.cost q.2.2 q.1.2))
        (ccAdd (costToCome q.1.1 q.2.1) (O.cost q.2.1 q.1.2))} :=
    measurableSet_of_measurable_decide hdec
  have hite : Measurable
      (fun q : (List (S × (Int × Nat)) × S) × S × S =>
        if ccLt (ccAdd (costToCome q.1.1 q.2.2) (O.cost q.2.2 q.1.2))
          (ccAdd (costToCome q.1.1 q.2.1) (O.cost q.2.1 q.1.2))
        then q.2.2 else q.2.1) :=
    Measurable.ite hset hv hb
  have heqDef : (fun q : (List (S × (Int × Nat)) × S) × S × S =>
      if ccLt (ccAdd (costToCome q.1.1 q.2.2) (O.cost q.2.2 q.1.2))
        (ccAdd (costToCome q.1.1 q.2.1) (O.cost q.2.1 q.1.2))
      then q.2.2 else q.2.1) = parentStep O := by
    funext q
    simp [parentStep]
  rw [heqDef] at hite
  exact hite

/-- Parent value with default for empty candidates. -/
private def parentVal {S : Type} [DecidableEq S] (O : Oracles S)
    (verts : List S) (costs : List (S × (Int × Nat))) (radiusOf : ℕ → ℚ)
    (near s : S) : S :=
  match candidates O verts radiusOf near s with
  | [] => near
  | h :: t =>
      (h :: t).foldl (fun best v =>
        if ccLt (ccAdd (costToCome costs v) (O.cost v s))
          (ccAdd (costToCome costs best) (O.cost best s)) then v
        else best) (if near ∈ h :: t then near else h)

/-- Parent value agrees with `chooseParent` on nonempty candidates. -/
private theorem chooseParent_eq_parentVal {S : Type} [DecidableEq S]
    (O : Oracles S) (verts : List S) (costs : List (S × Int × Nat))
    (radiusOf : ℕ → ℚ) (near s : S) (h : S) (l : List S)
    (hc : candidates O verts radiusOf near s = h :: l) :
    chooseParent O verts costs radiusOf near s =
      some (parentVal O verts costs radiusOf near s) := by
  unfold chooseParent parentVal
  simp [hc]

/-- Parent-value list-recursion step is measurable. -/
private theorem measurable_parentCons {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) :
    Measurable (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S =>
      let h := p.2.1
      let t := p.2.2.1
      let costs := p.1.1
      let near := p.1.2.1
      let s := p.1.2.2
      (h :: t).foldl
        (fun b v => parentStep O ((costs, s), b, v))
        (if near ∈ h :: t then near else h)) := by
  have hg := measurable_parentStep (S := S) hO
  have hfold := measurable_list_foldl (g := parentStep O) hg
  have hcosts : Measurable (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S => p.1.1) :=
    measurable_fst.comp measurable_fst
  have hnear : Measurable (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S => p.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hs : Measurable (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S => p.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hh : Measurable (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S => p.2.1) :=
    measurable_fst.comp measurable_snd
  have ht : Measurable (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hlist : Measurable (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S =>
      p.2.1 :: p.2.2.1) :=
    measurable_list_cons.comp (hh.prodMk ht)
  have hmemDec : Measurable (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S =>
      decide (p.1.2.1 ∈ p.2.1 :: p.2.2.1)) :=
    measurable_list_mem.comp (hnear.prodMk hlist)
  have hmemSet : MeasurableSet {p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S |
      p.1.2.1 ∈ p.2.1 :: p.2.2.1} :=
    measurableSet_of_measurable_decide hmemDec
  have hinit : Measurable (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S =>
      if p.1.2.1 ∈ p.2.1 :: p.2.2.1 then p.1.2.1 else p.2.1) :=
    Measurable.ite hmemSet hnear hh
  have hparams : Measurable (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S =>
      (p.1.1, p.1.2.2)) :=
    hcosts.prodMk hs
  have htri : Measurable (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S =>
      ((p.1.1, p.1.2.2),
        (if p.1.2.1 ∈ p.2.1 :: p.2.2.1 then p.1.2.1 else p.2.1),
        p.2.1 :: p.2.2.1)) :=
    hparams.prodMk (hinit.prodMk hlist)
  have hcomp := hfold.comp htri
  have heq : (fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S =>
      let h := p.2.1
      let t := p.2.2.1
      let costs := p.1.1
      let near := p.1.2.1
      let s := p.1.2.2
      (h :: t).foldl
        (fun b v => parentStep O ((costs, s), b, v))
        (if near ∈ h :: t then near else h)) =
      (fun q : (List (S × (Int × Nat)) × S) × S × List S =>
        q.2.2.foldl (fun b v => parentStep O (q.1, b, v)) q.2.1) ∘
        (fun p :
          (List (S × (Int × Nat)) × S × S) × S × List S × S =>
          ((p.1.1, p.1.2.2),
            (if p.1.2.1 ∈ p.2.1 :: p.2.2.1 then p.1.2.1 else p.2.1),
            p.2.1 :: p.2.2.1)) := by
    funext p
    simp
  rw [heq]
  exact hcomp

/-- Parent value is measurable in vertices, costs, near and sample. -/
private theorem measurable_parentVal {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) :
    Measurable (fun p : List S × List (S × (Int × Nat)) × S × S =>
      parentVal O p.1 p.2.1 radiusOf p.2.2.1 p.2.2.2) := by
  have hnil : Measurable
      (fun d : List (S × (Int × Nat)) × S × S => d.2.1) :=
    measurable_fst.comp measurable_snd
  have hcons := measurable_parentCons (S := S) hO
  have hrec := measurable_list_rec
    (α := S) (β := S) (δ := List (S × (Int × Nat)) × S × S)
    (nil := fun d : List (S × (Int × Nat)) × S × S => d.2.1)
    (cons := fun p :
      (List (S × (Int × Nat)) × S × S) × S × List S × S =>
      let h := p.2.1
      let t := p.2.2.1
      let costs := p.1.1
      let near := p.1.2.1
      let s := p.1.2.2
      (h :: t).foldl
        (fun b v => parentStep O ((costs, s), b, v))
        (if near ∈ h :: t then near else h))
    hnil hcons
  have hcands : Measurable
      (fun p : List S × List (S × (Int × Nat)) × S × S =>
        candidates O p.1 radiusOf p.2.2.1 p.2.2.2) := by
    have hcan := measurable_candidates (S := S) hO radiusOf
    have hproj : Measurable
        (fun p : List S × List (S × (Int × Nat)) × S × S =>
          (p.1, p.2.2.1, p.2.2.2)) := by
      have h1 : Measurable
          (fun p : List S × List (S × (Int × Nat)) × S × S => p.1) :=
        measurable_fst
      have h2 : Measurable
          (fun p : List S × List (S × (Int × Nat)) × S × S => p.2.2.1) :=
        measurable_fst.comp (measurable_snd.comp measurable_snd)
      have h3 : Measurable
          (fun p : List S × List (S × (Int × Nat)) × S × S => p.2.2.2) :=
        measurable_snd.comp (measurable_snd.comp measurable_snd)
      exact h1.prodMk (h2.prodMk h3)
    have hcomp0 := hcan.comp hproj
    have heq0 : (fun p : List S × List (S × (Int × Nat)) × S × S =>
        candidates O p.1 radiusOf p.2.2.1 p.2.2.2) =
        (fun q : List S × S × S =>
          candidates O q.1 radiusOf q.2.1 q.2.2) ∘
          (fun p : List S × List (S × (Int × Nat)) × S × S =>
            (p.1, p.2.2.1, p.2.2.2)) := by
      rfl
    rw [heq0]
    exact hcomp0
  have htri : Measurable
      (fun p : List S × List (S × (Int × Nat)) × S × S =>
        ((p.2.1, p.2.2.1, p.2.2.2),
          candidates O p.1 radiusOf p.2.2.1 p.2.2.2)) := by
    have hcosts : Measurable
        (fun p : List S × List (S × (Int × Nat)) × S × S => p.2.1) :=
      measurable_fst.comp measurable_snd
    have hnear : Measurable
        (fun p : List S × List (S × (Int × Nat)) × S × S => p.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have hs : Measurable
        (fun p : List S × List (S × (Int × Nat)) × S × S => p.2.2.2) :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    have hd : Measurable
        (fun p : List S × List (S × (Int × Nat)) × S × S =>
          (p.2.1, p.2.2.1, p.2.2.2)) :=
      hcosts.prodMk (hnear.prodMk hs)
    exact hd.prodMk hcands
  have hcomp := hrec.comp htri
  have heq : (fun p : List S × List (S × (Int × Nat)) × S × S =>
      parentVal O p.1 p.2.1 radiusOf p.2.2.1 p.2.2.2) =
      (fun p : (List (S × (Int × Nat)) × S × S) × List S =>
        List.rec (motive := fun _ => S) (p.1.2.1)
          (fun a l _ =>
            let h := a
            let t := l
            let costs := p.1.1
            let near := p.1.2.1
            let s := p.1.2.2
            (h :: t).foldl
              (fun b v => parentStep O ((costs, s), b, v))
              (if near ∈ h :: t then near else h)) p.2) ∘
        (fun p : List S × List (S × (Int × Nat)) × S × S =>
          ((p.2.1, p.2.2.1, p.2.2.2),
            candidates O p.1 radiusOf p.2.2.1 p.2.2.2)) := by
    funext p
    simp only [Function.comp_apply]
    simp only [parentVal]
    cases hc : candidates O p.1 radiusOf p.2.2.1 p.2.2.2 with
    | nil =>
        simp
    | cons h t =>
        simp [parentStep]
  rw [heq]
  exact hcomp

/-- Parent chain with varying fuel is jointly measurable. -/
private theorem measurable_parentChain_varying {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun p : (List (S × S) × S × S) × ℕ =>
      parentChain p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  apply measurable_from_prod_countable_left
  intro k
  exact measurable_parentChain k

/-- Shifted costs with varying fuel are jointly measurable. -/
private theorem measurable_shift_varying {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable
      (fun p : (List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat))) ×
          ℕ =>
        shiftCostsPair p.1.1 p.1.2.1 p.1.2.2.1 p.2 p.1.2.2.2.1
          p.1.2.2.2.2) := by
  apply measurable_from_prod_countable_left
  intro k
  exact measurable_shiftCostsPair k

/-- Cost-pair addition is measurable on discrete types. -/
private theorem measurable_ccAddPair :
    Measurable
      (fun p : (Int × Nat) × (Int × Nat) => ccAddPair p.1 p.2) :=
  measurable_of_countable _

/-- Cost-pair delta is measurable on discrete types. -/
private theorem measurable_pairDelta :
    Measurable
      (fun p : (Int × Nat) × (Int × Nat) => pairDelta p.1 p.2) :=
  measurable_of_countable _

/-- One step of the rewiring fold. -/
private def rewireStep {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ)
    (q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S) :
    List (S × (Int × Nat)) × List (S × S) :=
  let n := q.1.1
  let forbid := q.1.2.1
  let start := q.1.2.2.1
  let s := q.1.2.2.2.1
  let p := q.1.2.2.2.2
  let costs := q.2.1.1
  let edges := q.2.1.2
  let w := q.2.2
  if w ≠ start ∧ w ≠ s ∧ w ≠ p ∧ w ∉ forbid ∧
      O.cost s w ≤ radiusOf n ∧ O.link s w = true ∧
      ccLt (ccAdd (costToCome costs s) (O.cost s w))
        (costToCome costs w)
  then (shiftCostsPair edges start w (n + 1)
    (pairDelta (ccAdd (costToCome costs s) (O.cost s w))
      (costToCome costs w)) costs,
    replaceParent edges s w)
  else (costs, edges)

/-- Rewiring `w ≠ start` test is measurable. -/
private theorem measurable_rewireNe1 {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 ≠ q.1.2.2.1)) := by
  have hw : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hstart : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.2.2.1) :=
    measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hdecEq : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 = q.1.2.2.1)) :=
    measurable_decide_eq.comp (hw.prodMk hstart)
  have hnotM : Measurable (fun b : Bool => !b) := Measurable.of_discrete
  have hcomp := hnotM.comp hdecEq
  have heq : (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 ≠ q.1.2.2.1)) =
      (fun b : Bool => !b) ∘
        (fun q : (ℕ × List S × S × S × S) ×
          (List (S × (Int × Nat)) × List (S × S)) × S =>
          decide (q.2.2 = q.1.2.2.1)) := by
    funext q
    simp [decide_not]
  rw [heq]
  exact hcomp

/-- Rewiring `w ≠ s` test is measurable. -/
private theorem measurable_rewireNe2 {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 ≠ q.1.2.2.2.1)) := by
  have hw : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hs : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hdecEq : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 = q.1.2.2.2.1)) :=
    measurable_decide_eq.comp (hw.prodMk hs)
  have hnotM : Measurable (fun b : Bool => !b) := Measurable.of_discrete
  have hcomp := hnotM.comp hdecEq
  have heq : (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 ≠ q.1.2.2.2.1)) =
      (fun b : Bool => !b) ∘
        (fun q : (ℕ × List S × S × S × S) ×
          (List (S × (Int × Nat)) × List (S × S)) × S =>
          decide (q.2.2 = q.1.2.2.2.1)) := by
    funext q
    simp [decide_not]
  rw [heq]
  exact hcomp

/-- Rewiring `w ≠ p` test is measurable. -/
private theorem measurable_rewireNe3 {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 ≠ q.1.2.2.2.2)) := by
  have hw : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hp : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hdecEq : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 = q.1.2.2.2.2)) :=
    measurable_decide_eq.comp (hw.prodMk hp)
  have hnotM : Measurable (fun b : Bool => !b) := Measurable.of_discrete
  have hcomp := hnotM.comp hdecEq
  have heq : (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 ≠ q.1.2.2.2.2)) =
      (fun b : Bool => !b) ∘
        (fun q : (ℕ × List S × S × S × S) ×
          (List (S × (Int × Nat)) × List (S × S)) × S =>
          decide (q.2.2 = q.1.2.2.2.2)) := by
    funext q
    simp [decide_not]
  rw [heq]
  exact hcomp

/-- Rewiring `w ∉ forbid` test is measurable. -/
private theorem measurable_rewireNmem {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 ∉ q.1.2.1)) := by
  have hw : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hforbid : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hdecMem : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 ∈ q.1.2.1)) :=
    measurable_list_mem.comp (hw.prodMk hforbid)
  have hnotM : Measurable (fun b : Bool => !b) := Measurable.of_discrete
  have hcomp := hnotM.comp hdecMem
  have heq : (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (q.2.2 ∉ q.1.2.1)) =
      (fun b : Bool => !b) ∘
        (fun q : (ℕ × List S × S × S × S) ×
          (List (S × (Int × Nat)) × List (S × S)) × S =>
          decide (q.2.2 ∈ q.1.2.1)) := by
    funext q
    simp [decide_not]
  rw [heq]
  exact hcomp

/-- Rewiring radius test is measurable. -/
private theorem measurable_rewireLe {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) :
    Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      decide (O.cost q.1.2.2.2.1 q.2.2 ≤ radiusOf q.1.1)) := by
  have hn : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hs : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hw : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hcostSW : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      O.cost q.1.2.2.2.1 q.2.2) :=
    hO.cost.comp (hs.prodMk hw)
  have hrad : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      radiusOf q.1.1) :=
    (measurable_of_countable radiusOf).comp hn
  have hleM : Measurable (fun r : ℚ × ℚ => decide (r.1 ≤ r.2)) :=
    measurable_of_countable _
  exact hleM.comp (hcostSW.prodMk hrad)

/-- Rewiring link test is measurable. -/
private theorem measurable_rewireLink {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) :
    Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      O.link q.1.2.2.2.1 q.2.2) := by
  have hs : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hw : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.2) :=
    measurable_snd.comp measurable_snd
  exact hO.link.comp (hs.prodMk hw)

/-- Rewiring improvement test is measurable. -/
private theorem measurable_rewireLt {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) :
    Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => decide (ccLt
        (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
          (O.cost q.1.2.2.2.1 q.2.2))
        (costToCome q.2.1.1 q.2.2))) := by
  have hs : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hw : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hcosts : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hcostSW : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      O.cost q.1.2.2.2.1 q.2.2) :=
    hO.cost.comp (hs.prodMk hw)
  have hctcS : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      costToCome q.2.1.1 q.1.2.2.2.1) :=
    measurable_costToCome.comp (hcosts.prodMk hs)
  have hctcW : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      costToCome q.2.1.1 q.2.2) :=
    measurable_costToCome.comp (hcosts.prodMk hw)
  have haddS : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
        (O.cost q.1.2.2.2.1 q.2.2)) :=
    measurable_ccAdd.comp (hctcS.prodMk hcostSW)
  exact measurable_ccLt_decide.comp (haddS.prodMk hctcW)

/-- Rewiring shifted costs are measurable. -/
private theorem measurable_rewireShifted {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) :
    Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      shiftCostsPair q.2.1.2 q.1.2.2.1 q.2.2 (q.1.1 + 1)
        (pairDelta
          (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
            (O.cost q.1.2.2.2.1 q.2.2))
          (costToCome q.2.1.1 q.2.2)) q.2.1.1) := by
  have hn : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.1) :=
    measurable_fst.comp measurable_fst
  have hstart : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.2.2.1) :=
    measurable_fst.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hs : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hw : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hcosts : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hedges : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  have hcostSW : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      O.cost q.1.2.2.2.1 q.2.2) :=
    hO.cost.comp (hs.prodMk hw)
  have hctcS : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      costToCome q.2.1.1 q.1.2.2.2.1) :=
    measurable_costToCome.comp (hcosts.prodMk hs)
  have hctcW : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      costToCome q.2.1.1 q.2.2) :=
    measurable_costToCome.comp (hcosts.prodMk hw)
  have haddS : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
        (O.cost q.1.2.2.2.1 q.2.2)) :=
    measurable_ccAdd.comp (hctcS.prodMk hcostSW)
  have hdelta : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      pairDelta
        (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
          (O.cost q.1.2.2.2.1 q.2.2))
        (costToCome q.2.1.1 q.2.2)) :=
    measurable_pairDelta.comp (haddS.prodMk hctcW)
  have hsucc : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.1 + 1) :=
    Measurable.of_discrete.comp hn
  have hshiftOther : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      (q.2.1.2, q.1.2.2.1, q.2.2,
        pairDelta
          (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
            (O.cost q.1.2.2.2.1 q.2.2))
          (costToCome q.2.1.1 q.2.2),
        q.2.1.1)) :=
    hedges.prodMk (hstart.prodMk (hw.prodMk (hdelta.prodMk hcosts)))
  have hshiftArg : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      ((q.2.1.2, q.1.2.2.1, q.2.2,
        pairDelta
          (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
            (O.cost q.1.2.2.2.1 q.2.2))
          (costToCome q.2.1.1 q.2.2),
        q.2.1.1), q.1.1 + 1)) :=
    hshiftOther.prodMk hsucc
  have hshiftComp := measurable_shift_varying.comp hshiftArg
  have heqS : (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      shiftCostsPair q.2.1.2 q.1.2.2.1 q.2.2 (q.1.1 + 1)
        (pairDelta
          (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
            (O.cost q.1.2.2.2.1 q.2.2))
          (costToCome q.2.1.1 q.2.2)) q.2.1.1) =
      (fun p : (List (S × S) × S × S × (Int × Nat) ×
          List (S × (Int × Nat))) × ℕ =>
        shiftCostsPair p.1.1 p.1.2.1 p.1.2.2.1 p.2 p.1.2.2.2.1
          p.1.2.2.2.2) ∘
        (fun q : (ℕ × List S × S × S × S) ×
          (List (S × (Int × Nat)) × List (S × S)) × S =>
          ((q.2.1.2, q.1.2.2.1, q.2.2,
            pairDelta
              (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
                (O.cost q.1.2.2.2.1 q.2.2))
              (costToCome q.2.1.1 q.2.2),
            q.2.1.1), q.1.1 + 1)) := by
    rfl
  rw [heqS]
  exact hshiftComp

/-- Rewiring replaced edges are measurable. -/
private theorem measurable_rewireReplaced {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      replaceParent q.2.1.2 q.1.2.2.2.1 q.2.2) := by
  have hs : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.1.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_fst)))
  have hw : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hedges : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  have harg : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      (q.2.1.2, q.1.2.2.2.1, q.2.2)) :=
    hedges.prodMk (hs.prodMk hw)
  have hcompR := measurable_replaceParent.comp harg
  have heqR : (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      replaceParent q.2.1.2 q.1.2.2.2.1 q.2.2) =
      (fun p : List (S × S) × S × S =>
        replaceParent p.1 p.2.1 p.2.2) ∘
        (fun q : (ℕ × List S × S × S × S) ×
          (List (S × (Int × Nat)) × List (S × S)) × S =>
          (q.2.1.2, q.1.2.2.2.1, q.2.2)) := by
    rfl
  rw [heqR]
  exact hcompR

/-- Rewiring fold step is measurable. -/
private theorem measurable_rewireStep {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) :
    Measurable (rewireStep O radiusOf) := by
  have hset1 := measurableSet_of_measurable_decide
    (measurable_rewireNe1 (S := S))
  have hset2 := measurableSet_of_measurable_decide
    (measurable_rewireNe2 (S := S))
  have hset3 := measurableSet_of_measurable_decide
    (measurable_rewireNe3 (S := S))
  have hset4 := measurableSet_of_measurable_decide
    (measurable_rewireNmem (S := S))
  have hset5 := measurableSet_of_measurable_decide
    (measurable_rewireLe (S := S) hO radiusOf)
  have hset6 := measurableSet_eq_true
    (measurable_rewireLink (S := S) hO)
  have hset7 := measurableSet_of_measurable_decide
    (measurable_rewireLt (S := S) hO)
  have hcondSet : MeasurableSet {q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S |
      q.2.2 ≠ q.1.2.2.1 ∧ q.2.2 ≠ q.1.2.2.2.1 ∧ q.2.2 ≠ q.1.2.2.2.2 ∧
        q.2.2 ∉ q.1.2.1 ∧ O.cost q.1.2.2.2.1 q.2.2 ≤ radiusOf q.1.1 ∧
        O.link q.1.2.2.2.1 q.2.2 = true ∧
        ccLt (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
          (O.cost q.1.2.2.2.1 q.2.2)) (costToCome q.2.1.1 q.2.2)} := by
    have hinter := hset1.inter (hset2.inter (hset3.inter (hset4.inter
      (hset5.inter (hset6.inter hset7)))))
    have heqSet : {q : (ℕ × List S × S × S × S) ×
          (List (S × (Int × Nat)) × List (S × S)) × S |
          q.2.2 ≠ q.1.2.2.1 ∧ q.2.2 ≠ q.1.2.2.2.1 ∧ q.2.2 ≠ q.1.2.2.2.2 ∧
            q.2.2 ∉ q.1.2.1 ∧ O.cost q.1.2.2.2.1 q.2.2 ≤ radiusOf q.1.1 ∧
            O.link q.1.2.2.2.1 q.2.2 = true ∧
            ccLt (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
              (O.cost q.1.2.2.2.1 q.2.2)) (costToCome q.2.1.1 q.2.2)} =
        {q : (ℕ × List S × S × S × S) ×
            (List (S × (Int × Nat)) × List (S × S)) × S |
            q.2.2 ≠ q.1.2.2.1} ∩ ({q : (ℕ × List S × S × S × S) ×
            (List (S × (Int × Nat)) × List (S × S)) × S |
            q.2.2 ≠ q.1.2.2.2.1} ∩ ({q : (ℕ × List S × S × S × S) ×
            (List (S × (Int × Nat)) × List (S × S)) × S |
            q.2.2 ≠ q.1.2.2.2.2} ∩ ({q : (ℕ × List S × S × S × S) ×
            (List (S × (Int × Nat)) × List (S × S)) × S |
            q.2.2 ∉ q.1.2.1} ∩ ({q : (ℕ × List S × S × S × S) ×
            (List (S × (Int × Nat)) × List (S × S)) × S |
            O.cost q.1.2.2.2.1 q.2.2 ≤ radiusOf q.1.1} ∩
            ({q : (ℕ × List S × S × S × S) ×
            (List (S × (Int × Nat)) × List (S × S)) × S |
            O.link q.1.2.2.2.1 q.2.2 = true} ∩
            {q : (ℕ × List S × S × S × S) ×
            (List (S × (Int × Nat)) × List (S × S)) × S | ccLt
              (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
                (O.cost q.1.2.2.2.1 q.2.2))
              (costToCome q.2.1.1 q.2.2)}))))) := by
      rfl
    rw [heqSet]
    exact hinter
  have hshifted := measurable_rewireShifted (S := S) hO
  have hreplaced := measurable_rewireReplaced (S := S)
  have hthen : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      (shiftCostsPair q.2.1.2 q.1.2.2.1 q.2.2 (q.1.1 + 1)
        (pairDelta
          (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
            (O.cost q.1.2.2.2.1 q.2.2))
          (costToCome q.2.1.1 q.2.2)) q.2.1.1,
        replaceParent q.2.1.2 q.1.2.2.2.1 q.2.2)) :=
    hshifted.prodMk hreplaced
  have hcosts : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hedges : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S => q.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  have helse : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      (q.2.1.1, q.2.1.2)) :=
    hcosts.prodMk hedges
  have hite : Measurable (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      if q.2.2 ≠ q.1.2.2.1 ∧ q.2.2 ≠ q.1.2.2.2.1 ∧
          q.2.2 ≠ q.1.2.2.2.2 ∧ q.2.2 ∉ q.1.2.1 ∧
          O.cost q.1.2.2.2.1 q.2.2 ≤ radiusOf q.1.1 ∧
          O.link q.1.2.2.2.1 q.2.2 = true ∧
          ccLt (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
            (O.cost q.1.2.2.2.1 q.2.2)) (costToCome q.2.1.1 q.2.2)
      then (shiftCostsPair q.2.1.2 q.1.2.2.1 q.2.2 (q.1.1 + 1)
        (pairDelta
          (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
            (O.cost q.1.2.2.2.1 q.2.2))
          (costToCome q.2.1.1 q.2.2)) q.2.1.1,
        replaceParent q.2.1.2 q.1.2.2.2.1 q.2.2)
      else (q.2.1.1, q.2.1.2)) :=
    Measurable.ite hcondSet hthen helse
  have heqDef : (fun q : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × S =>
      if q.2.2 ≠ q.1.2.2.1 ∧ q.2.2 ≠ q.1.2.2.2.1 ∧
          q.2.2 ≠ q.1.2.2.2.2 ∧ q.2.2 ∉ q.1.2.1 ∧
          O.cost q.1.2.2.2.1 q.2.2 ≤ radiusOf q.1.1 ∧
          O.link q.1.2.2.2.1 q.2.2 = true ∧
          ccLt (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
            (O.cost q.1.2.2.2.1 q.2.2)) (costToCome q.2.1.1 q.2.2)
      then (shiftCostsPair q.2.1.2 q.1.2.2.1 q.2.2 (q.1.1 + 1)
        (pairDelta
          (ccAdd (costToCome q.2.1.1 q.1.2.2.2.1)
            (O.cost q.1.2.2.2.1 q.2.2))
          (costToCome q.2.1.1 q.2.2)) q.2.1.1,
        replaceParent q.2.1.2 q.1.2.2.2.1 q.2.2)
      else (q.2.1.1, q.2.1.2)) = rewireStep O radiusOf := by
    funext q
    simp [rewireStep]
  rw [heqDef] at hite
  exact hite

/-- Rewiring recursion equals a fold. -/
private theorem rewireAux_eq_foldl {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (n : ℕ) (forbid : List S) (start s p : S)
    (costs : List (S × (Int × Nat))) (ws : List S) (edges : List (S × S)) :
    rewireAux O costs radiusOf n forbid start s p ws edges =
      (ws.foldl (fun acc w =>
        rewireStep O radiusOf ((n, forbid, start, s, p), acc, w))
        (costs, edges)).2 := by
  induction ws generalizing costs edges with
  | nil =>
      simp [rewireAux]
  | cons w ws ih =>
      simp only [rewireAux, List.foldl_cons]
      by_cases hcond : (w ≠ start ∧ w ≠ s ∧ w ≠ p ∧ w ∉ forbid ∧
          O.cost s w ≤ radiusOf n ∧ O.link s w = true ∧
          ccLt (ccAdd (costToCome costs s) (O.cost s w))
            (costToCome costs w))
      · simp [hcond, ih, rewireStep]
      · simp [hcond, ih, rewireStep]

/-- Rewiring is measurable in all arguments. -/
private theorem measurable_rewireAuxFun {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) :
    Measurable (fun p : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × List S =>
      rewireAux O p.2.1.1 radiusOf p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1
        p.1.2.2.2.2 p.2.2 p.2.1.2) := by
  have hg := measurable_rewireStep (S := S) hO radiusOf
  have hfold := measurable_list_foldl (g := rewireStep O radiusOf) hg
  have hsnd := measurable_snd.comp hfold
  have heq : (fun p : (ℕ × List S × S × S × S) ×
      (List (S × (Int × Nat)) × List (S × S)) × List S =>
      rewireAux O p.2.1.1 radiusOf p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1
        p.1.2.2.2.2 p.2.2 p.2.1.2) =
      (fun p : (ℕ × List S × S × S × S) ×
        (List (S × (Int × Nat)) × List (S × S)) × List S =>
        (p.2.2.foldl (fun b a => rewireStep O radiusOf (p.1, b, a))
          p.2.1).2) := by
    funext p
    exact rewireAux_eq_foldl O radiusOf p.1.1 p.1.2.1 p.1.2.2.1
      p.1.2.2.2.1 p.1.2.2.2.2 p.2.1.1 p.2.2 p.2.1.2
  rw [heq]
  exact hsnd

/-- Steered sample for RRT* extension is measurable. -/
private theorem measurable_extendX {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (start : S) :
    Measurable (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
      O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) := by
  have hvert : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.1) := measurable_fst
  have hs : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hstart : Measurable (fun _ : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => start) := measurable_const
  have hnearArg : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => (p.1, start, p.2.2.2)) :=
    hvert.prodMk (hstart.prodMk hs)
  have hnearComp := (measurable_nearest (S := S) hO).comp hnearArg
  have hu : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      nearest O p.1 start p.2.2.2) := by
    have heqU : (fun p : List S × List (S × S) ×
        List (S × (Int × Nat)) × S =>
        nearest O p.1 start p.2.2.2) =
        (fun q : List S × S × S => nearest O q.1 q.2.1 q.2.2) ∘
          (fun p : List S × List (S × S) ×
            List (S × (Int × Nat)) × S => (p.1, start, p.2.2.2)) := by
      rfl
    rw [heqU]
    exact hnearComp
  have hx : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (nearest O p.1 start p.2.2.2, p.2.2.2)) :=
    hu.prodMk hs
  have hsteerComp := hO.steer.comp hx
  have heqX : (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) =
      (fun q : S × S => O.steer q.1 q.2) ∘
        (fun p : List S × List (S × S) ×
          List (S × (Int × Nat)) × S =>
          (nearest O p.1 start p.2.2.2, p.2.2.2)) := by
    rfl
  rw [heqX]
  exact hsteerComp

/-- Nearest vertex for RRT* extension is measurable. -/
private theorem measurable_extendU {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (start : S) :
    Measurable (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
      nearest O p.1 start p.2.2.2) := by
  have hvert : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.1) := measurable_fst
  have hs : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hstart : Measurable (fun _ : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => start) := measurable_const
  have harg : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => (p.1, start, p.2.2.2)) :=
    hvert.prodMk (hstart.prodMk hs)
  have hcomp := (measurable_nearest (S := S) hO).comp harg
  have heqU : (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      nearest O p.1 start p.2.2.2) =
      (fun q : List S × S × S => nearest O q.1 q.2.1 q.2.2) ∘
        (fun p : List S × List (S × S) ×
          List (S × (Int × Nat)) × S => (p.1, start, p.2.2.2)) := by
    rfl
  rw [heqU]
  exact hcomp

/-- Outer gate of RRT* extension is a measurable set. -/
private theorem measurableSet_extendOuter {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (start : S) :
    MeasurableSet {p : List S × List (S × S) × List (S × (Int × Nat)) × S |
      O.free p.2.2.2 = true ∧
        O.free (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
        O.link (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 ∉ p.1} := by
  have hs : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hvert : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.1) := measurable_fst
  have hu := measurable_extendU (S := S) hO start
  have hx := measurable_extendX (S := S) hO start
  have hfreeS : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => O.free p.2.2.2) :=
    hO.free.comp hs
  have hfreeX : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      O.free (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)) :=
    hO.free.comp hx
  have hlinkUX : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      O.link (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)) :=
    hO.link.comp (hu.prodMk hx)
  have hset1 := measurableSet_eq_true hfreeS
  have hset2 := measurableSet_eq_true hfreeX
  have hset3 := measurableSet_eq_true hlinkUX
  have hdecMem : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      decide (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 ∈ p.1)) :=
    measurable_list_mem.comp (hx.prodMk hvert)
  have hnotM : Measurable (fun b : Bool => !b) := Measurable.of_discrete
  have hdecNmem : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      decide (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 ∉ p.1)) := by
    have hcomp := hnotM.comp hdecMem
    have heq : (fun p : List S × List (S × S) ×
        List (S × (Int × Nat)) × S =>
        decide (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 ∉ p.1)) =
        (fun b : Bool => !b) ∘
          (fun p : List S × List (S × S) ×
            List (S × (Int × Nat)) × S =>
            decide (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2
              ∈ p.1)) := by
      funext p
      simp [decide_not]
    rw [heq]
    exact hcomp
  have hset4 := measurableSet_of_measurable_decide hdecNmem
  have hinter := hset1.inter (hset2.inter (hset3.inter hset4))
  have heqSet : {p : List S × List (S × S) × List (S × (Int × Nat)) × S |
      O.free p.2.2.2 = true ∧
        O.free (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
        O.link (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 ∉ p.1} =
      {p : List S × List (S × S) × List (S × (Int × Nat)) × S |
        O.free p.2.2.2 = true} ∩ ({p : List S × List (S × S) ×
          List (S × (Int × Nat)) × S |
          O.free (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
            = true} ∩ ({p : List S × List (S × S) ×
            List (S × (Int × Nat)) × S |
            O.link (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true} ∩
          {p : List S × List (S × S) × List (S × (Int × Nat)) × S |
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 ∉ p.1})) := by
    rfl
  rw [heqSet]
  exact hinter

/-- Extension candidates are measurable. -/
private theorem measurable_extendCands {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) (start : S) :
    Measurable (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
      candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)) := by
  have hvert : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.1) := measurable_fst
  have hu := measurable_extendU (S := S) hO start
  have hx := measurable_extendX (S := S) hO start
  have harg : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (p.1, nearest O p.1 start p.2.2.2,
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)) :=
    hvert.prodMk (hu.prodMk hx)
  have hcomp := (measurable_candidates (S := S) hO radiusOf).comp harg
  have heq : (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)) =
      (fun q : List S × S × S =>
        candidates O q.1 radiusOf q.2.1 q.2.2) ∘
        (fun p : List S × List (S × S) ×
          List (S × (Int × Nat)) × S =>
          (p.1, nearest O p.1 start p.2.2.2,
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)) := by
    rfl
  rw [heq]
  exact hcomp

/-- Nonempty candidates form a measurable set. -/
private theorem measurableSet_extendNonempty {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) (start : S) :
    MeasurableSet {p : List S × List (S × S) × List (S × (Int × Nat)) × S |
      candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) ≠ []} := by
  have hcands := measurable_extendCands (S := S) hO radiusOf start
  have hlen : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)).length) :=
    measurable_list_length.comp hcands
  have hdecEq0 : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => decide
        ((candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)).length = 0)) := by
    have h0M : Measurable (fun n : ℕ => decide (n = 0)) :=
      Measurable.of_discrete
    have hcomp := h0M.comp hlen
    have heq : (fun p : List S × List (S × S) ×
        List (S × (Int × Nat)) × S => decide
          ((candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)).length
            = 0)) =
        (fun n : ℕ => decide (n = 0)) ∘
          (fun p : List S × List (S × S) ×
            List (S × (Int × Nat)) × S =>
            (candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)).length) := by
      rfl
    rw [heq]
    exact hcomp
  have hempty : MeasurableSet {p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S |
      candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = []} := by
    have hset0 := measurableSet_of_measurable_decide hdecEq0
    have heqSet : {p : List S × List (S × S) ×
        List (S × (Int × Nat)) × S |
        candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = []} =
        {p : List S × List (S × S) × List (S × (Int × Nat)) × S |
          (candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)).length
            = 0} := by
      ext p
      simp [List.length_eq_zero_iff]
    rw [heqSet]
    exact hset0
  have hcompl := MeasurableSet.compl hempty
  have heqNe : {p : List S × List (S × S) × List (S × (Int × Nat)) × S |
      candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) ≠ []} =
      {p : List S × List (S × S) × List (S × (Int × Nat)) × S |
        candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = []}ᶜ := by
    rfl
  rw [heqNe]
  exact hcompl

/-- Extension parent value is measurable. -/
private theorem measurable_extendParent {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) (start : S) :
    Measurable (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
      parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)) := by
  have hvert : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.1) := measurable_fst
  have hcosts : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hu := measurable_extendU (S := S) hO start
  have hx := measurable_extendX (S := S) hO start
  have harg : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (p.1, p.2.2.1, nearest O p.1 start p.2.2.2,
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)) :=
    hvert.prodMk (hcosts.prodMk (hu.prodMk hx))
  have hcomp := (measurable_parentVal (S := S) hO radiusOf).comp harg
  have heq : (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)) =
      (fun q : List S × List (S × (Int × Nat)) × S × S =>
        parentVal O q.1 q.2.1 radiusOf q.2.2.1 q.2.2.2) ∘
        (fun p : List S × List (S × S) ×
          List (S × (Int × Nat)) × S =>
          (p.1, p.2.2.1, nearest O p.1 start p.2.2.2,
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)) := by
    rfl
  rw [heq]
  exact hcomp

/-- Extended vertices are measurable. -/
private theorem measurable_extendVerts' {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (start : S) :
    Measurable (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
      O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1) := by
  have hvert : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.1) := measurable_fst
  have hx := measurable_extendX (S := S) hO start
  have harg : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2, p.1)) :=
    hx.prodMk hvert
  have hcomp := measurable_list_cons.comp harg
  have heq : (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1) =
      (fun q : S × List S => q.1 :: q.2) ∘
        (fun p : List S × List (S × S) ×
          List (S × (Int × Nat)) × S =>
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2, p.1)) := by
    rfl
  rw [heq]
  exact hcomp

/-- Extended initial edges are measurable. -/
private theorem measurable_extendEdges0 {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) (start : S) :
    Measurable (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
      (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1) := by
  have hedges : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hparent := measurable_extendParent (S := S) hO radiusOf start
  have hx := measurable_extendX (S := S) hO start
  have hpair : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)) :=
    hparent.prodMk hx
  have harg : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2), p.2.1)) :=
    hpair.prodMk hedges
  have hcomp := measurable_list_cons.comp harg
  have heq : (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1) =
      (fun q : (S × S) × List (S × S) => q.1 :: q.2) ∘
        (fun p : List S × List (S × S) ×
          List (S × (Int × Nat)) × S =>
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2), p.2.1)) := by
    rfl
  rw [heq]
  exact hcomp

/-- Forbid list for rewiring is measurable. -/
private theorem measurable_extendForbid {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) (start : S) :
    Measurable (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
      parentChain
        ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
          O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
        start
        (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
        p.1.length) := by
  have hvert : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.1) := measurable_fst
  have hn : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.1.length) :=
    measurable_list_length.comp hvert
  have hstart : Measurable (fun _ : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => start) := measurable_const
  have hedges0 := measurable_extendEdges0 (S := S) hO radiusOf start
  have hparent := measurable_extendParent (S := S) hO radiusOf start
  have hother : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1),
        start,
        parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))) :=
    hedges0.prodMk (hstart.prodMk hparent)
  have harg : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      ((((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1),
        start,
        parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)), p.1.length)) :=
    hother.prodMk hn
  have hcomp := measurable_parentChain_varying.comp harg
  have heq : (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      parentChain
        ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
          O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
        start
        (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
        p.1.length) =
      (fun q : (List (S × S) × S × S) × ℕ =>
        parentChain q.1.1 q.1.2.1 q.1.2.2 q.2) ∘
        (fun p : List S × List (S × S) ×
          List (S × (Int × Nat)) × S =>
          ((((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1),
            start,
            parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)),
            p.1.length)) := by
    rfl
  rw [heq]
  exact hcomp

/-- Initial recomputed costs are measurable. -/
private theorem measurable_extendCosts0 {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) (start : S) :
    Measurable (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
      recomputeCosts O
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
        ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
          O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
        start) := by
  have hverts' := measurable_extendVerts' (S := S) hO start
  have hedges0 := measurable_extendEdges0 (S := S) hO radiusOf start
  have hstart : Measurable (fun _ : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => start) := measurable_const
  have harg : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1,
        ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
          O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1),
        start)) :=
    hverts'.prodMk (hedges0.prodMk hstart)
  have hcomp := (measurable_recomputeCosts (S := S) hO).comp harg
  have heq : (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      recomputeCosts O
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
        ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
          O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
        start) =
      (fun q : List S × List (S × S) × S =>
        recomputeCosts O q.1 q.2.1 q.2.2) ∘
        (fun p : List S × List (S × S) ×
          List (S × (Int × Nat)) × S =>
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1,
            ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1),
            start)) := by
    rfl
  rw [heq]
  exact hcomp

/-- Rewired edges are measurable. -/
private theorem measurable_extendEdges' {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) (start : S) :
    Measurable (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
      rewireAux O
        (recomputeCosts O
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
          start)
        radiusOf p.1.length
        (parentChain
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
          start
          (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
          p.1.length)
        start
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
        (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
        p.1
        ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
          O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)) := by
  have hvert : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.1) := measurable_fst
  have hn : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.1.length) :=
    measurable_list_length.comp hvert
  have hstart : Measurable (fun _ : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => start) := measurable_const
  have hx := measurable_extendX (S := S) hO start
  have hparent := measurable_extendParent (S := S) hO radiusOf start
  have hedges0 := measurable_extendEdges0 (S := S) hO radiusOf start
  have hforbid := measurable_extendForbid (S := S) hO radiusOf start
  have hcosts0 := measurable_extendCosts0 (S := S) hO radiusOf start
  have hdelta : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (p.1.length,
        parentChain
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
          start
          (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
          p.1.length,
        start,
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2,
        parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))) :=
    hn.prodMk (hforbid.prodMk (hstart.prodMk (hx.prodMk hparent)))
  have hbeta : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (recomputeCosts O
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
        ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
          O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
        start,
        ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
          O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1))) :=
    hcosts0.prodMk hedges0
  have harg : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      ((p.1.length,
        parentChain
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
          start
          (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
          p.1.length,
        start,
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2,
        parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)),
        (recomputeCosts O
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
          start,
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)),
        p.1)) :=
    hdelta.prodMk (hbeta.prodMk hvert)
  have hcomp := (measurable_rewireAuxFun (S := S) hO radiusOf).comp harg
  have heq : (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      rewireAux O
        (recomputeCosts O
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
          start)
        radiusOf p.1.length
        (parentChain
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
          start
          (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
          p.1.length)
        start
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
        (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
        p.1
        ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
          O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)) =
      (fun q : (ℕ × List S × S × S × S) ×
        (List (S × (Int × Nat)) × List (S × S)) × List S =>
        rewireAux O q.2.1.1 radiusOf q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2.1
          q.1.2.2.2.2 q.2.2 q.2.1.2) ∘
        (fun p : List S × List (S × S) ×
          List (S × (Int × Nat)) × S =>
          ((p.1.length,
            parentChain
              ((parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
              start
              (parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
              p.1.length,
            start,
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2,
            parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)),
            (recomputeCosts O
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
              ((parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
              start,
              ((parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)),
            p.1)) := by
    rfl
  rw [heq]
  exact hcomp

/-- Final recomputed costs are measurable. -/
private theorem measurable_extendCosts' {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) (start : S) :
    Measurable (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
      recomputeCosts O
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
        (rewireAux O
          (recomputeCosts O
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
            ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
            start)
          radiusOf p.1.length
          (parentChain
            ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
            start
            (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
            p.1.length)
          start
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
          (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
          p.1
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1))
        start) := by
  have hverts' := measurable_extendVerts' (S := S) hO start
  have hedges' := measurable_extendEdges' (S := S) hO radiusOf start
  have hstart : Measurable (fun _ : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => start) := measurable_const
  have harg : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1,
        rewireAux O
          (recomputeCosts O
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
            ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
            start)
          radiusOf p.1.length
          (parentChain
            ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
            start
            (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
            p.1.length)
          start
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
          (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
          p.1
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1),
        start)) :=
    hverts'.prodMk (hedges'.prodMk hstart)
  have hcomp := (measurable_recomputeCosts (S := S) hO).comp harg
  have heq : (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      recomputeCosts O
        (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
        (rewireAux O
          (recomputeCosts O
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
            ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
            start)
          radiusOf p.1.length
          (parentChain
            ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
            start
            (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
            p.1.length)
          start
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
          (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
          p.1
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1))
        start) =
      (fun q : List S × List (S × S) × S =>
        recomputeCosts O q.1 q.2.1 q.2.2) ∘
        (fun p : List S × List (S × S) ×
          List (S × (Int × Nat)) × S =>
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1,
            rewireAux O
              (recomputeCosts O
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
                ((parentVal O p.1 p.2.2.1 radiusOf
                  (nearest O p.1 start p.2.2.2)
                  (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                  O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
                start)
              radiusOf p.1.length
              (parentChain
                ((parentVal O p.1 p.2.2.1 radiusOf
                  (nearest O p.1 start p.2.2.2)
                  (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                  O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
                start
                (parentVal O p.1 p.2.2.1 radiusOf
                  (nearest O p.1 start p.2.2.2)
                  (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
                p.1.length)
              start
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
              (parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
              p.1
              ((parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1),
            start)) := by
    rfl
  rw [heq]
  exact hcomp

/-- RRT* one-step extension is measurable. -/
private theorem measurable_extendStarFun {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) (start : S) :
    Measurable (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
      extendStar O p.1 p.2.1 p.2.2.1 radiusOf start p.2.2.2) := by
  have hverts' := measurable_extendVerts' (S := S) hO start
  have hedges' := measurable_extendEdges' (S := S) hO radiusOf start
  have hcosts' := measurable_extendCosts' (S := S) hO radiusOf start
  have hconstr : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1,
        rewireAux O
          (recomputeCosts O
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
            ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
            start)
          radiusOf p.1.length
          (parentChain
            ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
            start
            (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
            p.1.length)
          start
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
          (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
          p.1
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1),
        recomputeCosts O
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
          (rewireAux O
            (recomputeCosts O
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
              ((parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
              start)
            radiusOf p.1.length
            (parentChain
              ((parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
              start
              (parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
              p.1.length)
            start
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
            (parentVal O p.1 p.2.2.1 radiusOf
              (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
            p.1
            ((parentVal O p.1 p.2.2.1 radiusOf
              (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1))
          start)) :=
    hverts'.prodMk (hedges'.prodMk hcosts')
  have hvert : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.1) := measurable_fst
  have hedges : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hcosts : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hid : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S => (p.1, p.2.1, p.2.2.1)) :=
    hvert.prodMk (hedges.prodMk hcosts)
  have houter := measurableSet_extendOuter (S := S) hO start
  have hnonempty := measurableSet_extendNonempty (S := S) hO radiusOf start
  have hcondSet : MeasurableSet {p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S |
      (O.free p.2.2.2 = true ∧
        O.free (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
        O.link (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
        O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 ∉ p.1) ∧
        candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) ≠ []} := by
    have hinter := houter.inter hnonempty
    have heqSet : {p : List S × List (S × S) ×
        List (S × (Int × Nat)) × S |
        (O.free p.2.2.2 = true ∧
          O.free (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
          O.link (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
          O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 ∉ p.1) ∧
          candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) ≠ []} =
        {p : List S × List (S × S) × List (S × (Int × Nat)) × S |
          O.free p.2.2.2 = true ∧
            O.free (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
              = true ∧
            O.link (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 ∉ p.1} ∩
          {p : List S × List (S × S) × List (S × (Int × Nat)) × S |
            candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) ≠ []} := by
      rfl
    rw [heqSet]
    exact hinter
  have hite : Measurable (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      if (O.free p.2.2.2 = true ∧
          O.free (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
          O.link (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
          O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 ∉ p.1) ∧
          candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) ≠ []
      then (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1,
        rewireAux O
          (recomputeCosts O
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
            ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
            start)
          radiusOf p.1.length
          (parentChain
            ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
            start
            (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
            p.1.length)
          start
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
          (parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
          p.1
          ((parentVal O p.1 p.2.2.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1),
        recomputeCosts O
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
          (rewireAux O
            (recomputeCosts O
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
              ((parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
              start)
            radiusOf p.1.length
            (parentChain
              ((parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
              start
              (parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
              p.1.length)
            start
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
            (parentVal O p.1 p.2.2.1 radiusOf
              (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
            p.1
            ((parentVal O p.1 p.2.2.1 radiusOf
              (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1))
          start)
      else (p.1, p.2.1, p.2.2.1)) :=
    Measurable.ite hcondSet hconstr hid
  have heqFun : (fun p : List S × List (S × S) ×
      List (S × (Int × Nat)) × S =>
      extendStar O p.1 p.2.1 p.2.2.1 radiusOf start p.2.2.2) =
      (fun p : List S × List (S × S) ×
        List (S × (Int × Nat)) × S =>
        if (O.free p.2.2.2 = true ∧
            O.free (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
              = true ∧
            O.link (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) = true ∧
            O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 ∉ p.1) ∧
            candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) ≠ []
        then (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1,
          rewireAux O
            (recomputeCosts O
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
              ((parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
              start)
            radiusOf p.1.length
            (parentChain
              ((parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
              start
              (parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
              p.1.length)
            start
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
            (parentVal O p.1 p.2.2.1 radiusOf
              (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
            p.1
            ((parentVal O p.1 p.2.2.1 radiusOf
              (nearest O p.1 start p.2.2.2)
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
              O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1),
          recomputeCosts O
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
            (rewireAux O
              (recomputeCosts O
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2 :: p.1)
                ((parentVal O p.1 p.2.2.1 radiusOf
                  (nearest O p.1 start p.2.2.2)
                  (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                  O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
                start)
              radiusOf p.1.length
              (parentChain
                ((parentVal O p.1 p.2.2.1 radiusOf
                  (nearest O p.1 start p.2.2.2)
                  (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                  O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1)
                start
                (parentVal O p.1 p.2.2.1 radiusOf
                  (nearest O p.1 start p.2.2.2)
                  (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
                p.1.length)
              start
              (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2)
              (parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2))
              p.1
              ((parentVal O p.1 p.2.2.1 radiusOf
                (nearest O p.1 start p.2.2.2)
                (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2),
                O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) :: p.2.1))
            start)
        else (p.1, p.2.1, p.2.2.1)) := by
    funext p
    simp only [extendStar]
    cases hc : candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
      (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) with
    | nil =>
        simp [hc, chooseParent]
    | cons h t =>
        have hne : candidates O p.1 radiusOf (nearest O p.1 start p.2.2.2)
            (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) ≠ [] := by
          simp [hc]
        have hcp := chooseParent_eq_parentVal O p.1 p.2.2.1 radiusOf
          (nearest O p.1 start p.2.2.2)
          (O.steer (nearest O p.1 start p.2.2.2) p.2.2.2) h t hc
        simp [hcp]
  rw [heqFun]
  exact hite

/-- RRT* auxiliary run equals a fold. -/
private theorem rrtStarAux_eq_foldl {S : Type} [DecidableEq S] (O : Oracles S)
    (radiusOf : ℕ → ℚ) (start : S) (verts : List S) (edges : List (S × S))
    (costs : List (S × (Int × Nat))) (samples : List S) :
    rrtStarAux O radiusOf start verts edges costs samples =
      samples.foldl
        (fun acc s => extendStar O acc.1 acc.2.1 acc.2.2 radiusOf start s)
        (verts, edges, costs) := by
  induction samples generalizing verts edges costs with
  | nil =>
      simp [rrtStarAux]
  | cons s ss ih =>
      simp only [rrtStarAux, List.foldl_cons]
      simp [ih]

/-- RRT* fold step is measurable. -/
private theorem measurable_rrtStarStep {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) (start : S) :
    Measurable (fun q : Unit ×
      (List S × List (S × S) × List (S × (Int × Nat))) × S =>
      extendStar O q.2.1.1 q.2.1.2.1 q.2.1.2.2 radiusOf start q.2.2) := by
  have hfun := measurable_extendStarFun (S := S) hO radiusOf start
  have harg : Measurable (fun q : Unit ×
      (List S × List (S × S) × List (S × (Int × Nat))) × S =>
      (q.2.1.1, q.2.1.2.1, q.2.1.2.2, q.2.2)) := by
    have h1 : Measurable (fun q : Unit ×
        (List S × List (S × S) × List (S × (Int × Nat))) × S =>
        q.2.1.1) :=
      measurable_fst.comp (measurable_fst.comp measurable_snd)
    have h2 : Measurable (fun q : Unit ×
        (List S × List (S × S) × List (S × (Int × Nat))) × S =>
        q.2.1.2.1) :=
      measurable_fst.comp
        (measurable_snd.comp (measurable_fst.comp measurable_snd))
    have h3 : Measurable (fun q : Unit ×
        (List S × List (S × S) × List (S × (Int × Nat))) × S =>
        q.2.1.2.2) :=
      measurable_snd.comp
        (measurable_snd.comp (measurable_fst.comp measurable_snd))
    have h4 : Measurable (fun q : Unit ×
        (List S × List (S × S) × List (S × (Int × Nat))) × S =>
        q.2.2) :=
      measurable_snd.comp measurable_snd
    exact h1.prodMk (h2.prodMk (h3.prodMk h4))
  have hcomp := hfun.comp harg
  have heq : (fun q : Unit ×
      (List S × List (S × S) × List (S × (Int × Nat))) × S =>
      extendStar O q.2.1.1 q.2.1.2.1 q.2.1.2.2 radiusOf start q.2.2) =
      (fun p : List S × List (S × S) × List (S × (Int × Nat)) × S =>
        extendStar O p.1 p.2.1 p.2.2.1 radiusOf start p.2.2.2) ∘
        (fun q : Unit ×
          (List S × List (S × S) × List (S × (Int × Nat))) × S =>
          (q.2.1.1, q.2.1.2.1, q.2.1.2.2, q.2.2)) := by
    rfl
  rw [heq]
  exact hcomp

/-- The RRT* output (vertices, edges and cost table) is a measurable function of the
sample list, for any radius schedule. -/
theorem measurable_rrtStar {S : Type} [DecidableEq S] [MeasurableSpace S] [MeasurableEq S]
    {O : Oracles S} (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ) (start : S) :
    Measurable (rrtStar O radiusOf start) := by
  have hg := measurable_rrtStarStep (S := S) hO radiusOf start
  have hfold := measurable_list_foldl
    (g := fun q : Unit ×
      (List S × List (S × S) × List (S × (Int × Nat))) × S =>
      extendStar O q.2.1.1 q.2.1.2.1 q.2.1.2.2 radiusOf start q.2.2) hg
  have hinitV : Measurable (fun _ : List S => [start]) := measurable_const
  have hinitE : Measurable (fun _ : List S => ([] : List (S × S))) :=
    measurable_const
  have hinitC : Measurable (fun _ : List S =>
      recomputeCosts O [start] [] start) := measurable_const
  have hinit : Measurable (fun _ : List S =>
      ([start], ([] : List (S × S)), recomputeCosts O [start] [] start)) :=
    hinitV.prodMk (hinitE.prodMk hinitC)
  have hunit : Measurable (fun _ : List S => (() : Unit)) := measurable_const
  have harg : Measurable (fun samples : List S =>
      ((), ([start], ([] : List (S × S)),
        recomputeCosts O [start] [] start), samples)) :=
    hunit.prodMk (hinit.prodMk measurable_id')
  have hcomp := hfold.comp harg
  have heq : (fun samples : List S => rrtStar O radiusOf start samples) =
      (fun p : Unit ×
        (List S × List (S × S) × List (S × (Int × Nat))) × List S =>
        p.2.2.foldl
          (fun b a => extendStar O b.1 b.2.1 b.2.2 radiusOf start a)
          p.2.1) ∘
        (fun samples : List S =>
          ((), ([start], ([] : List (S × S)),
            recomputeCosts O [start] [] start), samples)) := by
    funext samples
    simp [rrtStar, rrtStarAux_eq_foldl]
  show Measurable (fun samples : List S => rrtStar O radiusOf start samples)
  rw [heq]
  exact hcomp

/-- RRT* skips samples that are not collision free. -/
theorem rrtStar_filter_free {S : Type} [DecidableEq S] (O : Oracles S) (radiusOf : ℕ → ℚ)
    (start : S) (samples : List S) :
    rrtStar O radiusOf start (samples.filter O.free) = rrtStar O radiusOf start samples := by
  unfold rrtStar
  exact rrtStarAux_filter_free O radiusOf start samples _ _ _

end Cslib.Planning.MotionPlanning.SamplingPlanners
