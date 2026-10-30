/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
    PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleTorusPushforward

/-!
# Translation closure of thin crossings and a counterexample

The translation closure of the thin-crossing event on the torus, its description by a finite
expanded union, and an explicit configuration on the 8-torus showing that the closure is not covered
by coarse thin crossings.

## i. Overview

Closing the thin-crossing event under torus translations gives an event described by `L² · 2α³`
translated long rectangles. `not_translationClosure_coarseCover_two_one` is a Lean-checked
refutation: for `L = 8`, `α = 2`, `n = 1` the translation-closure event does NOT satisfy
`BdcTorusWindingToThinCover`, via the explicit configuration
`thinTranslationClosureCounterexampleConfig`. Covers of that shape are therefore unavailable without
changing the geometry.

## ii. Key results

- `bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_finiteExpanded`: finite description of
  the closure.
- `not_translationClosure_coarseCover_two_one`: refutation of the coarse cover at `(8, 2, 1)`.

## iii. Table of contents

- A. Translation closure
- B. Expanded unions
- C. Counterexample on the 8-torus

## iv. References

* V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster model is
  critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012).
-/

@[expose] public section

open MeasureTheory SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.Universality

/-! ## A. Translation closure -/

lemma translateConfig_add (t s : Site 2)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    translateConfig t (translateConfig s omega) =
      translateConfig (t + s) omega := by
  funext e
  unfold translateConfig
  rw [Sym2.map_map]
  congr 1
  apply Sym2.map_congr
  intro z _hz
  ext i
  simp [add_assoc]

lemma torusAmbientTranslateConfig_add
    (L : ℕ) [Fact (2 < L)] (t s : Site 2)
    (omega : TorusAmbientConfig L) :
    torusAmbientTranslateConfig L t
        (torusAmbientTranslateConfig L s omega) =
      torusAmbientTranslateConfig L (t + s) omega := by
  apply torusPlanarPullback_injective L
  rw [torusPlanarPullback_translate, torusPlanarPullback_translate,
    torusPlanarPullback_translate, translateConfig_add]

@[simp] lemma torusAmbientTranslateConfig_zero
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    torusAmbientTranslateConfig L 0 omega = omega := by
  apply torusPlanarPullback_injective L
  rw [torusPlanarPullback_translate, translateConfig_zero]

/-- Some torus translate of the configuration has a thin crossing. -/
def bdcTorusThinCrossingTranslationClosure
    (L alpha n : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : Prop :=
  ∃ t : Site 2,
    bdcTorusThinCrossing L alpha n
      (torusAmbientTranslateConfig L t omega)

lemma bdcTorusThinCrossing_subset_translationClosure
    (L alpha n : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L)
    (h : bdcTorusThinCrossing L alpha n omega) :
    bdcTorusThinCrossingTranslationClosure L alpha n omega := by
  refine ⟨0, ?_⟩
  simpa using h

lemma bdcTorusThinCrossingTranslationClosure_translate_iff
    (L alpha n : ℕ) [Fact (2 < L)]
    (s : Site 2) (omega : TorusAmbientConfig L) :
    bdcTorusThinCrossingTranslationClosure L alpha n
        (torusAmbientTranslateConfig L s omega) ↔
      bdcTorusThinCrossingTranslationClosure L alpha n omega := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t + s, ?_⟩
    rw [torusAmbientTranslateConfig_add] at ht
    exact ht
  · rintro ⟨t, ht⟩
    refine ⟨t - s, ?_⟩
    rw [torusAmbientTranslateConfig_add]
    convert ht using 1
    congr 2
    ext i
    simp

/-- The set of torus configurations in the translation closure of the thin-crossing event. -/
def bdcTorusThinCrossingTranslationClosureEvent
    (L alpha n : ℕ) [Fact (2 < L)] :
    Set (TorusAmbientConfig L) :=
  {omega | bdcTorusThinCrossingTranslationClosure L alpha n omega}

lemma bdcTorusThinCrossingTranslationClosureEvent_preimage
    (L alpha n : ℕ) [Fact (2 < L)] (s : Site 2) :
    torusAmbientTranslateConfig L s ⁻¹'
        bdcTorusThinCrossingTranslationClosureEvent L alpha n =
      bdcTorusThinCrossingTranslationClosureEvent L alpha n := by
  ext omega
  exact bdcTorusThinCrossingTranslationClosure_translate_iff
    L alpha n s omega

/-- The canonical lattice representative of a torus site. -/
def bdcTorusCanonicalShift {L : ℕ} (u : ZMod L × ZMod L) : Site 2 :=
  ![(u.1.val : ℤ), (u.2.val : ℤ)]

@[simp] lemma torusReduceSite_bdcTorusCanonicalShift
    (L : ℕ) [NeZero L] (u : ZMod L × ZMod L) :
    torusReduceSite L (bdcTorusCanonicalShift u) = u := by
  apply Prod.ext
  · change (((u.1.val : ℕ) : ℤ) : ZMod L) = u.1
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  · change (((u.2.val : ℕ) : ℤ) : ZMod L) = u.2
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]

lemma torusAmbientTranslateConfig_eq_canonical
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (omega : TorusAmbientConfig L) :
    torusAmbientTranslateConfig L t omega =
      torusAmbientTranslateConfig L
        (bdcTorusCanonicalShift (torusReduceSite L t)) omega := by
  funext e
  unfold torusAmbientTranslateConfig
  congr 1
  apply Subtype.ext
  change Sym2.map (torusSiteTranslateEquiv L t) e.1 =
    Sym2.map (torusSiteTranslateEquiv L
      (bdcTorusCanonicalShift (torusReduceSite L t))) e.1
  apply Sym2.map_congr
  intro z _hz
  apply Prod.ext <;>
    simp [torusSiteTranslateEquiv, bdcTorusCanonicalShift, torusReduceSite]

/-! ## B. Expanded unions -/

/-- Indices of torus-translated long rectangles: a torus shift and a rectangle index. -/
abbrev BdcLongRectangleTorusTranslationIndex (L alpha : ℕ) :=
  (ZMod L × ZMod L) × BdcLongRectangleIndex alpha

/-- The vertical crossing event of a torus-translated long rectangle. -/
def bdcLongRectangleTorusTranslatedEvent
    (L alpha n : ℕ)
    (j : BdcLongRectangleTorusTranslationIndex L alpha) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  translateConfig (bdcTorusCanonicalShift j.1) ⁻¹'
    bdcLongRectangleEvent alpha n j.2

/-- The union of all torus-translated long-rectangle crossing events. -/
def bdcLongRectangleTorusTranslationExpandedUnion
    (L alpha n : ℕ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ j : BdcLongRectangleTorusTranslationIndex L alpha,
    bdcLongRectangleTorusTranslatedEvent L alpha n j

lemma bdcLongRectangleTorusTranslationIndex_card
    (L alpha : ℕ) [NeZero L] :
    Fintype.card (BdcLongRectangleTorusTranslationIndex L alpha) =
      L ^ 2 * (2 * alpha ^ 3) := by
  simp [BdcLongRectangleIndex]
  ring

/-- All torus-translation indices, as a `Finset`. -/
def bdcLongRectangleTorusTranslationIndices
    (L alpha : ℕ) [NeZero L] :
    Finset (BdcLongRectangleTorusTranslationIndex L alpha) :=
  Finset.univ

lemma bdcLongRectangleTorusTranslationIndices_card
    (L alpha : ℕ) [NeZero L] :
    (bdcLongRectangleTorusTranslationIndices L alpha).card =
      L ^ 2 * (2 * alpha ^ 3) := by
  simpa [bdcLongRectangleTorusTranslationIndices] using
    bdcLongRectangleTorusTranslationIndex_card L alpha

lemma monotone_translateConfig (t : Site 2) :
    Monotone (translateConfig t) := by
  intro omega eta homega e
  exact homega _

lemma bdcLongRectangleTorusTranslatedEvent_isIncreasing
    (L alpha n : ℕ)
    (j : BdcLongRectangleTorusTranslationIndex L alpha) :
    IsIncreasing (bdcLongRectangleTorusTranslatedEvent L alpha n j) := by
  intro omega eta homegaeta homega
  exact bdcLongRectangleEvent_isIncreasing alpha n j.2
    (monotone_translateConfig (bdcTorusCanonicalShift j.1) homegaeta)
    homega

lemma bdcLongRectangleTorusTranslatedEvent_measurableSet
    (L alpha n : ℕ)
    (j : BdcLongRectangleTorusTranslationIndex L alpha) :
    MeasurableSet (bdcLongRectangleTorusTranslatedEvent L alpha n j) := by
  exact (bdcLongRectangleEvent_measurableSet alpha n j.2).preimage
    (cti_measurable_translateConfig (bdcTorusCanonicalShift j.1))

lemma bdcLongRectangleTorusTranslatedEvent_probability_eq
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (hshift : ∀ t : Site 2, MeasurePreserving (translateConfig t) mu mu)
    (L alpha n : ℕ)
    (j : BdcLongRectangleTorusTranslationIndex L alpha) :
    mu.real (bdcLongRectangleTorusTranslatedEvent L alpha n j) =
      mu.real (bdcLongRectangleBaseEvent alpha n) := by
  calc
    mu.real (bdcLongRectangleTorusTranslatedEvent L alpha n j) =
        mu.real (bdcLongRectangleEvent alpha n j.2) :=
      (hshift (bdcTorusCanonicalShift j.1)).measureReal_preimage
        (bdcLongRectangleEvent_measurableSet alpha n j.2).nullMeasurableSet
    _ = mu.real (bdcLongRectangleBaseEvent alpha n) :=
      bdcLongRectangleEvent_probability_eq mu hshift alpha n j.2

lemma bdcLongRectangleTorusTranslationExpandedUnion_eq_finset
    (L alpha n : ℕ) [NeZero L] :
    bdcLongRectangleTorusTranslationExpandedUnion L alpha n =
      ⋃ j ∈ bdcLongRectangleTorusTranslationIndices L alpha,
        bdcLongRectangleTorusTranslatedEvent L alpha n j := by
  ext omega
  simp [bdcLongRectangleTorusTranslationExpandedUnion,
    bdcLongRectangleTorusTranslationIndices]

/-- The index of the untranslated rectangle with zero shift. -/
def bdcLongRectangleTorusTranslationOriginIndex
    (L alpha : ℕ) (ha : 0 < alpha) :
    BdcLongRectangleTorusTranslationIndex L alpha :=
  ((0, 0), bdcLongRectangleOriginIndex alpha ha)

@[simp] lemma bdcLongRectangleTorusTranslationOriginIndex_mem
    (L alpha : ℕ) [NeZero L] (ha : 0 < alpha) :
    bdcLongRectangleTorusTranslationOriginIndex L alpha ha ∈
      bdcLongRectangleTorusTranslationIndices L alpha := by
  simp [bdcLongRectangleTorusTranslationIndices]

@[simp] lemma bdcLongRectangleTorusTranslationOriginIndex_event
    (L alpha n : ℕ) (ha : 0 < alpha) :
    bdcLongRectangleTorusTranslatedEvent L alpha n
        (bdcLongRectangleTorusTranslationOriginIndex L alpha ha) =
      bdcLongRectangleBaseEvent alpha n := by
  have hzero : bdcTorusCanonicalShift
      ((0, 0) : ZMod L × ZMod L) = (0 : Site 2) := by
    ext i
    fin_cases i <;> simp [bdcTorusCanonicalShift]
  rw [show bdcLongRectangleTorusTranslatedEvent L alpha n
      (bdcLongRectangleTorusTranslationOriginIndex L alpha ha) =
      translateConfig (bdcTorusCanonicalShift ((0, 0) : ZMod L × ZMod L)) ⁻¹'
        bdcLongRectangleEvent alpha n
          (bdcLongRectangleOriginIndex alpha ha) by rfl]
  rw [hzero, bdcLongRectangleOriginIndex_event]
  ext omega
  change translateConfig 0 omega ∈ bdcLongRectangleBaseEvent alpha n ↔
    omega ∈ bdcLongRectangleBaseEvent alpha n
  rw [translateConfig_zero]

/-- The union over all lattice translations of the long-rectangle crossing events. -/
def bdcLongRectangleTranslationExpandedUnion (alpha n : ℕ) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  ⋃ t : Site 2,
    translateConfig t ⁻¹' bdcLongRectangleUnion alpha n

lemma bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_expanded
    (L alpha n : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    bdcTorusThinCrossingTranslationClosure L alpha n omega ↔
      torusPlanarPullback L omega ∈
        bdcLongRectangleTranslationExpandedUnion alpha n := by
  constructor
  · rintro ⟨t, ht⟩
    rw [bdcTorusThinCrossing_iff_pullback_mem_union,
      torusPlanarPullback_translate] at ht
    exact Set.mem_iUnion.2 ⟨t, ht⟩
  · intro h
    obtain ⟨t, ht⟩ := Set.mem_iUnion.1 h
    refine ⟨t, ?_⟩
    rw [bdcTorusThinCrossing_iff_pullback_mem_union,
      torusPlanarPullback_translate]
    exact ht

lemma bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_finiteExpanded
    (L alpha n : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    bdcTorusThinCrossingTranslationClosure L alpha n omega ↔
      torusPlanarPullback L omega ∈
        bdcLongRectangleTorusTranslationExpandedUnion L alpha n := by
  constructor
  · rintro ⟨t, ht⟩
    let u := torusReduceSite L t
    let s := bdcTorusCanonicalShift u
    have htranslate : torusAmbientTranslateConfig L t omega =
        torusAmbientTranslateConfig L s omega := by
      simpa [u, s] using
        torusAmbientTranslateConfig_eq_canonical L t omega
    rw [htranslate] at ht
    obtain ⟨k, hk⟩ := ht
    refine Set.mem_iUnion.2 ⟨(u, k), ?_⟩
    change translateConfig s (torusPlanarPullback L omega) ∈
      bdcLongRectangleEvent alpha n k
    rw [← torusPlanarPullback_translate]
    exact hk
  · intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
    refine ⟨bdcTorusCanonicalShift j.1, ⟨j.2, ?_⟩⟩
    change translateConfig (bdcTorusCanonicalShift j.1)
      (torusPlanarPullback L omega) ∈
        bdcLongRectangleEvent alpha n j.2 at hj
    rw [torusPlanarPullback_translate]
    exact hj

local instance thinTranslationClosureCounterexample_eightFact :
    Fact (2 < (8 : ℕ)) := ⟨by norm_num⟩

/-! ## C. Counterexample on the 8-torus -/

/-- An explicit configuration on the 8-torus in the translation closure but without a coarse thin
  crossing. -/
noncomputable def thinTranslationClosureCounterexampleConfig :
    TorusAmbientConfig 8 :=
  fun e =>
    match (torusEdgeCodeEquiv 8).symm e with
    | ((_, _), TorusEdgeOrientation.horizontal) => false
    | ((x, y), TorusEdgeOrientation.vertical) =>
        decide (x = 0 ∧ (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4))

@[simp] lemma thinTranslationClosureCounterexampleConfig_horizontal
    (x y : ZMod 8) :
    thinTranslationClosureCounterexampleConfig
        (torusHorizontalEdge 8 x y) = false := by
  have hcode : (torusEdgeCodeEquiv 8).symm
      (torusHorizontalEdge 8 x y) =
        ((x, y), TorusEdgeOrientation.horizontal) := by
    apply (torusEdgeCodeEquiv 8).injective
    simp [torusEdgeCodeEquiv_apply, torusEdgeOfCode]
  rw [thinTranslationClosureCounterexampleConfig, hcode]

@[simp] lemma thinTranslationClosureCounterexampleConfig_vertical
    (x y : ZMod 8) :
    thinTranslationClosureCounterexampleConfig
        (torusVerticalEdge 8 x y) =
      decide (x = 0 ∧ (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4)) := by
  have hcode : (torusEdgeCodeEquiv 8).symm
      (torusVerticalEdge 8 x y) =
        ((x, y), TorusEdgeOrientation.vertical) := by
    apply (torusEdgeCodeEquiv 8).injective
    simp [torusEdgeCodeEquiv_apply, torusEdgeOfCode]
  rw [thinTranslationClosureCounterexampleConfig, hcode]

lemma thinTranslationClosureCounterexample_translated_open
    (y : ℤ) (hy0 : 0 ≤ y) (hy3 : y ≤ 3) :
    IsOpenEdge 2
      (torusPlanarPullback 8
        (torusAmbientTranslateConfig 8 ![0, 1]
          thinTranslationClosureCounterexampleConfig))
      ![0, y] ![0, y + 1] := by
  rw [torusPlanarPullback_translate]
  refine ⟨vadj_step 0 y, ?_⟩
  change torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
    (Sym2.map (fun x => x + ![0, 1]) s(![0, y], ![0, y + 1])) = true
  rw [Sym2.map_mk]
  have hopen : torusPlanarPullback 8
      thinTranslationClosureCounterexampleConfig
        s(![0, y + 1], ![0, (y + 1) + 1]) = true := by
    rw [torusPlanarPullback_vertical,
      thinTranslationClosureCounterexampleConfig_vertical,
      decide_eq_true_eq]
    constructor
    · norm_num
    · interval_cases y <;> norm_num
  simpa using hopen

lemma thinTranslationClosureCounterexample_translated_crossing :
    VerticalCrossing
      (torusPlanarPullback 8
        (torusAmbientTranslateConfig 8 ![0, 1]
          thinTranslationClosureCounterexampleConfig))
      0 2 0 4 := by
  let omega := torusPlanarPullback 8
    (torusAmbientTranslateConfig 8 ![0, 1]
      thinTranslationClosureCounterexampleConfig)
  let v0 : (rect 0 2 0 4 : Set (Site 2)) :=
    ⟨![0, 0], by simp [mem_rect]⟩
  let v1 : (rect 0 2 0 4 : Set (Site 2)) :=
    ⟨![0, 1], by simp [mem_rect]⟩
  let v2 : (rect 0 2 0 4 : Set (Site 2)) :=
    ⟨![0, 2], by simp [mem_rect]⟩
  let v3 : (rect 0 2 0 4 : Set (Site 2)) :=
    ⟨![0, 3], by simp [mem_rect]⟩
  let v4 : (rect 0 2 0 4 : Set (Site 2)) :=
    ⟨![0, 4], by simp [mem_rect]⟩
  have h01 : (openSubgraphInduce 2 omega (rect 0 2 0 4)).Adj v0 v1 := by
    rw [openSubgraphInduce_adj, openSubgraph_adj]
    simpa [omega, v0, v1] using
      (thinTranslationClosureCounterexample_translated_open 0
        (by norm_num) (by norm_num)).2
  have h12 : (openSubgraphInduce 2 omega (rect 0 2 0 4)).Adj v1 v2 := by
    rw [openSubgraphInduce_adj, openSubgraph_adj]
    simpa [omega, v1, v2] using
      (thinTranslationClosureCounterexample_translated_open 1
        (by norm_num) (by norm_num)).2
  have h23 : (openSubgraphInduce 2 omega (rect 0 2 0 4)).Adj v2 v3 := by
    rw [openSubgraphInduce_adj, openSubgraph_adj]
    simpa [omega, v2, v3] using
      (thinTranslationClosureCounterexample_translated_open 2
        (by norm_num) (by norm_num)).2
  have h34 : (openSubgraphInduce 2 omega (rect 0 2 0 4)).Adj v3 v4 := by
    rw [openSubgraphInduce_adj, openSubgraph_adj]
    simpa [omega, v3, v4] using
      (thinTranslationClosureCounterexample_translated_open 3
        (by norm_num) (by norm_num)).2
  refine ⟨⟨![0, 0], by simp [bottomSide, mem_rect]⟩,
    ⟨![0, 4], by simp [topSide, mem_rect]⟩, ?_⟩
  have hconn : ConnectedWithin 2 omega (rect 0 2 0 4) v0 v4 :=
    h01.reachable.trans (h12.reachable.trans
      (h23.reachable.trans h34.reachable))
  simpa [omega, v0, v4] using hconn

lemma thinTranslationClosureCounterexample_mem_closure :
    bdcTorusThinCrossingTranslationClosure 8 2 1
      thinTranslationClosureCounterexampleConfig := by
  refine ⟨![0, 1], ?_⟩
  refine ⟨bdcLongRectangleOriginIndex 2 (by norm_num), ?_⟩
  simpa [bdcLongRectangleXOffset, bdcLongRectangleYOffset,
    bdcLongRectangleOriginIndex] using
    thinTranslationClosureCounterexample_translated_crossing

lemma thinTranslationClosureCounterexample_vertical_iff (x y : ℤ) :
    torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
        s(![x, y], ![x, y + 1]) = true ↔
      (x : ZMod 8) = 0 ∧
        ((y : ZMod 8) = 1 ∨ (y : ZMod 8) = 2 ∨
          (y : ZMod 8) = 3 ∨ (y : ZMod 8) = 4) := by
  rw [torusPlanarPullback_vertical,
    thinTranslationClosureCounterexampleConfig_vertical,
    decide_eq_true_eq]

lemma thinTranslationClosureCounterexample_cut_step
    {a c h : ℤ} {p q : Site 2}
    (hp : p ∈ rect a (a + 2) c (c + 4))
    (hq : q ∈ rect a (a + 2) c (c + 4))
    (hadj : (hypercubicLattice 2).Adj p q)
    (hopen : torusPlanarPullback 8
      thinTranslationClosureCounterexampleConfig s(p, q) = true)
    (hple : p 1 ≤ h)
    (hclosed : ∀ x : ℤ,
      torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
        s(![x, h], ![x, h + 1]) ≠ true) :
    q 1 ≤ h := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  rw [mem_rect] at hp hq
  by_contra hqle
  push Not at hqle
  have hp1 : p 1 = h := by omega
  have hq1 : q 1 = h + 1 := by omega
  have hpq0 : p 0 = q 0 := by omega
  have hpe : p = ![p 0, h] := by
    funext i
    fin_cases i <;> simp [hp1]
  have hqe : q = ![p 0, h + 1] := by
    funext i
    fin_cases i <;> simp [hpq0.symm, hq1]
  apply hclosed (p 0)
  rw [hpe, hqe] at hopen
  simpa using hopen

lemma thinTranslationClosureCounterexample_cut_walk
    {a c h : ℤ}
    (hclosed : ∀ x : ℤ,
      torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
        s(![x, h], ![x, h + 1]) ≠ true)
    {p q : (rect a (a + 2) c (c + 4) : Set (Site 2))}
    (w : (openSubgraphInduce 2
      (torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig)
      (rect a (a + 2) c (c + 4))).Walk p q)
    (hp : (p : Site 2) 1 ≤ h) :
    (q : Site 2) 1 ≤ h := by
  induction w with
  | nil => exact hp
  | @cons u v z huv _ ih =>
      rw [openSubgraphInduce_adj, openSubgraph_adj] at huv
      exact ih (thinTranslationClosureCounterexample_cut_step
        u.2 v.2 huv.1 huv.2 hp hclosed)

lemma thinTranslationClosureCounterexample_no_vertical_of_cut
    {a c h : ℤ} (hch : c ≤ h) (hhc : h < c + 4)
    (hclosed : ∀ x : ℤ,
      torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
        s(![x, h], ![x, h + 1]) ≠ true) :
    ¬ VerticalCrossing
      (torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig)
      a (a + 2) c (c + 4) := by
  rintro ⟨p, q, hpq⟩
  have hp1 : (p : Site 2) 1 = c := p.2.2
  have hq1 : (q : Site 2) 1 = c + 4 := q.2.2
  have hbound := thinTranslationClosureCounterexample_cut_walk hclosed hpq.some
    (by rw [hp1]; exact hch)
  rw [hq1] at hbound
  omega

lemma thinTranslationClosureCounterexample_cut_zero (x : ℤ) :
    torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
      s(![x, 0], ![x, 1]) ≠ true := by
  intro hopen
  have h := (thinTranslationClosureCounterexample_vertical_iff x 0).mp hopen
  rcases h.2 with h | h | h | h
  · exact (by decide : (0 : ZMod 8) ≠ 1) h
  · exact (by decide : (0 : ZMod 8) ≠ 2) h
  · exact (by decide : (0 : ZMod 8) ≠ 3) h
  · exact (by decide : (0 : ZMod 8) ≠ 4) h

lemma thinTranslationClosureCounterexample_cut_five (x : ℤ) :
    torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig
      s(![x, 5], ![x, 6]) ≠ true := by
  intro hopen
  have h := (thinTranslationClosureCounterexample_vertical_iff x 5).mp hopen
  rcases h.2 with h | h | h | h
  · exact (by decide : (5 : ZMod 8) ≠ 1) h
  · exact (by decide : (5 : ZMod 8) ≠ 2) h
  · exact (by decide : (5 : ZMod 8) ≠ 3) h
  · exact (by decide : (5 : ZMod 8) ≠ 4) h

lemma thinTranslationClosureCounterexample_not_coarse :
    ¬ bdcTorusThinCrossing 8 2 1
      thinTranslationClosureCounterexampleConfig := by
  rintro ⟨k, hk⟩
  let a : ℤ := bdcLongRectangleXOffset 1 k
  let c : ℤ := bdcLongRectangleYOffset 1 k
  change VerticalCrossing
    (torusPlanarPullback 8 thinTranslationClosureCounterexampleConfig)
      a (a + 2) c (c + 4) at hk
  have hc : c = 0 ∨ c = 4 := by
    simp [c, bdcLongRectangleYOffset]
    omega
  rcases hc with hc | hc
  · rw [hc] at hk
    apply thinTranslationClosureCounterexample_no_vertical_of_cut
      (a := a) (c := 0) (h := 0)
      (by norm_num) (by norm_num)
      thinTranslationClosureCounterexample_cut_zero
    simpa [a] using hk
  · rw [hc] at hk
    apply thinTranslationClosureCounterexample_no_vertical_of_cut
      (a := a) (c := 4) (h := 5)
      (by norm_num) (by norm_num)
      thinTranslationClosureCounterexample_cut_five
    simpa [a] using hk

lemma thinTranslationClosureCounterexample_closure_not_coarse :
    bdcTorusThinCrossingTranslationClosure 8 2 1
        thinTranslationClosureCounterexampleConfig ∧
      ¬ bdcTorusThinCrossing 8 2 1
        thinTranslationClosureCounterexampleConfig :=
  ⟨thinTranslationClosureCounterexample_mem_closure,
    thinTranslationClosureCounterexample_not_coarse⟩

/-- Refutation of the coarse cover at `(8, 2, 1)`. -/
theorem not_translationClosure_coarseCover_two_one :
    ¬ BdcTorusWindingToThinCover 8 2 1
      (bdcTorusThinCrossingTranslationClosureEvent 8 2 1) := by
  intro h
  exact thinTranslationClosureCounterexample_not_coarse
    (h.toThin thinTranslationClosureCounterexampleConfig
      thinTranslationClosureCounterexample_mem_closure)

end StatMech.BeffaraDC
