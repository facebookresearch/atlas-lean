/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.GlobalAssembly

/-!
# Contradictions from primal and dual crossing limits in rectangle arrays

Along a finite array of rectangles, crossing probabilities cannot switch from vertical to
horizontal while every adjacent pair and every dual rectangle has a crossing limit equal to one.

## i. Overview

The first group of results is real analysis on arrays of numbers in `[0, 1]`. Index rectangles
by `k ≤ K n + 1`. If the vertical crossing probability of rectangle `0` tends to one, the
horizontal crossing probability of rectangle `K n + 1` tends to one, and for every choice of
index `k n` the larger of "horizontal at `k`" and "vertical at `k + 1`" tends to one while the
smaller of the two crossings of each rectangle tends to zero, one obtains a contradiction by
following the first index at which the horizontal crossing becomes large. The dual version
replaces the vanishing minima by dual crossing limits and the complementarity
`primal + dual ≤ 1` (a primal horizontal crossing and a dual vertical crossing of the same
rectangle are disjoint events).

`branchAlignedComplementaryLimits_false` and `balancedAdjacentSelectorsComplementary_false`
are the same exclusion for one rectangle and for two adjacent rectangles with a balance error.

`PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_max_limits` is the geometric form:
for rectangles whose sides exceed ten edge-arc lengths, primal crossing limits along adjacent
pairs and dual crossing limits on every rectangle are incompatible, because the primal and dual
crossings of the slightly shrunken rectangles exclude each other.

Headline fidelity: all five results conclude `False`. They are unconditional statements that the
listed limits are jointly impossible; they are used as the closing step of contradiction
arguments elsewhere.

## ii. Key results

- `adjacent_height_array_contradiction_of_endpoint_and_uniform_limits`
- `adjacent_height_array_contradiction_of_primal_dual_limits`
- `PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_max_limits`

## iii. Table of contents

- A. Arrays of numbers
- B. Exclusion for one and two rectangles
- C. Arrays with dual limits
- D. Arrays of drawn rectangles

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Topology

namespace StatMech.FK.PeriodicPlanar

/-! ## A. Arrays of numbers -/

/-- Real-number array contradiction: vertical values starting near one, horizontal values ending
near one, adjacent maxima `max (horizontal k) (vertical (k + 1))` tending to one and each
rectangle's minimum `min (vertical k) (horizontal k)` tending to zero, uniformly over index
sequences, cannot all hold. -/
lemma adjacent_height_array_contradiction_of_endpoint_and_uniform_limits
    (horizontal vertical : Nat -> Nat -> Real) (K : Nat -> Nat)
    (hhorizontal_nonneg : forall n k, 0 <= horizontal n k)
    (hvertical_nonneg : forall n k, 0 <= vertical n k)
    (hhorizontal_le_one : forall n k, horizontal n k <= 1)
    (hvertical_le_one : forall n k, vertical n k <= 1)
    (hvertical_start : Tendsto (fun n => vertical n 0) atTop (nhds 1))
    (hhorizontal_end : Tendsto
      (fun n => horizontal n (K n + 1)) atTop (nhds 1))
    (hlimits : forall k : Nat -> Nat,
      (forall n, k n < K n + 1) ->
        Tendsto (fun n => max
          (horizontal n (k n)) (vertical n (k n + 1)))
          atTop (nhds 1) /\
        Tendsto (fun n => min
          (vertical n (k n)) (horizontal n (k n)))
          atTop (nhds 0) /\
        Tendsto (fun n => min
          (vertical n (k n + 1)) (horizontal n (k n + 1)))
          atTop (nhds 0)) : False := by
  let error : Nat -> Real := fun n =>
    max (1 - vertical n 0) (1 - horizontal n (K n + 1))
  have herror_nonneg : forall n, 0 <= error n := by
    intro n
    exact (sub_nonneg.mpr (hvertical_le_one n 0)).trans (le_max_left _ _)
  have herror : Tendsto error atTop (nhds 0) := by
    have hv : Tendsto (fun n => 1 - vertical n 0) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hvertical_start
    have hh : Tendsto (fun n => 1 - horizontal n (K n + 1))
        atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds (x := (1 : Real))).sub hhorizontal_end
    simpa [error] using hv.max hh
  have hstart : forall n,
      horizontal n 0 <= vertical n 0 + error n := by
    intro n
    have herr : 1 - vertical n 0 <= error n := le_max_left _ _
    linarith [hhorizontal_le_one n 0]
  have hend : forall n,
      vertical n (K n + 1) <=
        horizontal n (K n + 1) + error n := by
    intro n
    have herr : 1 - horizontal n (K n + 1) <= error n :=
      le_max_right _ _
    linarith [hvertical_le_one n (K n + 1)]
  exact approximate_balanced_height_sequence_contradiction
    horizontal vertical error K hhorizontal_nonneg hvertical_nonneg
    herror_nonneg herror hstart hend hlimits

/-! ## B. Exclusion for one and two rectangles -/

/-- If the primal branch selected by `branch n` and the dual branch of the opposite orientation both
tend to one, the complementarity bounds `H + dualV ≤ 1` and `V + dualH ≤ 1` give a contradiction. -/
lemma branchAlignedComplementaryLimits_false
    (branch : Nat -> Bool) (H V dualV dualH : Nat -> Real)
    (hHdual : forall n, H n + dualV n <= 1)
    (hVdual : forall n, V n + dualH n <= 1)
    (hprimal : Tendsto (fun n => if branch n then V n else H n)
      atTop (nhds 1))
    (hdual : Tendsto (fun n => if branch n then dualH n else dualV n)
      atTop (nhds 1)) : False := by
  let selectedPrimal : Nat -> Real := fun n =>
    if branch n then V n else H n
  let selectedDual : Nat -> Real := fun n =>
    if branch n then dualH n else dualV n
  have hsum (n : Nat) : selectedPrimal n + selectedDual n <= 1 := by
    cases hbranch : branch n
    · simpa [selectedPrimal, selectedDual, hbranch] using hHdual n
    · simpa [selectedPrimal, selectedDual, hbranch] using hVdual n
  have htwo : Tendsto (fun n => selectedPrimal n + selectedDual n)
      atTop (nhds 2) := by
    convert hprimal.add hdual using 1
    norm_num [selectedPrimal, selectedDual]
  have heventually : ∀ᶠ n in atTop,
      (3 / 2 : Real) < selectedPrimal n + selectedDual n :=
    (tendsto_order.1 htwo).1 (3 / 2) (by norm_num)
  obtain ⟨n, hn⟩ := heventually.exists
  linarith [hsum n]

/-- Two adjacent rectangles with balanced primal crossings (up to a vanishing error), a primal
adjacent limit `max (H0 n) (V1 n) → 1`, dual limits on both rectangles and the four complementarity
bounds give a contradiction. -/
lemma balancedAdjacentSelectorsComplementary_false
    (H0 V0 H1 V1 dualV0 dualH0 dualV1 dualH1 error : Nat -> Real)
    (hH0_nonneg : forall n, 0 <= H0 n)
    (hV0_nonneg : forall n, 0 <= V0 n)
    (hH1_nonneg : forall n, 0 <= H1 n)
    (hV1_nonneg : forall n, 0 <= V1 n)
    (hH0_le_one : forall n, H0 n <= 1)
    (hV0_le_one : forall n, V0 n <= 1)
    (hH1_le_one : forall n, H1 n <= 1)
    (hV1_le_one : forall n, V1 n <= 1)
    (hbalance : forall n, H0 n <= V0 n + error n)
    (hnext : forall n, V1 n <= H1 n + error n)
    (herror : Tendsto error atTop (nhds 0))
    (hadjacent : Tendsto (fun n => max (H0 n) (V1 n))
      atTop (nhds 1))
    (hdual0 : Tendsto (fun n => max (dualV0 n) (dualH0 n))
      atTop (nhds 1))
    (hdual1 : Tendsto (fun n => max (dualV1 n) (dualH1 n))
      atTop (nhds 1))
    (hmatchH0 : forall n, H0 n + dualV0 n <= 1)
    (hmatchV0 : forall n, V0 n + dualH0 n <= 1)
    (hmatchH1 : forall n, H1 n + dualV1 n <= 1)
    (hmatchV1 : forall n, V1 n + dualH1 n <= 1) : False := by
  let levelBranch : Nat -> Bool := fun n => decide (H0 n <= V1 n)
  let primary : Nat -> Real := fun n =>
    if levelBranch n then V1 n else H0 n
  let companion : Nat -> Real := fun n =>
    if levelBranch n then H1 n else V0 n
  have hprimary_eq (n : Nat) : primary n = max (H0 n) (V1 n) := by
    by_cases h : H0 n <= V1 n
    · simp [primary, levelBranch, h]
    · simp [primary, levelBranch, h, max_eq_left (le_of_not_ge h)]
  have hprimary : Tendsto primary atTop (nhds 1) := by
    apply hadjacent.congr'
    filter_upwards [] with n
    exact (hprimary_eq n).symm
  have hprimary_le_companion_add (n : Nat) :
      primary n <= companion n + error n := by
    by_cases h : H0 n <= V1 n
    · simpa [primary, companion, levelBranch, h] using hnext n
    · simpa [primary, companion, levelBranch, h] using hbalance n
  have hcompanion_le_one (n : Nat) : companion n <= 1 := by
    by_cases h : H0 n <= V1 n
    · simpa [companion, levelBranch, h] using hH1_le_one n
    · simpa [companion, levelBranch, h] using hV0_le_one n
  have hcompanion : Tendsto companion atTop (nhds 1) := by
    have hlower : Tendsto (fun n => primary n - error n)
        atTop (nhds 1) := by
      simpa using hprimary.sub herror
    apply hlower.squeeze tendsto_const_nhds
    · intro n
      linarith [hprimary_le_companion_add n]
    · exact hcompanion_le_one
  let selectedH : Nat -> Real := fun n =>
    if levelBranch n then H1 n else H0 n
  let selectedV : Nat -> Real := fun n =>
    if levelBranch n then V1 n else V0 n
  let selectedDualV : Nat -> Real := fun n =>
    if levelBranch n then dualV1 n else dualV0 n
  let selectedDualH : Nat -> Real := fun n =>
    if levelBranch n then dualH1 n else dualH0 n
  have hprimaryMin : Tendsto (fun n => min (primary n) (companion n))
      atTop (nhds 1) := by
    simpa only [min_self] using hprimary.min hcompanion
  have hselectedH : Tendsto selectedH atTop (nhds 1) := by
    apply hprimaryMin.squeeze tendsto_const_nhds
    · intro n
      cases hlevel : levelBranch n
      · simp [selectedH, primary, companion, hlevel]
      · simp [selectedH, primary, companion, hlevel]
    · intro n
      cases hlevel : levelBranch n
      · simpa [selectedH, hlevel] using hH0_le_one n
      · simpa [selectedH, hlevel] using hH1_le_one n
  have hselectedV : Tendsto selectedV atTop (nhds 1) := by
    apply hprimaryMin.squeeze tendsto_const_nhds
    · intro n
      cases hlevel : levelBranch n
      · simp [selectedV, primary, companion, hlevel]
      · simp [selectedV, primary, companion, hlevel]
    · intro n
      cases hlevel : levelBranch n
      · simpa [selectedV, hlevel] using hV0_le_one n
      · simpa [selectedV, hlevel] using hV1_le_one n
  let dualMax0 : Nat -> Real := fun n => max (dualV0 n) (dualH0 n)
  let dualMax1 : Nat -> Real := fun n => max (dualV1 n) (dualH1 n)
  have hdualMin : Tendsto (fun n => min (dualMax0 n) (dualMax1 n))
      atTop (nhds 1) := by
    simpa only [dualMax0, dualMax1, min_self] using hdual0.min hdual1
  have hselectedDualMax : Tendsto (fun n =>
      max (selectedDualV n) (selectedDualH n)) atTop (nhds 1) := by
    apply hdualMin.squeeze tendsto_const_nhds
    · intro n
      cases hlevel : levelBranch n
      · simpa [selectedDualV, selectedDualH, dualMax0, hlevel] using
          min_le_left (dualMax0 n) (dualMax1 n)
      · simpa [selectedDualV, selectedDualH, dualMax1, hlevel] using
          min_le_right (dualMax0 n) (dualMax1 n)
    · intro n
      cases hlevel : levelBranch n
      · simp only [selectedDualV, selectedDualH, hlevel, Bool.false_eq_true,
          ↓reduceIte]
        apply max_le <;> linarith [hmatchH0 n, hmatchV0 n,
          hH0_nonneg n, hV0_nonneg n]
      · simp only [selectedDualV, selectedDualH, hlevel, ↓reduceIte]
        apply max_le <;> linarith [hmatchH1 n, hmatchV1 n,
          hH1_nonneg n, hV1_nonneg n]
  let dualBranch : Nat -> Bool := fun n =>
    decide (selectedDualV n <= selectedDualH n)
  have hdualSelected : Tendsto (fun n => if dualBranch n then
      selectedDualH n else selectedDualV n) atTop (nhds 1) := by
    apply hselectedDualMax.congr'
    filter_upwards [] with n
    by_cases h : selectedDualV n <= selectedDualH n
    · simp [dualBranch, h]
    · simp [dualBranch, h, max_eq_left (le_of_not_ge h)]
  have hselectedMin : Tendsto (fun n => min (selectedH n) (selectedV n))
      atTop (nhds 1) := by
    simpa only [min_self] using hselectedH.min hselectedV
  have hprimalSelected : Tendsto (fun n => if dualBranch n then
      selectedV n else selectedH n) atTop (nhds 1) := by
    apply hselectedMin.squeeze tendsto_const_nhds
    · intro n
      cases hdual : dualBranch n
      · simp [hdual]
      · simp [hdual]
    · intro n
      cases hlevel : levelBranch n <;> cases hdual : dualBranch n
      · simpa [selectedH, hlevel, hdual] using hH0_le_one n
      · simpa [selectedV, hlevel, hdual] using hV0_le_one n
      · simpa [selectedH, hlevel, hdual] using hH1_le_one n
      · simpa [selectedV, hlevel, hdual] using hV1_le_one n
  apply branchAlignedComplementaryLimits_false dualBranch
    selectedH selectedV selectedDualV selectedDualH
  · intro n
    cases hlevel : levelBranch n
    · simpa [selectedH, selectedDualV, hlevel] using hmatchH0 n
    · simpa [selectedH, selectedDualV, hlevel] using hmatchH1 n
  · intro n
    cases hlevel : levelBranch n
    · simpa [selectedV, selectedDualH, hlevel] using hmatchV0 n
    · simpa [selectedV, selectedDualH, hlevel] using hmatchV1 n
  · exact hprimalSelected
  · exact hdualSelected

/-! ## C. Arrays with dual limits -/

/-- Array contradiction with dual limits: the hypotheses of
`adjacent_height_array_contradiction_of_endpoint_and_uniform_limits` with the vanishing minima
replaced by dual crossing limits on every rectangle and complementarity `primal + dual ≤ 1`. See
also `adjacent_height_array_contradiction_of_primal_dual_bounded_limits` (stronger: dual limits only
for indices `≤ K n + 1`). -/
lemma adjacent_height_array_contradiction_of_primal_dual_limits
    (horizontal vertical dualVertical dualHorizontal : Nat -> Nat -> Real)
    (K : Nat -> Nat)
    (hhorizontal_nonneg : forall n k, 0 <= horizontal n k)
    (hvertical_nonneg : forall n k, 0 <= vertical n k)
    (hhorizontal_le_one : forall n k, horizontal n k <= 1)
    (hvertical_le_one : forall n k, vertical n k <= 1)
    (hvertical_start : Tendsto (fun n => vertical n 0) atTop (nhds 1))
    (hhorizontal_end : Tendsto
      (fun n => horizontal n (K n + 1)) atTop (nhds 1))
    (hmatchHorizontal : forall n k,
      horizontal n k + dualVertical n k <= 1)
    (hmatchVertical : forall n k,
      vertical n k + dualHorizontal n k <= 1)
    (hprimalLimits : forall k : Nat -> Nat,
      (forall n, k n < K n + 1) ->
        Tendsto (fun n => max
          (horizontal n (k n)) (vertical n (k n + 1)))
          atTop (nhds 1))
    (hdualLimits : forall k : Nat -> Nat,
      Tendsto (fun n => max
        (dualVertical n (k n)) (dualHorizontal n (k n)))
        atTop (nhds 1)) : False := by
  let error : Nat -> Real := fun n =>
    max (1 - vertical n 0) (1 - horizontal n (K n + 1))
  have herror_nonneg : forall n, 0 <= error n := by
    intro n
    exact (sub_nonneg.mpr (hvertical_le_one n 0)).trans (le_max_left _ _)
  have herror : Tendsto error atTop (nhds 0) := by
    have hv : Tendsto (fun n => 1 - vertical n 0) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : Real))).sub hvertical_start
    have hh : Tendsto (fun n => 1 - horizontal n (K n + 1))
        atTop (nhds 0) := by
      simpa using
        (tendsto_const_nhds (x := (1 : Real))).sub hhorizontal_end
    simpa [error] using hv.max hh
  have hstart : forall n,
      horizontal n 0 <= vertical n 0 + error n := by
    intro n
    have herr : 1 - vertical n 0 <= error n := le_max_left _ _
    linarith [hhorizontal_le_one n 0]
  have hend : forall n,
      vertical n (K n + 1) <= horizontal n (K n + 1) + error n := by
    intro n
    have herr : 1 - horizontal n (K n + 1) <= error n :=
      le_max_right _ _
    linarith [hvertical_le_one n (K n + 1)]
  obtain ⟨k, hk⟩ := exists_adjacent_approximate_balanced_height_sequence
    horizontal vertical error K herror_nonneg hstart hend
  apply balancedAdjacentSelectorsComplementary_false
    (fun n => horizontal n (k n))
    (fun n => vertical n (k n))
    (fun n => horizontal n (k n + 1))
    (fun n => vertical n (k n + 1))
    (fun n => dualVertical n (k n))
    (fun n => dualHorizontal n (k n))
    (fun n => dualVertical n (k n + 1))
    (fun n => dualHorizontal n (k n + 1)) error
  · exact fun n => hhorizontal_nonneg n (k n)
  · exact fun n => hvertical_nonneg n (k n)
  · exact fun n => hhorizontal_nonneg n (k n + 1)
  · exact fun n => hvertical_nonneg n (k n + 1)
  · exact fun n => hhorizontal_le_one n (k n)
  · exact fun n => hvertical_le_one n (k n)
  · exact fun n => hhorizontal_le_one n (k n + 1)
  · exact fun n => hvertical_le_one n (k n + 1)
  · exact fun n => (hk n).2.1
  · exact fun n => (hk n).2.2
  · exact herror
  · exact hprimalLimits k (fun n => (hk n).1)
  · exact hdualLimits k
  · exact hdualLimits (fun n => k n + 1)
  · exact fun n => hmatchHorizontal n (k n)
  · exact fun n => hmatchVertical n (k n)
  · exact fun n => hmatchHorizontal n (k n + 1)
  · exact fun n => hmatchVertical n (k n + 1)

/-! ## D. Arrays of drawn rectangles -/

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

/-- For an array of drawn rectangles, primal start and end crossings tending to one, primal
adjacent-pair maxima tending to one and dual crossing maxima tending to one on every rectangle are
incompatible. See also
`PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_bounded_max_limits` (stronger: dual
limits only for indices `≤ K n + 1`). -/
lemma PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_max_limits
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    {B : Real} (hBpos : 0 < B)
    (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
    (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
    (a b c d : Nat -> Nat -> Real) (K : Nat -> Nat)
    (hspanX : ∀ n k, a n k + 5 * B < b n k - 5 * B)
    (hspanY : ∀ n k, c n k + 5 * B < d n k - 5 * B)
    (hvertical_start : Tendsto (fun n => mu.real
      (D.primalEmbedding.verticalCrossingEvent
        (a n 0 + 4 * B) (b n 0 - 4 * B) (c n 0) (d n 0)))
      atTop (nhds 1))
    (hhorizontal_end : Tendsto (fun n => mu.real
      (D.primalEmbedding.horizontalCrossingEvent
        (a n (K n + 1)) (b n (K n + 1))
        (c n (K n + 1) + 4 * B) (d n (K n + 1) - 4 * B)))
      atTop (nhds 1))
    (hprimalLimits : ∀ k : Nat -> Nat,
      (∀ n, k n < K n + 1) -> Tendsto (fun n => max
        (mu.real (D.primalEmbedding.horizontalCrossingEvent
          (a n (k n)) (b n (k n))
          (c n (k n) + 4 * B) (d n (k n) - 4 * B)))
        (mu.real (D.primalEmbedding.verticalCrossingEvent
          (a n (k n + 1) + 4 * B) (b n (k n + 1) - 4 * B)
          (c n (k n + 1)) (d n (k n + 1)))))
        atTop (nhds 1))
    (hdualLimits : ∀ k : Nat -> Nat, Tendsto (fun n => max
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (a n (k n) + 4 * B) (b n (k n) - 4 * B)
          (c n (k n)) (d n (k n))))
      (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.horizontalCrossingEvent
          (a n (k n)) (b n (k n))
          (c n (k n) + 4 * B) (d n (k n) - 4 * B))))
      atTop (nhds 1)) : False := by
  let horizontal : Nat -> Nat -> Real := fun n k => mu.real
    (D.primalEmbedding.horizontalCrossingEvent
      (a n k) (b n k) (c n k + 4 * B) (d n k - 4 * B))
  let vertical : Nat -> Nat -> Real := fun n k => mu.real
    (D.primalEmbedding.verticalCrossingEvent
      (a n k + 4 * B) (b n k - 4 * B) (c n k) (d n k))
  let dualVertical : Nat -> Nat -> Real := fun n k => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (a n k + 4 * B) (b n k - 4 * B) (c n k) (d n k))
  let dualHorizontal : Nat -> Nat -> Real := fun n k => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (a n k) (b n k) (c n k + 4 * B) (d n k - 4 * B))
  apply adjacent_height_array_contradiction_of_primal_dual_limits
    horizontal vertical dualVertical dualHorizontal K
  · exact fun _ _ => measureReal_nonneg
  · exact fun _ _ => measureReal_nonneg
  · exact fun _ _ => measureReal_le_one
  · exact fun _ _ => measureReal_le_one
  · simpa only [vertical] using hvertical_start
  · simpa only [horizontal] using hhorizontal_end
  · intro n k
    exact D.matchedCrossing_measureReal_add_le_one mu hBpos hBp hBd
      (hspanX n k) (hspanY n k)
  · intro n k
    exact D.matchedVerticalHorizontalCrossing_measureReal_add_le_one
      mu hBpos hBp hBd (hspanX n k) (hspanY n k)
  · intro k hk
    simpa only [horizontal, vertical] using hprimalLimits k hk
  · intro k
    simpa only [dualVertical, dualHorizontal] using hdualLimits k

end StatMech.FK.PeriodicPlanar
