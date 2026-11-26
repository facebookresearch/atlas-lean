/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DualTranslated
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Rotated

/-!
# Balanced aspect ratios for rectangle crossings

A discrete intermediate-value argument over a family of rectangle heights, and the
contradiction it yields with a crossing dichotomy.

## i. Overview

Fix, for every scale `n`, a finite family of rectangles indexed by a height parameter
`k = 0, …, K n + 1`, with horizontal and vertical crossing probabilities `horizontal n k` and
`vertical n k`. If the shortest rectangle favors vertical crossings (`horizontal n 0 ≤
vertical n 0`) and the tallest favors horizontal ones, then some adjacent pair `k n, k n + 1`
switches preference. The approximate version allows an error `error n` in both comparisons.

At such a balanced pair, the rectangle `k n` is crossed horizontally about as often as
vertically, and so is `k n + 1` with the roles reversed. If, in addition, at every balanced pair
the larger crossing probability tends to `1` while the smaller ones tend to `0` (the
"one direction wins" dichotomy), the two statements are incompatible. This is the aspect-ratio
balancing step in Sheffield's proof that, for a translation-invariant FK measure on a periodic
planar graph, an infinite primal cluster and an infinite dual cluster cannot both be unique.

All three results are elementary and proved unconditionally from their stated hypotheses.

## ii. Key results

- `exists_adjacent_approximate_balanced_height_sequence` : an adjacent pair of heights at which
  the preference switches, up to an error, chosen for every scale.
- `approximate_balanced_height_sequence_contradiction` : the crossing dichotomy at every
  balanced pair, together with a vanishing error, is contradictory. Proved unconditionally;
  its `hlimits` hypothesis is the dichotomy that callers must supply.

## iii. Table of contents

- A. Adjacent crossover of a height sequence
- B. Contradiction with the crossing dichotomy

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar

/-! ## A. Adjacent crossover of a height sequence -/

/-- Discrete intermediate-value step, exact version: if at every scale `n` the first height favors
vertical crossings and height `K n + 1` favors horizontal ones, there is an adjacent pair
`k n, k n + 1` at which the preference switches. The single-sequence version is
`exists_adjacent_preference_crossover`. -/
lemma exists_adjacent_balanced_height_sequence
    (horizontal vertical : Nat → Nat → Real) (K : Nat → Nat)
    (hstart : ∀ n, horizontal n 0 ≤ vertical n 0)
    (hend : ∀ n,
      vertical n (K n + 1) ≤ horizontal n (K n + 1)) :
    ∃ k : Nat → Nat, ∀ n,
      k n < K n + 1 ∧
      horizontal n (k n) ≤ vertical n (k n) ∧
      vertical n (k n + 1) ≤ horizontal n (k n + 1) := by
  choose k hk using fun n =>
    exists_adjacent_preference_crossover
      (vertical n) (horizontal n) 0 (K n)
        (hstart n) (by simpa using hend n)
  refine ⟨k, fun n => ⟨?_, (hk n).2.2.1, (hk n).2.2.2⟩⟩
  simpa using (hk n).2.1

/-- Discrete intermediate-value step with an error: the version of
`exists_adjacent_balanced_height_sequence` where every comparison holds up to `error n`. See also
`exists_adjacent_approximate_preference_crossover`, its single-sequence form. -/
lemma exists_adjacent_approximate_balanced_height_sequence
    (horizontal vertical : Nat → Nat → Real)
    (error : Nat → Real) (K : Nat → Nat)
    (herror : ∀ n, 0 ≤ error n)
    (hstart : ∀ n,
      horizontal n 0 ≤ vertical n 0 + error n)
    (hend : ∀ n,
      vertical n (K n + 1) ≤
        horizontal n (K n + 1) + error n) :
    ∃ k : Nat → Nat, ∀ n,
      k n < K n + 1 ∧
      horizontal n (k n) ≤ vertical n (k n) + error n ∧
      vertical n (k n + 1) ≤
        horizontal n (k n + 1) + error n := by
  choose k hk using fun n =>
    exists_adjacent_approximate_preference_crossover
      (vertical n) (horizontal n) (error n) 0 (K n)
        (herror n) (hstart n) (by simpa using hend n)
  refine ⟨k, fun n => ⟨?_, (hk n).2.2.1, (hk n).2.2.2⟩⟩
  simpa using (hk n).2.1

/-! ## B. Contradiction with the crossing dichotomy -/

/-- Balanced heights contradict the crossing dichotomy: if the error vanishes and, at every adjacent
pair of heights, the larger crossing probability tends to `1` while the smaller ones tend to `0`,
then the approximately balanced pair of `exists_adjacent_approximate_balanced_height_sequence` gives
a contradiction (Sheffield, *Random Surfaces*, Ch. 9). -/
theorem approximate_balanced_height_sequence_contradiction
    (horizontal vertical : Nat -> Nat -> Real)
    (error : Nat -> Real) (K : Nat -> Nat)
    (hhorizontal : forall n k, 0 <= horizontal n k)
    (hvertical : forall n k, 0 <= vertical n k)
    (herror0 : forall n, 0 <= error n)
    (herror : Tendsto error atTop (nhds 0))
    (hstart : forall n,
      horizontal n 0 <= vertical n 0 + error n)
    (hend : forall n,
      vertical n (K n + 1) <=
        horizontal n (K n + 1) + error n)
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
  obtain ⟨k, hk⟩ := exists_adjacent_approximate_balanced_height_sequence
    horizontal vertical error K herror0 hstart hend
  obtain ⟨hmax, hmin, hminNext⟩ := hlimits k (fun n => (hk n).1)
  exact balanced_aspect_crossing_contradiction_of_error
    (fun n => horizontal n (k n))
    (fun n => vertical n (k n))
    (fun n => horizontal n (k n + 1))
    (fun n => vertical n (k n + 1)) error
    (fun n => hhorizontal n (k n))
    (fun n => hvertical n (k n + 1)) herror0
    (fun n => (hk n).2.1) (fun n => (hk n).2.2)
    herror hmax hmin hminNext

end StatMech.FK.PeriodicPlanar
