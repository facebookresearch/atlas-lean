/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldDualTranslated
import Code.FK.PeriodicPlanarSheffieldRotated










open Filter MeasureTheory Set SimpleGraph Topology

namespace StatMech.FK.PeriodicPlanar



theorem exists_adjacent_balanced_height_sequence
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



theorem exists_adjacent_approximate_balanced_height_sequence
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
