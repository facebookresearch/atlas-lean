/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MeteredParkingFunctions
import all MathlibExt.Combinatorics.Enumerative.OneMeteredParkingFunctions

/-!
# Lucky cars in 1-metered parking

A lace starts with a lucky car. Each continuation displaces the next car by one spot, unless
that spot is beyond the end of the street, in which case the car fails and leaves no occupied
spot for the next arrival.

## References

* Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*,
  INTEGERS 25 (2025), Article A73, pp. 1–37, Lemma 1 (pp. 12–13),
  <https://math.colgate.edu/~integers/z73/z73.pdf>. We use the lucky-car formulation, which also
  covers a failed attempt at the last spot.
* S. Alex Bradt, Jennifer Elder, Pamela E. Harris, Gordon Rojas Kirby, Eva Reutercrona, Yuxuan
  (Susan) Wang, and Juliet Whidden, *Unit Interval Parking Functions and the r-Fubini Numbers*,
  La Matematica 3 (2024), pp. 370–384, Definition 2.7, <https://doi.org/10.1007/s44007-024-00089-y>.
* Lucas Chaves Meyles, Pamela E. Harris, Richter Jordaan, Gordon Rojas Kirby, Sam Sehayek, and
  Ethan Spingarn, *Unit-Interval Parking Functions and the Permutohedron*, arXiv:2305.15554
  (2023), Remark 2.7, <https://arxiv.org/abs/2305.15554>.
  The latter two references are credited for related decompositions in Remark 3 of
  *Metered Parking Functions*.
-/

namespace MetaMathlibExt

open meteredParkingCount_one_binet (lastSpot nextSpot meteredOutcome_one_append lastSpot_append
  nextSpot_eq_some_iff)

-- The preference that would extend a block, even if the resulting bump would fail.
private def laceTarget : List ℕ → Option ℕ
  | [] => none
  | [p] => some p
  | p :: q :: rest => some ((p :: q :: rest).getLastD 0 + 1)

private def laceFlags (cs : List (List ℕ)) : List Bool :=
  cs.flatMap fun c => true :: List.replicate (c.length - 1) false

private theorem laceStep_summary (cs : List (List ℕ)) (a : ℕ) :
    let continues := (cs.getLast?.bind laceTarget = some a)
    laceFlags (laceStep cs a) = laceFlags cs ++ [decide (¬continues)] ∧
      (laceStep cs a).getLast?.bind laceTarget = some (if continues then a + 1 else a) := by
  dsimp only
  rcases cs.eq_nil_or_concat with rfl | ⟨cs, c, rfl⟩
  · simp [laceStep, laceFlags, laceTarget]
  · simp only [List.concat_eq_append]
    have hstep : laceStep (cs ++ [c]) a =
        if laceTarget c = some a then cs ++ [c ++ [a]] else (cs ++ [c]) ++ [[a]] := by
      rcases c with _ | ⟨p, _ | ⟨q, rest⟩⟩ <;> simp [laceStep, laceTarget, eq_comm]
    simp only [hstep, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.bind_some]
    split_ifs with hc
    · have hlen : (c ++ [a]).length - 1 = (c.length - 1) + 1 := by
        cases c with
        | nil => simp [laceTarget] at hc
        | cons p rest => simp
      constructor
      · simp only [laceFlags, List.flatMap_append, List.flatMap_singleton, hlen,
          List.replicate_succ', hc, decide_not, decide_true, Bool.not_true, List.cons_append,
          List.append_assoc]
      · simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
          Option.bind_some]
        rcases c with _ | ⟨p, _ | ⟨q, rest⟩⟩
        · simp [laceTarget] at hc
        · rfl
        · change some (((q :: rest) ++ [a]).getLastD 0 + 1) = some (a + 1)
          rw [List.getLastD_concat]
    · have hsingle : laceTarget [a] = some a := rfl
      simp [laceFlags, hc, hsingle]

private theorem luckyFlags_eq_laceFlags {n : ℕ} (L : List ℕ) (hL : ∀ a ∈ L, a < n) :
    (meteredOutcome 1 n L).length = L.length ∧
      (L.zip (meteredOutcome 1 n L)).map (fun p => decide (p.2 = some p.1)) =
        laceFlags (laceDecomposition L) ∧
      lastSpot n L = ((laceDecomposition L).getLast?.bind laceTarget).filter (· < n) := by
  induction L using List.reverseRecOn with
  | nil => simp [meteredOutcome, laceDecomposition, laceFlags, lastSpot]
  | append_singleton L a ih =>
    have ha : a < n := hL a (by simp)
    obtain ⟨hlen, hflags, hspot⟩ := ih fun b hb => hL b (by simp [hb])
    have hdecomp : laceDecomposition (L ++ [a]) = laceStep (laceDecomposition L) a := by
      simp [laceDecomposition, List.foldl_append]
    obtain ⟨hstepFlags, hstepTarget⟩ := laceStep_summary (laceDecomposition L) a
    have hcontinue : lastSpot n L = some a ↔
        (laceDecomposition L).getLast?.bind laceTarget = some a := by
      simp [hspot, ha]
    refine ⟨by simp [meteredOutcome_one_append, hlen], ?_, ?_⟩
    · rw [meteredOutcome_one_append, List.zip_append hlen.symm, List.map_append,
        hflags, hdecomp, hstepFlags]
      simp [nextSpot_eq_some_iff ha, hcontinue]
    · rw [lastSpot_append, hdecomp, hstepTarget]
      apply Option.ext
      intro j
      by_cases h : lastSpot n L = some a
      · by_cases ht : a + 1 < n <;>
          simp [nextSpot_eq_some_iff ha, h, hcontinue.mp h, Option.filter, ht, eq_comm (a := j)]
      · simp [nextSpot_eq_some_iff ha, h, mt hcontinue.mpr h, Option.filter, ha, eq_comm (a := j)]

-- Retain the source's hypotheses even though the list invariant only needs the range bound.
set_option linter.unusedVariables false in
/-- **Lucky cars of 1-metered parking are the lace starts.** Let $0 < m \le n$ and let
$\alpha = (a_1, \dots, a_m)$, with each $a_i \in \{1, \dots, n\}$, be any sequence of preferred
spots of $m$ cars on $n$ spots. Under the $1$-metered parking scheme, car $i$ is lucky (it parks
in its preferred spot $a_i$) if and only if position $i$ is the first position of one of the
laces of the lace decomposition $\mathrm{lace}(\alpha)$.

Source: Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking
Functions*, INTEGERS 25 (2025), Article A73, Lemma 1 (`integers-2025-A73-lem-1`). -/
public theorem one_metered_lucky_iff_lace_start {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (f : Fin m → Fin n) :
    ((List.ofFn fun i => (f i : ℕ)).zip (meteredOutcome 1 n (List.ofFn fun i => (f i : ℕ)))).map
        (fun p => decide (p.2 = some p.1)) =
      (laceDecomposition (List.ofFn fun i => (f i : ℕ))).flatMap
        fun c => true :: List.replicate (c.length - 1) false := by
  exact (luckyFlags_eq_laceFlags _ (by simp [List.mem_ofFn])).2.1

end MetaMathlibExt
