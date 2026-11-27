/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PositionalColoredCompositions

/-!
# Even colored compositions and binary runs

The count of even colored compositions of `k + 1` is the sum of the products of the lengths
of the runs of ones in binary strings of length `k`.
-/

namespace MetaMathlibExt
namespace PositionalColoredCompositionRuns

/-- Run lengths after a prefix ending in `n + 1` copies of `b`, including this open run. -/
private def runs (b : Bool) (n : ℕ) : List Bool → List ℕ
  | [] => [n + 1]
  | x :: xs =>
    if x = b then runs b (n + 1) xs else (n + 1) :: runs x 0 xs

private theorem runs_pos (b : Bool) (n : ℕ) (xs : List Bool) :
    ∀ p ∈ runs b n xs, 0 < p := by
  induction xs generalizing b n with
  | nil => simp [runs]
  | cons x xs ih =>
    by_cases h : x = b
    · simpa [runs, h] using ih b (n + 1)
    · simpa [runs, h] using ih x 0

private theorem runs_sum (b : Bool) (n : ℕ) (xs : List Bool) :
    (runs b n xs).sum = n + 1 + xs.length := by
  induction xs generalizing b n with
  | nil => simp [runs]
  | cons x xs ih =>
    by_cases h : x = b <;> simp [runs, h, ih] <;> omega

/-- Recover a binary string from its first bit and successive run lengths. -/
private def expand (b : Bool) : List ℕ → List Bool
  | [] => []
  | p :: ps => List.replicate p b ++ expand (!b) ps

private theorem expand_runs (b : Bool) (n : ℕ) (xs : List Bool) :
    expand b (runs b n xs) = List.replicate (n + 1) b ++ xs := by
  induction xs generalizing b n with
  | nil => simp [runs, expand]
  | cons x xs ih =>
    cases b <;> cases x <;> simp [runs, expand, ih, List.replicate_succ']

/-- Prepend a zero, then take the lengths of its alternating zero and one runs. -/
private def toComposition {k : ℕ} (f : Fin k → Bool) : Composition (k + 1) where
  blocks := runs false 0 (List.ofFn f)
  blocks_pos := runs_pos _ _ _ _
  blocks_sum := by simp [runs_sum, Nat.add_comm]

private theorem toComposition_bijective (k : ℕ) : Function.Bijective (@toComposition k) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro f g h
    have he := congrArg (fun c => expand false c.blocks) h
    simpa [toComposition, expand_runs] using he
  · simp [composition_card]

/-- Product of alternating parts, starting with a colored part exactly when `b` is true. -/
private def weight (b : Bool) : List ℕ → ℕ
  | [] => 1
  | p :: ps => (if b then p else 1) * weight (!b) ps

private theorem weight_eq_mapIdx (ps : List ℕ) (j : ℕ) :
    weight (decide (j % 2 = 0)) ps =
      (ps.mapIdx fun i p => if (i + j) % 2 = 0 then p else 1).prod := by
  induction ps generalizing j with
  | nil => simp [weight]
  | cons p ps ih =>
    have flip : (!decide (j % 2 = 0)) = decide ((j + 1) % 2 = 0) := by
      by_cases h : j % 2 = 0 <;> simp [h] <;> omega
    simp [weight, List.mapIdx_cons, flip, ih, Nat.add_left_comm, Nat.add_comm]

private theorem weight_runs (b : Bool) (n : ℕ) (xs : List Bool) :
    weight b (runs b n xs) =
      let acc := if b then List.replicate (n + 1) true else []
      (((List.splitOnPPrepend (· == false) xs acc).map List.length).filter (· ≠ 0)).prod := by
  induction xs generalizing b n with
  | nil => cases b <;> simp [runs, weight]
  | cons x xs ih =>
    cases b <;> cases x <;>
      simp [runs, weight, List.splitOnPPrepend_cons_eq_ite, ← List.splitOnPPrepend_nil_right,
        ih, List.replicate_succ]

end PositionalColoredCompositionRuns

open PositionalColoredCompositionRuns

/-- **Even colored compositions and runs in binary strings.** For every $k \ge 0$, the number
$e(k + 1) = c_{2,0}(k + 1)$ of even colored compositions of $k + 1$, in which only the parts at
even positions are colored, equals the sum, over all binary strings of length $k$, of the
product of the lengths of the maximal runs of $1$s in the string; a string without a $1$
contributes the empty product $1$.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 4 (`integers-2026-A49-thm-4`). -/
public theorem even_succ_eq_sum_runLength_prod (k : ℕ) :
    positionalColoredCompositionCount 2 0 (k + 1) =
      ∑ f : Fin k → Bool,
        ((((List.ofFn f).splitOn false).map List.length).filter (· ≠ 0)).prod := by
  let e := Equiv.ofBijective _ (toComposition_bijective k)
  unfold positionalColoredCompositionCount
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro f _
  change ((runs false 0 (List.ofFn f)).mapIdx _).prod = _
  rw [← weight_eq_mapIdx _ 1]
  simpa [List.splitOn_eq_splitOnP] using weight_runs false 0 (List.ofFn f)

end MetaMathlibExt
