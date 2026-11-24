/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.WeightedProjectiveSimplexReflexive

/-! # Examples of reflexive weighted projective space simplices -/

open MetaMathlibExt

-- The vertex `-q` of `Δ_(1,q)` is a lattice point, and doubling it gives a lattice point of `2Δ`.
example : IsLatticePoint (weightedSimplex ![3, 10, 15]) ![-3, -10, -15] := by
  apply subset_convexHull
  right
  funext i
  fin_cases i <;> simp

example : IsLatticePoint (polytopeDilate 2 (weightedSimplex ![1])) ![-2] := by
  refine ⟨fun _ => -1, subset_convexHull ℝ _ (Or.inr ?_), ?_⟩
  · funext i
    simp
  · funext i
    fin_cases i
    norm_num

example (P : Set (Fin 2 → ℝ)) : polytopeDilate 1 P = P := polytopeDilate_one P

-- For `n = 1` and `n = 2` the theorem gives the first reflexive stabilizations of `(3, 10, 15)`
-- and `(6, 20, 30)`.
example : reflexiveStabilization [3, 10, 15] = [1, 3, 10, 15] := by
  rw [← almostIDPWeights_eq_reflexiveStabilization 1 le_rfl]
  decide

example : reflexiveStabilization [6, 20, 30] = [1, 1, 1, 6, 20, 30] := by
  rw [← almostIDPWeights_eq_reflexiveStabilization 2 (by norm_num)]
  decide

-- The reflexive stabilization number of `(3, 10, 15)` is `1`, so `Δ_(1,(1,3,10,15))` is
-- reflexive and `Δ_(1,(3,10,15))` is not.
private theorem reflexiveStabilizationNumber_three_ten_fifteen_test :
    reflexiveStabilizationNumber [3, 10, 15] = 1 := by
  have h := congrArg List.length (almostIDPWeights_eq_reflexiveStabilization 1 le_rfl)
  simp only [List.length_ofFn, reflexiveStabilization, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil, Nat.mul_one] at h
  omega

example : IsReflexive (weightedSimplexList [1, 3, 10, 15]) := by
  have h1 := reflexiveStabilizationNumber_three_ten_fifteen_test
  have hne : {k : ℕ | IsReflexive
      (weightedSimplexList (List.replicate k 1 ++ [3, 10, 15]))}.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    rw [reflexiveStabilizationNumber, h, Nat.sInf_empty] at h1
    exact zero_ne_one h1
  have hmem := Nat.sInf_mem hne
  rw [← reflexiveStabilizationNumber, h1] at hmem
  exact hmem

example : ¬ IsReflexive (weightedSimplexList [3, 10, 15]) := by
  intro h
  have h0 : reflexiveStabilizationNumber [3, 10, 15] = 0 :=
    Nat.eq_zero_of_le_zero (Nat.sInf_le (by simpa using h))
  rw [reflexiveStabilizationNumber_three_ten_fifteen_test] at h0
  exact one_ne_zero h0

-- The hypothesis `1 ≤ n` is needed: for `n = 0` the weight vector is `(0, 0)`, which is too short
-- to be a stabilization of `(0, 0, 0)`.
example : List.ofFn (almostIDPWeights 0) = [0, 0] := by
  decide

example : List.ofFn (almostIDPWeights 0) ≠ reflexiveStabilization [3 * 0, 10 * 0, 15 * 0] := by
  intro h
  have := congrArg List.length h
  simp only [List.length_ofFn, reflexiveStabilization, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil] at this
  omega
