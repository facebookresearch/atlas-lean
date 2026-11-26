/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ModifiedDegenerateBernoulliConvolution

/-! # Tests for the modified degenerate Bernoulli convolution -/

open Finset MetaMathlibExt

local notation "B" => modifiedDegenerateBernoulli

-- At bidegree (1, 1), each inner sum omits the tuple with zero distinguished index.
-- Only the shift in the second coordinate carries the extra 1.
example (lam a b : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    B lam 0 a * B lam 1 b + B lam 0 b * B lam 1 a =
      (B lam 0 a * B lam 1 (b - a + 1) + B lam 1 a * B lam 0 (b - a + 1)) +
        (B lam 1 b * B lam 0 (a - b) + B lam 0 b * B lam 1 (a - b)) := by
  have h := modifiedDegenerateBernoulli_lemma_three 2 (by decide) ![1, 1] ![a, b]
    lam hlam hlam1
  have htuple : Finset.Nat.antidiagonalTuple 2 2 = {![0, 2], ![1, 1], ![2, 0]} := by decide
  have h₀ : (univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h₁ : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
  norm_num [Fin.sum_univ_two, htuple, h₀, h₁, Finset.sum_insert] at h
  linear_combination h

-- With first index zero, only the second outer summand survives.
example (lam a b : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    B lam 0 b * B lam 0 a = B lam 0 b * B lam 0 (a - b) := by
  have h := modifiedDegenerateBernoulli_lemma_three 2 (by decide) ![0, 1] ![a, b]
    lam hlam hlam1
  have htuple : Finset.Nat.antidiagonalTuple 2 1 = {![0, 1], ![1, 0]} := by decide
  have h₀ : (univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have h₁ : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
  simpa [Fin.sum_univ_two, htuple, h₀, h₁, Finset.sum_insert] using h
