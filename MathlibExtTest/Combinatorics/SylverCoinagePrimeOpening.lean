/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SylverCoinagePrimeOpening

open MetaMathlibExt

-- Against the smallest covered prime, replying with 2 leaves the opener a winning position.
example : IsSylverNPosition {2, 5} := by
  have h := isSylverPPosition_prime_opening (p := 5) (by decide) (by decide)
  obtain ⟨_, replies⟩ := h
  apply replies 2
  simp only [sylverLegalMoves, Set.mem_ofPred_eq, AddSubmonoid.mem_closure_singleton,
    smul_eq_mul, not_exists]
  omega

-- At the excluded prime 3, the player to move can instead win by replying with 2.
example : IsSylverNPosition {3} := by
  apply IsSylverNPosition.move (q := 2) _ isSylverPPosition_two_three
  simp only [sylverLegalMoves, Set.mem_ofPred_eq, AddSubmonoid.mem_closure_singleton,
    smul_eq_mul, not_exists]
  omega
