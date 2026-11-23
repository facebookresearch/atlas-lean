/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ErgodicMarkovChain
public import MathlibExt.Probability.KolmogorovCycleNecessity

@[expose] public section
open Finset BigOperators
open MathlibExt.Probability.ErgodicMarkovChain

namespace MathlibExtTest.Probability.ErgodicMarkovChainCanonicalTests

/-- Existing canonical stochastic matrices use the ordinary matrix-power bridge. -/
theorem canonical_power_bridge {M : ℕ} (P : _root_.StochasticMatrix M)
    (n : ℕ) (i j : Fin (M + 1)) :
    P.matPow n i j = (StochasticMatrix.toMatrix P ^ n) i j :=
  StochasticMatrix.matPow_eq_pow P n i j

/-- Ergodicity and the canonical irreducibility API refer to the same transition matrix. -/
theorem canonical_irreducible {M : ℕ} (P : _root_.StochasticMatrix M)
    (h : StochasticMatrix.IsErgodic P) : P.IsIrreducible :=
  fun i j => h.exists_matPow_pos i j

/-- An ergodic canonical chain supports the existing detailed-balance positivity theorem. -/
theorem canonical_balance_positive {M : ℕ} (P : _root_.StochasticMatrix M)
    (h : StochasticMatrix.IsErgodic P) (π : _root_.StochasticMatrix.Distribution M)
    (hdb : P.DetailedBalance π) : ∀ i, 0 < π.val i :=
  _root_.StochasticMatrix.distribution_pos_of_irreducible_detailedBalance P π
    (fun i j => h.exists_matPow_pos i j) hdb

end MathlibExtTest.Probability.ErgodicMarkovChainCanonicalTests
