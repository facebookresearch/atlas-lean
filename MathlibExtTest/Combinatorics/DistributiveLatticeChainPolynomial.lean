/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.DistributiveLatticeChainPolynomial

open MathlibExt.Combinatorics.DistributiveLatticeChainPolynomialAMR156Problem0021Wanted
open Finset Polynomial

-- Even the empty poset has its empty chain.
example : chainPolynomial (Fin 0) = 1 := by
  classical
  have hu : (univ : Finset (Finset (Fin 0))) = {∅} := by
    ext s
    simp only [mem_univ, mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  rw [chainPolynomial, hu, sum_filter, sum_singleton]
  simp

-- The two middle elements of the four-element Boolean lattice form its only incomparable pair.
example : (chainPolynomial (Bool × Bool)).coeff 2 = 5 := by
  let pairs := (univ : Finset (Finset (Bool × Bool))).filter fun s =>
    ∀ x ∈ s, ∀ y ∈ s, x ≤ y ∨ y ≤ x
  classical
  have hf : (univ.filter fun s : Finset (Bool × Bool) =>
      IsChain (· ≤ ·) (s : Set (Bool × Bool))) = pairs := by
    ext s
    simp only [pairs, mem_filter, mem_univ, true_and]
    exact ⟨fun h _ hx _ hy => h.total hx hy, fun h _ hx _ hy _ => h _ hx _ hy⟩
  rw [chainPolynomial, hf, finsetSum_coeff]
  simp only [coeff_X_pow, sum_boole]
  decide +kernel
