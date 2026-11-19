/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sidon sets that are asymptotic bases of order three (Erdős Problem 157)

Erdős Problem 157: does there exist an infinite Sidon set which is an asymptotic basis of order `3`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Additive.Basis
public import MathlibExt.Combinatorics.Additive.Sidon

@[expose] public section

namespace MathlibExt.NumberTheory.SidonAsymptoticBasisErdosProblem157Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #157, https://www.erdosproblems.com/157 (status
PROVED). UnsolvedMath record UM-30006744 (`EP-157`), dataset ulamai/UnsolvedMath v1.8.0.

Sidon sets are the repository's `Set.IsSidon` (all sums `a + b`, `a ≤ b`, distinct) and asymptotic
bases `Set.IsAsymptoticAddBasisOfOrder 3`. Compared with the formal-conjectures statement
`ErdosProblems/157.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 157: some infinite Sidon set `A ⊆ ℕ` is an asymptotic additive basis of order
`3` (every sufficiently large integer is the sum of three elements of `A`). -/
def sidonAsymptoticBasisOfOrderThree : Prop :=
  ∃ A : Set ℕ, A.Infinite ∧ A.IsSidon ∧ A.IsAsymptoticAddBasisOfOrder 3

/--
Resolved true: Pilatte constructed a Sidon set `S ⊆ ℕ` such that every sufficiently large integer is
a sum of three elements of `S` (using Sawin's `𝔽_q[t]` analogue of Montgomery's conjecture);
erdosproblems.com/157 lists the problem as proved. Source: T. F. Bloom, Erdős Problems, Problem
#157, https://www.erdosproblems.com/157 (status PROVED); resolution: C. Pilatte, A solution to the
Erdős-Sárközy-Sós problem on asymptotic Sidon bases of order 3, Compositio Math. 160 (2024),
1418-1432, abstract (arXiv:2303.09659): there is a Sidon set S ⊆ ℕ that is an asymptotic basis of
order 3, https://arxiv.org/abs/2303.09659.
-/
public theorem_wanted sidonAsymptoticBasisOfOrderThree_holds : sidonAsymptoticBasisOfOrderThree

end MathlibExt.NumberTheory.SidonAsymptoticBasisErdosProblem157Wanted
