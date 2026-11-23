/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equal products of central binomial coefficients (Erdős Problem 397)

Erdős Problem 397: are there only finitely many solutions of `∏ᵢ C(2mᵢ, mᵢ) = ∏ⱼ C(2nⱼ, nⱼ)` with
the `mᵢ, nⱼ` distinct?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Central

@[expose] public section

namespace MathlibExt.NumberTheory.CentralBinomialProductsErdosProblem397Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #397, https://www.erdosproblems.com/397 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30006852 (`EP-397`), dataset ulamai/UnsolvedMath v1.8.0.

A solution is a pair of disjoint finite sets `M, N` (all indices distinct). Both sets are nonempty
and consist of positive integers, which only removes degenerate solutions (`C(0, 0) = 1`, empty
products), so the refutation is stronger than for the unrestricted count. Compared with the
formal-conjectures statement `ErdosProblems/397.lean` (stronger, since that statement has no
positivity or nonemptiness; no code imported).
-/

/-- Erdős Problem 397: only finitely many pairs of disjoint nonempty finite sets `M, N` of positive
integers satisfy `∏_{m ∈ M} C(2m, m) = ∏_{n ∈ N} C(2n, n)`. -/
def finitelyManyCentralBinomialProductEqualities : Prop :=
  {p : Finset ℕ × Finset ℕ | p.1.Nonempty ∧ p.2.Nonempty ∧ (∀ m ∈ p.1 ∪ p.2, 0 < m) ∧
    Disjoint p.1 p.2 ∧ ∏ m ∈ p.1, m.centralBinom = ∏ m ∈ p.2, m.centralBinom}.Finite

/--
Resolved false: Somani (using ChatGPT) found the identity `C(2a, a) C(4a + 4, 2a + 2) C(2c, c) =
C(2a + 2, a + 1) C(4a, 2a) C(2c + 2, c + 1)` with `c = 8a² + 8a + 1`; for every `a ≥ 2` the six
indices are distinct, which gives infinitely many solutions. erdosproblems.com/397 lists the problem
as disproved, with a Lean proof. Source: T. F. Bloom, Erdős Problems, Problem #397,
https://www.erdosproblems.com/397 (status DISPROVED (LEAN)); resolution: R. Somani (using ChatGPT),
erdosproblems.com/397; formal proof gist.github.com/llllvvuu/40d68cfa9de9f43eece07ff4fdc3b0ef
(397.lean), C(2a, a) C(4a + 4, 2a + 2) C(2c, c) = C(2a + 2, a + 1) C(4a, 2a) C(2c + 2, c + 1) for c
= 8a² + 8a + 1, a ≥ 2, https://www.erdosproblems.com/397.
-/
public theorem_wanted finitelyManyCentralBinomialProductEqualities_refuted :
    ¬ finitelyManyCentralBinomialProductEqualities

end MathlibExt.NumberTheory.CentralBinomialProductsErdosProblem397Wanted
