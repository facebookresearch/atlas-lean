/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Independent sets of set mappings on pairs (Erdős Problem 1025)

Erdős Problem 1025 (Erdős and Hajnal): for `f` from the pairs of `{1, …, n}` to `{1, …, n}` with
`f(x, y) ∉ {x, y}`, call `X` independent if `f(x, y) ∉ X` for all `x, y ∈ X`. Let `g(n)` be such
that every such `f` has an independent set of size at least `g(n)`. Estimate `g(n)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Sym.Sym2

@[expose] public section

namespace MathlibExt.Combinatorics.PairSetMappingIndependenceErdosProblem1025Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1025, https://www.erdosproblems.com/1025 (status
SOLVED (LEAN)). UnsolvedMath record UM-30007132 (`EP-1025`), dataset ulamai/UnsolvedMath v1.8.0.

Pairs are unordered pairs of distinct elements (`Sym2`, diagonal values unused); `g(n)` is the
largest guaranteed size. For `n = 2` no admissible mapping exists, so every `k` qualifies and `sSup`
returns the junk value `0`; `IsTheta` at `atTop` ignores it. The estimate is stated as
`g(n) ≍ n^{1/2}` (`Asymptotics.IsTheta`): Spencer's Turán bound for `3`-graphs gives the lower
bound, and Conlon, Fox and Sudakov (Section 2, Theorem 2.1 with `k = 2`, `l = 1`) give the upper
bound. The UnsolvedMath triage note proposed `(n log n)^{1/2}`, which is only the upper bound of
Erdős and Hajnal. Compared with the formal-conjectures statement `ErdosProblems/1025.lean`
(equivalent; no code imported).
-/

/-- `X` is independent for a set mapping `f` on pairs: `f {x, y} ∉ X` whenever `x ≠ y` lie in `X`.
-/
def IsIndependentFor {n : ℕ} (f : Sym2 (Fin n) → Fin n) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f s(x, y) ∉ X

/-- `g(n)`: the largest `k` such that every set mapping `f` on the pairs of an `n`-element set with
`f {x, y} ∉ {x, y}` has an independent set of size at least `k`. -/
noncomputable def setMappingIndependence (n : ℕ) : ℕ :=
  sSup {k | ∀ f : Sym2 (Fin n) → Fin n, (∀ x y, x ≠ y → f s(x, y) ≠ x ∧ f s(x, y) ≠ y) →
    ∃ X : Finset (Fin n), IsIndependentFor f X ∧ k ≤ X.card}

/-- Erdős Problem 1025, with the answer of Spencer and of Conlon, Fox and Sudakov:
`g(n) ≍ n^{1/2}`. -/
def setMappingIndependenceAsymp : Prop :=
  Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (setMappingIndependence n : ℝ))
    (fun n : ℕ => Real.sqrt n)

/--
Resolved true: Spencer proved `g(n) ≫ n^{1/2}` and Conlon, Fox and Sudakov proved `g(n) ≪ n^{1/2}`;
erdosproblems.com/1025 lists the problem as solved, with a formal proof in plby/lean-proofs
(`Erdos1025.lean`). Source: T. F. Bloom, Erdős Problems, Problem #1025,
https://www.erdosproblems.com/1025 (status SOLVED (LEAN)); resolution: J. Spencer, Turán's theorem
for k-graphs, Discrete Math. (1972), 183-186; D. Conlon, J. Fox and B. Sudakov, Short proofs of some
extremal results II, J. Combin. Theory Ser. B (2016), 173-196, Spencer: g(n) ≫ n^{1/2};
Conlon-Fox-Sudakov: g(n) ≪ n^{1/2} (erdosproblems.com/1025),
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1025.lean#L829.
-/
public theorem_wanted setMappingIndependenceAsymp_holds : setMappingIndependenceAsymp

end MathlibExt.Combinatorics.PairSetMappingIndependenceErdosProblem1025Wanted
