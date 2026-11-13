/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Counting highly composite numbers (Erdős Problem 381)

Erdős Problem 381: `n` is highly composite if `τ(m) < τ(n)` for all `m < n`. With `Q(x)` the number
of highly composite numbers in `[1, x]`, is `Q(x) ≫_k (log x)^k` for every `k ≥ 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.NumberTheory.HighlyComposite

@[expose] public section

namespace MathlibExt.NumberTheory.HighlyCompositeCountErdosProblem381Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #381, https://www.erdosproblems.com/381 (status
DISPROVED). UnsolvedMath record UM-30006847 (`EP-381`), dataset ulamai/UnsolvedMath v1.8.0.

Highly composite numbers are MathlibExt's `Nat.IsHighlyComposite` (positive, with more divisors than
every smaller positive integer). `Q(x) ≫_k (log x)^k` means `Q(x) ≥ c_k (log x)^k` for some `c_k >
0` and all large real `x`. formal-conjectures has no statement of this problem.
-/

/-- `Q(x)`: the number of highly composite numbers in `[1, x]`. -/
noncomputable def highlyCompositeCount (x : ℝ) : ℕ :=
  {n : ℕ | n.IsHighlyComposite ∧ (n : ℝ) ≤ x}.ncard

/-- Erdős Problem 381: for every `k ≥ 1`, `Q(x) ≫_k (log x)^k`. -/
def highlyCompositeCountBeatsLogPowers : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in Filter.atTop,
    c * Real.log x ^ k ≤ highlyCompositeCount x

/--
Resolved false: Nicolas proved `Q(x) ≪ (log x)^{O(1)}`, so `Q(x) ≥ c (log x)^k` fails for large `x`
once `k` exceeds that exponent (Erdős had shown `Q(x) ≫ (log x)^{1 + c}`); erdosproblems.com/381
lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem #381,
https://www.erdosproblems.com/381 (status DISPROVED); resolution: J.-L. Nicolas, Répartition des
nombres hautement composés de Ramanujan, Canadian J. Math. (1971), 116-130, Q(x) ≪ (log x)^{O(1)}
(erdosproblems.com/381).
-/
public theorem_wanted highlyCompositeCountBeatsLogPowers_refuted :
    ¬ highlyCompositeCountBeatsLogPowers

end MathlibExt.NumberTheory.HighlyCompositeCountErdosProblem381Wanted
