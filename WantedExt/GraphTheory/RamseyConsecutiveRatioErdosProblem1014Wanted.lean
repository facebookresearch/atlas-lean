/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ratios of consecutive off-diagonal Ramsey numbers (Erdős Problem 1014)

Erdős Problem 1014: prove, for fixed `k ≥ 3`, that `lim_{l → ∞} R(k, l + 1) / R(k, l) = 1`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey

@[expose] public section

namespace MathlibExt.GraphTheory.RamseyConsecutiveRatioErdosProblem1014Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1014, https://www.erdosproblems.com/1014 (status
PROVED (LEAN)). UnsolvedMath record UM-00002439 (`EP-1014`), dataset ulamai/UnsolvedMath v1.8.0.

`R(k, l)` is `MathlibExt`'s `SimpleGraph.graphRamsey k l`, the least `N` such that every graph on
`Fin N` contains `K_k` or its complement contains `K_l` (an independent set of size `l`); graphs on
more vertices then have the same property, so this is the usual Ramsey number. Compared with the
formal-conjectures statement `ErdosProblems/1014.lean` (equivalent; no code imported).
-/

/-- Erdős Problem 1014: for every fixed `k ≥ 3`, `R(k, l + 1) / R(k, l) → 1` as `l → ∞`. -/
def ramseyConsecutiveRatioTendsToOne : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    Filter.Tendsto
      (fun l : ℕ => (SimpleGraph.graphRamsey k (l + 1) : ℝ) / SimpleGraph.graphRamsey k l)
      Filter.atTop (nhds 1)

/--
Resolved true: erdosproblems.com/1014 marks the problem proved, on the strength of an unrefereed
proof by an internal OpenAI model that `R(k, l + 1) ≤ (1 + O(l^{-c/k²})) R(k, l)` for some `c > 0`;
since `R(k, l)` is nondecreasing in `l`, the ratio tends to `1`. Source: T. F. Bloom, Erdős
Problems, Problem #1014, https://www.erdosproblems.com/1014 (status PROVED (LEAN)); resolution:
proof by an internal model at OpenAI,
https://cdn.openai.com/pdf/6dc7175d-d9e7-4b8d-96b8-48fe5798cd5b/Ramsey.pdf (2026), R(k, l + 1) ≤
(1 + O(l^{-c/k²})) R(k, l) for some c > 0 (erdosproblems.com/1014: "This been solved by an internal
model at OpenAI"), https://www.erdosproblems.com/1014.
-/
public theorem_wanted ramseyConsecutiveRatioTendsToOne_holds : ramseyConsecutiveRatioTendsToOne

end MathlibExt.GraphTheory.RamseyConsecutiveRatioErdosProblem1014Wanted
