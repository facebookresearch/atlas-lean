/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdos Problem #146: degenerate bipartite extremal bound
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import MathlibExt.Combinatorics.SimpleGraph.Degeneracy
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem146Wanted

/-! Source record `EP-146`. -/

namespace EP146

/-!
# Clause inventory for [EP-146] Erdős Problem #146

- `V`: quantifier domain of vertices of the fixed graph `H` (finite type).
- `H : SimpleGraph V`: the fixed graph.
- `H` is bipartite (hypothesis `H.IsBipartite` from
  `Mathlib.Combinatorics.SimpleGraph.Bipartite`).
- `r : ℕ`: degeneracy parameter, with side condition `1 ≤ r`.
- `H` is `r`-degenerate (hypothesis `H.IsDegenerate r` from
  `MathlibExt.Combinatorics.SimpleGraph.Degeneracy`).
- `n : ℕ`: extremal number of vertices (asymptotic variable).
- `SimpleGraph.extremalNumber n H`: `ex(n; H)` from
  `Mathlib.Combinatorics.SimpleGraph.Extremal.Basic`.
- Conclusion: `ex(n; H) ≪ n ^ (2 - 1 / r)` as `n → ∞`, formalized as
  `Asymptotics.IsBigO Filter.atTop`.
-/

/-- [EP-146] The claim: if `H` is bipartite and `r`-degenerate with `1 ≤ r`, then
`ex(n; H) ≪ n ^ (2 - 1 / r)`. -/
def DegenerateExtremalClaim : Prop :=
  ∀ (V : Type*) [Fintype V] (H : SimpleGraph V) (r : ℕ),
    H.IsBipartite → H.IsDegenerate r → 1 ≤ r →
      Asymptotics.IsBigO Filter.atTop
        (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ))
        (fun n : ℕ => (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)))

end EP146

/--
Resolved false: Resolved false: an internal OpenAI model constructed a connected bipartite
2-degenerate H with ex(n;H) >= c n^{3/2+epsilon} for all large n (OpenAI, Ten proofs, 2026),
disproving the Erdős-Simonovits conjecture; erdosproblems.com/146 records it as disproved.
Source: T. F. Bloom, Erdős Problem #146, erdosproblems.com (live page, LaTeX source and forum
threads read 2026-10-22), https://www.erdosproblems.com/146; OpenAI, Ten proofs (section
disproving the Erdős degeneracy conjecture), 2026,
https://cdn.openai.com/pdf/ten-proofs-oai.pdf. Moved from
`OpenConjectures/Combinatorics/ErdosProblem146`.
-/
public theorem_wanted DegenerateExtremalClaim_refuted : ¬ EP146.DegenerateExtremalClaim

end MathlibExt.Combinatorics.ErdosProblem146Wanted
