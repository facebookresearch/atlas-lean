/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 625
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem625Wanted

/-! Source record `UM-00002219-Q001`. -/
open Filter Topology

/-- The probability that a uniformly random labelled graph on `n` vertices (`G(n, 1/2)`) has
`χ(G) - ζ(G) > C`, where `ζ` is the cochromatic number. -/
noncomputable def probDiffGT (C : ℕ) (n : ℕ) : ℝ :=
  (Fintype.card { G : SimpleGraph (Fin n) //
      G.chromaticNumber.toNat - G.cochromaticNumber.toNat > C
    } : ℝ) /
  (Fintype.card (SimpleGraph (Fin n)) : ℝ)

/-- For `G ~ G(n, 1/2)`, `χ(G) - ζ(G) → ∞` almost surely: for every `C` the probability that
`χ(G) - ζ(G) > C` tends to `1`. -/
def conjecture : Prop :=
  ∀ C : ℕ, Filter.Tendsto (fun n => probDiffGT C n) Filter.atTop (𝓝 (1 : ℝ))

-- Carried source audit `UM-00002219-Q001` (see the Moved/ record).

/--
Resolved true: Resolved true: erdosproblems.com/625 records that Petkov and GPT-5.6 improved
Heckel's bounds to chi(G) - zeta(G) >> n/(log n)^3 with high probability for G ~ G(n,1/2), as
Heckel predicted; in particular chi(G) - zeta(G) -> infinity almost surely. Source: T. F. Bloom,
Erdős Problem #625, erdosproblems.com (live page, LaTeX source and forum threads read
2026-10-22), https://www.erdosproblems.com/625; S. Petkov (with GPT-5.6), proof for Erdős
Problem #625, https://github.com/SamPetkov/Erdos/blob/main/625/arxiv_625.pdf. Moved from
`OpenConjectures/Combinatorics/ErdosProblem625`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem625Wanted
