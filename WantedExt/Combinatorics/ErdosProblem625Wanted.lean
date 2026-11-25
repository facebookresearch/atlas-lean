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

/-- **Probability of a large chromatic–cochromatic gap.** For natural numbers $C$ and $n$, the
proportion of simple graphs $G$ on the vertex set $\{0, \dots, n - 1\}$ with
$\chi(G) - \zeta(G) > C$, where $\chi$ is the chromatic number and $\zeta$ the cochromatic
number; equivalently, the probability of this event for a uniformly random labelled graph,
$G \sim G(n, 1/2)$. -/
noncomputable def probDiffGT (C : ℕ) (n : ℕ) : ℝ :=
  (Fintype.card { G : SimpleGraph (Fin n) //
      G.chromaticNumber.toNat - G.cochromaticNumber.toNat > C
    } : ℝ) /
  (Fintype.card (SimpleGraph (Fin n)) : ℝ)

/-- **Erdős Problem 625.** The statement that for every natural number $C$, the probability
that a uniformly random simple graph $G$ on the vertex set $\{0, \dots, n - 1\}$ (that is,
$G \sim G(n, 1/2)$) satisfies $\chi(G) - \zeta(G) > C$ tends to $1$ as $n \to \infty$, where
$\chi$ is the chromatic number and $\zeta$ the cochromatic number. In other words,
$\chi(G) - \zeta(G) \to \infty$ with high probability. -/
def conjecture : Prop :=
  ∀ C : ℕ, Filter.Tendsto (fun n => probDiffGT C n) Filter.atTop (𝓝 (1 : ℝ))

-- Carried source audit `UM-00002219-Q001` (see the Moved/ record).

/--
**Chromatic minus cochromatic number of a random graph tends to infinity.** For every natural
number $C$, the probability that a uniformly random simple graph $G$ on the vertex set
$\{0, \dots, n - 1\}$ (that is, $G \sim G(n, 1/2)$) satisfies $\chi(G) - \zeta(G) > C$
tends to $1$ as $n \to \infty$, where $\chi$ is the chromatic number and $\zeta$ the
cochromatic number.

Petkov and GPT-5.6 improved Heckel's bounds to $\chi(G) - \zeta(G) \gg n / (\log n)^3$ with
high probability for $G \sim G(n, 1/2)$, as Heckel predicted; this answers Erdős Problem 625 in
the affirmative.

Source: T. F. Bloom,
Erdős Problem #625, erdosproblems.com (live page, LaTeX source and forum threads read
2026-10-22), https://www.erdosproblems.com/625; S. Petkov (with GPT-5.6), proof for Erdős
Problem #625, https://github.com/SamPetkov/Erdos/blob/main/625/arxiv_625.pdf. Moved from
`OpenConjectures/Combinatorics/ErdosProblem625`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem625Wanted
