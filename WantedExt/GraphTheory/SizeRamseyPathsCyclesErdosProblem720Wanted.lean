/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Size Ramsey numbers of paths and cycles (Erdős Problem 720)

Erdős Problem 720 (Erdős, Faudree, Rousseau and Schelp): let `R̂(G)` denote the size Ramsey number,
the minimal number of edges `m` such that there is a graph `H` with `m` edges such that in any
`2`-colouring of the edges of `H` there is a monochromatic copy of `G`. Is it true that, if `P_n` is
the path of length `n`, then `R̂(P_n) / n → ∞` and `R̂(P_n) / n² → 0`? Is it true that, if `C_n` is
the cycle with `n` edges, then `R̂(C_n) = o(n²)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.SizeRamseyPathsCyclesErdosProblem720Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #720, https://www.erdosproblems.com/720 (status
PROVED). UnsolvedMath record UM-30006992 (`EP-720`), dataset ulamai/UnsolvedMath v1.8.0.

`H` ranges over finite graphs on `Fin N`; a colouring is a red subgraph `R ≤ H` with blue graph `H \
R`, and a monochromatic copy of `G` is `G ⊑ R` or `G ⊑ H \ R`. The size Ramsey number `R̂(G)` is the
least edge count of such an `H`, so each bound is stated through host graphs: `R̂(G) ≤ m` iff some
such `H` has at most `m` edges, and `R̂(G) > m` iff every such `H` has more than `m` edges. No size
Ramsey function is defined here: the repository's `OpenProblem2177.sizeRamseyNumber` lives in
OpenConjectures, which WantedExt may not import (`scripts/check_health.sh` layering). `P_n` is
`pathGraph (n + 1)` (`n` edges) and `C_n` is `cycleGraph n`. One target per question. Compared with
the formal-conjectures statement `ErdosProblems/720.lean` (equivalent; no code imported).
-/

open Filter

/-- Erdős Problem 720 (a): `R̂(P_n) / n → ∞`, where `P_n` is the path of length `n` (`n + 1`
vertices). Stated through host graphs: for every `C`, for all large `n`, every finite graph `H`
such that every red/blue colouring of its edges (red graph `R ≤ H`, blue graph `H \ R`) has a
monochromatic `P_n` has more than `C n` edges. -/
def pathSizeRamseySuperlinear : Prop :=
  ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ (N : ℕ) (H : SimpleGraph (Fin N)),
    (∀ R : SimpleGraph (Fin N), R ≤ H →
      (SimpleGraph.pathGraph (n + 1)).IsContained R ∨
        (SimpleGraph.pathGraph (n + 1)).IsContained (H \ R)) →
      C * (n : ℝ) < (H.edgeSet.ncard : ℝ)

/-- Erdős Problem 720 (b): `R̂(P_n) / n² → 0`. Stated through host graphs: for every `ε > 0` and all
large `n`, some finite graph with at most `ε n²` edges has a monochromatic `P_n` in every red/blue
colouring of its edges. -/
def pathSizeRamseySubquadratic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ (N : ℕ) (H : SimpleGraph (Fin N)),
    (H.edgeSet.ncard : ℝ) ≤ ε * (n : ℝ) ^ 2 ∧
      ∀ R : SimpleGraph (Fin N), R ≤ H →
        (SimpleGraph.pathGraph (n + 1)).IsContained R ∨
          (SimpleGraph.pathGraph (n + 1)).IsContained (H \ R)

/-- Erdős Problem 720 (c): `R̂(C_n) = o(n²)`, where `C_n` is the cycle with `n` edges. Stated
through host graphs: for every `ε > 0` and all large `n`, some finite graph with at most `ε n²`
edges has a monochromatic `C_n` in every red/blue colouring of its edges. -/
def cycleSizeRamseySubquadratic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∃ (N : ℕ) (H : SimpleGraph (Fin N)),
    (H.edgeSet.ncard : ℝ) ≤ ε * (n : ℝ) ^ 2 ∧
      ∀ R : SimpleGraph (Fin N), R ≤ H →
        (SimpleGraph.cycleGraph n).IsContained R ∨
          (SimpleGraph.cycleGraph n).IsContained (H \ R)

/--
Resolved false: Beck proved `R̂(P_n) ≪ n`, so `R̂(P_n) / n` is bounded; erdosproblems.com/720
records Beck's answer. Source: T. F. Bloom, Erdős Problems, Problem #720,
https://www.erdosproblems.com/720 (status PROVED); resolution: J. Beck, On size Ramsey number of
paths, trees, and circuits. I, J. Graph Theory 7 (1983), 115-129, erdosproblems.com/720: 'Answered
by Beck, who proved that in fact R̂(P_n) ≪ n and R̂(C_n) ≪ n', https://www.erdosproblems.com/720.
-/
public theorem_wanted pathSizeRamseySuperlinear_refuted : ¬ pathSizeRamseySuperlinear

/--
Resolved true: Beck proved `R̂(P_n) ≪ n`, in particular `R̂(P_n) / n² → 0`. Source: T. F. Bloom,
Erdős Problems, Problem #720, https://www.erdosproblems.com/720 (status PROVED); resolution: J.
Beck, On size Ramsey number of paths, trees, and circuits. I, J. Graph Theory 7 (1983), 115-129,
erdosproblems.com/720: 'Answered by Beck, who proved that in fact R̂(P_n) ≪ n and R̂(C_n) ≪ n',
https://www.erdosproblems.com/720.
-/
public theorem_wanted pathSizeRamseySubquadratic_holds : pathSizeRamseySubquadratic

/--
Resolved true: Beck proved `R̂(C_n) ≪ n`, in particular `R̂(C_n) = o(n²)` (erdosproblems.com/720).
Source: T. F. Bloom, Erdős Problems, Problem #720, https://www.erdosproblems.com/720 (status
PROVED); resolution: J. Beck, On size Ramsey number of paths, trees, and circuits. I, J. Graph
Theory 7 (1983), 115-129, erdosproblems.com/720: 'Answered by Beck, who proved that in fact R̂(P_n)
≪ n and R̂(C_n) ≪ n', https://www.erdosproblems.com/720.
-/
public theorem_wanted cycleSizeRamseySubquadratic_holds : cycleSizeRamseySubquadratic

end MathlibExt.GraphTheory.SizeRamseyPathsCyclesErdosProblem720Wanted
