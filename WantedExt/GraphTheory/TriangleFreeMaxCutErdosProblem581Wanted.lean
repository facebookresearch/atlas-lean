/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bipartite subgraphs of triangle-free graphs (Erdős Problem 581)

Erdős Problem 581 (Chung, Erdős and Graham): let `f(m)` be the maximal `k` such that a triangle-free
graph on `m` edges must contain a bipartite graph with `k` edges. Determine `f(m)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MathlibExt.GraphTheory.TriangleFreeMaxCutErdosProblem581Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #581, https://www.erdosproblems.com/581 (status
SOLVED). UnsolvedMath record UM-30006939 (`EP-581`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite; a bipartite subgraph is `H ≤ G` with `H.IsBipartite`. 'Determine `f(m)`' is
formalized as Alon's resolution `f(m) = m/2 + Θ(m^{4/5})`, with constants for every `m`, as on the
problem page; the exact value of `f(m)` is not known and is not stated. Compared with the
formal-conjectures statement `ErdosProblems/581.lean` (equivalent; no code imported).
-/

/-- `f(m)`: the largest `k` such that every finite triangle-free graph with `m` edges has a
bipartite subgraph with at least `k` edges (the set is bounded by `m`, since a matching with `m`
edges is triangle-free). -/
noncomputable def triangleFreeMaxCut (m : ℕ) : ℕ :=
  sSup {k | ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    G.edgeSet.ncard = m → ∃ H ≤ G, H.IsBipartite ∧ k ≤ H.edgeSet.ncard}

/-- Erdős Problem 581 (Chung, Erdős and Graham), in the form of Alon's answer: there are constants
`c₁, c₂ > 0` with `m/2 + c₁ m^{4/5} ≤ f(m) ≤ m/2 + c₂ m^{4/5}` for every `m`. -/
def triangleFreeMaxCutAsymptotics : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ m : ℕ,
    (m : ℝ) / 2 + c₁ * (m : ℝ) ^ (4 / 5 : ℝ) ≤ triangleFreeMaxCut m ∧
      (triangleFreeMaxCut m : ℝ) ≤ (m : ℝ) / 2 + c₂ * (m : ℝ) ^ (4 / 5 : ℝ)

/--
Resolved true: Alon showed that there are constants `c₁, c₂ > 0` with `m/2 + c₁ m^{4/5} ≤ f(m) ≤ m/2
+ c₂ m^{4/5}`; erdosproblems.com/581 lists the problem as solved, with a Lean proof of the
formal-conjectures statement. Source: T. F. Bloom, Erdős Problems, Problem #581,
https://www.erdosproblems.com/581 (status SOLVED); resolution: N. Alon, Bipartite subgraphs,
Combinatorica (1996), 301-311, erdosproblems.com/581: there are constants c₁, c₂ > 0 with m/2 + c₁
m^{4/5} ≤ f(m) ≤ m/2 + c₂ m^{4/5}, https://www.erdosproblems.com/581.
-/
public theorem_wanted triangleFreeMaxCutAsymptotics_holds : triangleFreeMaxCutAsymptotics

end MathlibExt.GraphTheory.TriangleFreeMaxCutErdosProblem581Wanted
