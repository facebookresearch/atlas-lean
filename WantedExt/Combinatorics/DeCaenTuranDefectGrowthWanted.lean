/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.DeCaenTuranDefectGrowthWanted

/-!
# De Caen question on `k * (1 - π(K_{k+1}^k))`

Source: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source collection AIM Problem Lists, Source URL http://aimpl.org/hypergraphturan/1/.

Clause list from the source; every item appears in the formal text below:
1. Uniformity parameter `k : ℕ` with `k → ∞` via `Filter.atTop`.
2. `K_{k+1}^k` is the complete `k`-uniform hypergraph on `k + 1` vertices.
3. Vertex set `Fin (k + 1)`; edge set is all `k`-element subsets.
4. `F`-free means no embedding `Fin (k + 1) ↪ Fin n` sending each forbidden edge to an edge.
5. Turán number is the maximum edge count among `F`-free `k`-families on `Fin n`.
6. Ratio is `ex / C(n, k)`, with value `0` when `C(n, k) = 0`.
7. Density `π` is the `limsup` of the ratios as `n → ∞`.
8. Sequence `a k = k * (1 - π(K_{k+1}^k))`.
9. Question: does `a k` tend to `∞` as `k → ∞`, i.e. `Tendsto a atTop atTop`.
-/

open scoped Classical

/-- Complete `k`-uniform edge family on `m` vertices: all `k`-subsets of `Fin m`.

Source citation: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source URL http://aimpl.org/hypergraphturan/1/. -/
def completeHypergraphEdges (k m : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.powersetCard k

/-- Turán number for `K_{k+1}^k`: maximum cardinality among `k`-uniform edge families
on `Fin n` with no embedding of the complete edges on `Fin (k + 1)`.

Source citation: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source URL http://aimpl.org/hypergraphturan/1/. -/
noncomputable def turanNumber (k n : ℕ) : ℕ :=
  let forb : Finset (Finset (Fin (k + 1))) := completeHypergraphEdges k (k + 1)
  let all : Finset (Finset (Finset (Fin n))) :=
    ((Finset.univ : Finset (Fin n)).powersetCard k).powerset
  let free := all.filter (fun E => ¬ ∃ f : Fin (k + 1) ↪ Fin n, ∀ e ∈ forb, Finset.map f e ∈ E)
  free.sup (fun E => E.card)

/-- Turán density ratio `ex(n, K_{k+1}^k) / C(n, k)`, `0` when `C(n, k) = 0`.

Source citation: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source URL http://aimpl.org/hypergraphturan/1/. -/
noncomputable def turanDensityRatio (k n : ℕ) : ℝ :=
  if n.choose k = 0 then 0 else (turanNumber k n : ℝ) / (n.choose k : ℝ)

/-- Turán density `π(K_{k+1}^k)` as the `limsup` of the density ratios as `n → ∞`.

Source citation: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source URL http://aimpl.org/hypergraphturan/1/. -/
noncomputable def turanDensityComplete (k : ℕ) : ℝ :=
  Filter.limsup (fun n : ℕ => turanDensityRatio k n) Filter.atTop

/-- De Caen question: does `k * (1 - π(K_{k+1}^k))` tend to `∞` as `k → ∞`.

Source citation: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source URL http://aimpl.org/hypergraphturan/1/. -/
noncomputable def conjecture : Prop :=
  Filter.Tendsto (fun k : ℕ => (k : ℝ) * (1 - turanDensityComplete k)) Filter.atTop Filter.atTop

/--
Resolved false: Resolved false: Pikhurko (Adv. Math. 464 (2025) 110148, Theorem 1.1) proves T(n,
k+1, k) <= 6.239/(k+1) * C(n,k) for all n > k >= 1, so k(1 - pi(K^k_{k+1})) <= 6.239 for every
k; the paper states that this disproves de Caen's conjecture. Source: O. Pikhurko, Constructions
of Turán systems that are tight up to a multiplicative constant, Advances in Mathematics 464
(2025), 110148, https://pikhurko.github.io/E/Pikhurko25am.pdf. Moved from
`OpenConjectures/Combinatorics/DeCaenTuranDefectGrowth`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.DeCaenTuranDefectGrowthWanted
