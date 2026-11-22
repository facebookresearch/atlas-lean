/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Independence number of linear triple systems (Erdős Problem 1024)

Erdős Problem 1024: let `f(n)` be such that every `3`-uniform linear hypergraph on `n` vertices
contains an independent set on `f(n)` vertices. Estimate `f(n)`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1024, https://www.erdosproblems.com/1024 (status
SOLVED). UnsolvedMath record UM-30007131 (`EP-1024`), dataset ulamai/UnsolvedMath v1.8.0.

`f(n)` is read as the largest such size, which is finite since independent sets have at most `n`
vertices. A linear hypergraph has edges of size `3` meeting pairwise in at most one vertex; an
independent set contains no edge. The estimate is stated as `f(n) ≍ (n log n)^{1/2}`
(`Asymptotics.IsTheta`). Compared with the formal-conjectures statement `ErdosProblems/1024.lean`
(equivalent; no code imported).
-/

/-- A `3`-uniform linear hypergraph (partial Steiner triple system) on `Fin n`: every edge has three
vertices and two distinct edges share at most one vertex. -/
def IsLinearTripleSystem {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ H, e.card = 3) ∧ ∀ e ∈ H, ∀ e' ∈ H, e ≠ e' → (e ∩ e').card ≤ 1

/-- `f(n)`: the largest `m` such that every `3`-uniform linear hypergraph on `n` vertices has an
independent set (a vertex set containing no edge) of size at least `m`. -/
noncomputable def linearTripleIndependence (n : ℕ) : ℕ :=
  sSup {m | ∀ H : Finset (Finset (Fin n)), IsLinearTripleSystem H →
    ∃ I : Finset (Fin n), m ≤ I.card ∧ ∀ e ∈ H, ¬ e ⊆ I}

/-- Erdős Problem 1024, with the answer of Phelps and Rödl: `f(n) ≍ (n log n)^{1/2}`. -/
def linearTripleIndependenceAsymp : Prop :=
  Asymptotics.IsTheta Filter.atTop (fun n : ℕ => (linearTripleIndependence n : ℝ))
    (fun n : ℕ => Real.sqrt (n * Real.log n))

/--
Resolved true: erdosproblems.com/1024 records that Phelps and Rödl proved `f(n) ≍ (n log n)^{1/2}`
(Erdős had `n^{1/2} ≪ f(n) ≪ n^{2/3}`). Source: T. F. Bloom, Erdős Problems, Problem #1024,
https://www.erdosproblems.com/1024 (status SOLVED); resolution: K. T. Phelps and V. Rödl, Steiner
triple systems with minimum independence number, Ars Combin. (1986), 167-172, f(n) ≍ (n log n)^{1/2}
(erdosproblems.com/1024), https://www.erdosproblems.com/1024.
-/
public theorem_wanted linearTripleIndependenceAsymp_holds : linearTripleIndependenceAsymp

end MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted
