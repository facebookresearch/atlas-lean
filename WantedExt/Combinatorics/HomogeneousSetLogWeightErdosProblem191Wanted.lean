/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Monochromatic sets of large logarithmic weight (Erdős Problem 191)

Erdős Problem 191: let `C > 0`. If `n` is large enough depending on `C`, does every 2-colouring of
the pairs of `{2, …, n}` have a set `X ⊆ {2, …, n}` whose pairs all have one colour and `∑_{x ∈ X} 1
/ log x ≥ C`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.Combinatorics.HomogeneousSetLogWeightErdosProblem191Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #191, https://www.erdosproblems.com/191 (status PROVED
(LEAN)). UnsolvedMath record UM-30006757 (`EP-191`), dataset ulamai/UnsolvedMath v1.8.0.

A 2-colouring of pairs is the edge/non-edge partition of a graph `G` on `ℕ`, of which only the pairs
inside `{2, …, n}` matter; a monochromatic `X` is a clique or an independent set. Compared with the
formal-conjectures statement `ErdosProblems/191.lean` (equivalent; no code imported).
-/

open Filter

/-- **Erdős Problem 191.** The statement that for every real $C > 0$ there is an $N$ such that for
every $n \ge N$ and every graph $G$ on the natural numbers (its edges and non-edges 2-colour the
pairs of $\{2, \dots, n\}$) there is a finite set $X \subseteq \{2, \dots, n\}$ that is a clique
or an independent set of $G$ (a monochromatic set) with $\sum_{x \in X} 1 / \log x \ge C$. -/
def homogeneousSetLargeLogWeight : Prop :=
  ∀ C : ℝ, 0 < C → ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph ℕ, ∃ X : Finset ℕ,
    X ⊆ Finset.Icc 2 n ∧ (G.IsClique (X : Set ℕ) ∨ G.IsIndepSet (X : Set ℕ)) ∧
      C ≤ ∑ x ∈ X, 1 / Real.log x

/-- **Monochromatic sets of large logarithmic weight exist.** For every real $C > 0$ there is an
$N$ such that for every $n \ge N$ and every graph $G$ on the natural numbers there is a finite
set $X \subseteq \{2, \dots, n\}$ that is a clique or an independent set of $G$ and satisfies
$\sum_{x \in X} 1 / \log x \ge C$.

Rödl proved this, and Conlon, Fox and Sudakov later showed that the best such $X$ has weight at
least $2^{-8} \log \log \log n$ for large $n$, which is sharp by Rödl's construction.

Source: T. F. Bloom, Erdős Problems, Problem #191,
https://www.erdosproblems.com/191 (status PROVED (LEAN)); resolution: V. Rödl, On homogeneous sets
of positive integers, J. Combin. Theory Ser. A 102 (2003), 229-240, erdosproblems.com/191: proved by
Rödl [Ro03]; Conlon, Fox and Sudakov (2013) gave the sharp bound 2^{-8} log log log n,
https://doi.org/10.1016/S0097-3165(03)00026-8.
-/
public theorem_wanted homogeneousSetLargeLogWeight_holds : homogeneousSetLargeLogWeight

end MathlibExt.Combinatorics.HomogeneousSetLogWeightErdosProblem191Wanted
