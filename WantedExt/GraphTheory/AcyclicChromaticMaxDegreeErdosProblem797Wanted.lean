/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Acyclic chromatic number and maximum degree (Erdős Problem 797)

Erdős Problem 797: let `f(d)` be the maximal acyclic chromatic number of a graph with maximum degree
`d` (the least number of colors of a proper coloring with no cycle using only two colors). Estimate
`f(d)`. In particular, is `f(d) = o(d²)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #797, https://www.erdosproblems.com/797 (status
PROVED). UnsolvedMath record UM-30007036 (`EP-797`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite (on `Fin n`). A coloring is acyclic when it is proper and any two color classes
induce a forest, i.e. no cycle uses only two colors. `f(d) = o(d²)` is: for every `ε > 0` and all
large `d`, every graph of maximum degree at most `d` has an acyclic coloring with `⌊ε d²⌋` colors
(the maximum over degree exactly `d` is the same). formal-conjectures has no statement of this
problem.
-/

/-- An acyclic coloring: a proper coloring in which the union of any two color classes induces a
forest, i.e. no cycle uses only two colors. -/
def IsAcyclicColoring {V : Type*} (G : SimpleGraph V) {k : ℕ} (c : V → Fin k) : Prop :=
  (∀ u v, G.Adj u v → c u ≠ c v) ∧ ∀ i j : Fin k, (G.induce {v | c v = i ∨ c v = j}).IsAcyclic

open Classical in
/-- Erdős Problem 797: `f(d) = o(d²)`, where `f(d)` is the largest acyclic chromatic number of a
finite graph with maximum degree `d`. -/
def acyclicChromaticSubquadratic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in Filter.atTop, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.maxDegree ≤ d → ∃ c : Fin n → Fin ⌊ε * (d : ℝ) ^ 2⌋₊, IsAcyclicColoring G c

/--
Resolved true: Alon, McDiarmid and Reed proved `d^{4/3} / (log d)^{1/3} ≪ f(d) ≪ d^{4/3}`, so `f(d)
= o(d²)`; erdosproblems.com/797 lists the problem as proved. Source: T. F. Bloom, Erdős Problems,
Problem #797, https://www.erdosproblems.com/797 (status PROVED); resolution: N. Alon, C. McDiarmid
and B. Reed, Acyclic coloring of graphs, Random Structures Algorithms 2 (1991), 277-288, Theorem
1.1: a graph of maximum degree d has acyclic chromatic number O(d^{4/3}) as d → ∞, settling Erdős's
1976 conjecture A(G) = o(d²); Theorem 1.2: some graphs of maximum degree d need Ω(d^{4/3}/(log
d)^{1/3}) colors,
https://web.math.princeton.edu/~nalon/PDFS/Publications2/Acyclic%20colouring%20of%20graphs.pdf.
-/
public theorem_wanted acyclicChromaticSubquadratic_holds : acyclicChromaticSubquadratic

end MathlibExt.GraphTheory.AcyclicChromaticMaxDegreeErdosProblem797Wanted
