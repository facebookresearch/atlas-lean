/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimum degree of transversal-critical triple systems (Erdős Problem 834)

Erdős Problem 834: does there exist a `3`-critical `3`-uniform hypergraph in which every vertex
has degree `≥ 7`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph

@[expose] public section

namespace MathlibExt.Combinatorics.TransversalCriticalTripleSystemDegreeErdosProblem834Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #834, https://www.erdosproblems.com/834 (status
SOLVED). UnsolvedMath record UM-30007054 (`EP-834`), dataset ulamai/UnsolvedMath v1.8.0.

Erdős and Lovász did not define `3`-critical. The page gives two definitions and records Li's
resolution of both. This module states the transversal one: there is a set of `3` vertices meeting
every edge, no such set of size `2`, and for every edge `e` a pair of vertices meeting every edge
except `e` (`τ(H) = 3` and `τ(H - e) ≤ 2`; transversals of size at most `t` are used, which is
equivalent once there are at least `t` vertices). Uniformity is MathlibExt's
`SetFamily.IsUniform`; the transversal conditions are written out in the target. The vertex set is
`Fin n`, and every vertex of it must have degree at least `7`. The chromatic reading is not
stated: Li answers it with one explicit `9`-vertex hypergraph, a finite check. Compared with the
formal-conjectures statement `ErdosProblems/834.lean` (equivalent to its part (i); no code
imported).
-/

/-- Erdős Problem 834 with the transversal notion of `3`-criticality: there is a `3`-uniform
hypergraph `H` (`SetFamily.IsUniform H 3`, on some vertex set `Fin n`) with a transversal (a vertex
set meeting every edge) of at most `3` vertices, none of at most `2` vertices, and for every edge
`e` a transversal of `H - e` of at most `2` vertices (`τ(H) = 3`, `τ(H - e) ≤ 2`), in which every
vertex lies in at least `7` edges. -/
def transversalCriticalMinDegreeSeven : Prop :=
  ∃ (n : ℕ) (H : Finset (Finset (Fin n))), SetFamily.IsUniform H 3 ∧
    (∃ T : Finset (Fin n), T.card ≤ 3 ∧ ∀ f ∈ H, (f ∩ T).Nonempty) ∧
    (¬ ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ∀ f ∈ H, (f ∩ T).Nonempty) ∧
    (∀ e ∈ H, ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ∀ f ∈ H.erase e, (f ∩ T).Nonempty) ∧
    ∀ v : Fin n, 7 ≤ (H.filter (v ∈ ·)).card

/--
Resolved false for the transversal notion: Li proved that a `3`-uniform hypergraph with `τ(H) = 3`
and `τ(H - e) = 2` for every edge has at most `10` edges, so some vertex has degree at most `6`.
Source: T. F. Bloom, Erdős Problems, Problem #834, https://www.erdosproblems.com/834 (status
SOLVED); resolution: R. Li, On an Erdős-Lovász problem: 3-critical 3-graphs of minimum degree 7,
arXiv:2512.24850 (2025; unrefereed, accepted on erdosproblems.com/834), abstract and main theorem
for the transversal interpretation: a 3-uniform hypergraph H with τ(H) = 3 and τ(H - e) = 2 for
every edge e has at most 10 edges, in particular δ(H) ≤ 6, sharp for K₅⁽³⁾; erdosproblems.com/834:
'In the first formulation ... Li proves that a 3-critical 3-uniform hypergraph must have a vertex
of degree ≤ 6', https://arxiv.org/abs/2512.24850.
-/
public theorem_wanted transversalCriticalMinDegreeSeven_refuted :
    ¬ transversalCriticalMinDegreeSeven

end MathlibExt.Combinatorics.TransversalCriticalTripleSystemDegreeErdosProblem834Wanted
