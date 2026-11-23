/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ORIENTEERING is NP-complete

Source:
B. L. Golden, L. Levy and R. Vohra, "The orienteering problem", Naval Research Logistics 34
(1987), 307-318, doi:10.1002/1520-6750(198706)34:3<307::AID-NAV3220340302>3.0.CO;2-D (the problem
and the NP-hardness of its optimization version);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH, pp. 199-200 (comment: the
variants in which the starting point or the ending point or both are specified are also
NP-complete), for the reduction to this decision version given in the module docstring.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Orienteering

/-!
# ORIENTEERING is NP-complete

INSTANCE: a complete graph on vertices `0, …, n - 1` with a travel time `t_uv ∈ ℤ₀⁺` on each
edge `{u, v}`, a start vertex `s` and a different end vertex `t`, a score `r_v ∈ ℤ₀⁺` at each
vertex other than `s` and `t`, a time limit `T` and a target score `S`.
QUESTION: is there a path from `s` to `t` (visiting each vertex at most once) whose total travel
time is at most `T` and whose visited vertices have total score at least `S`?

This is the decision version of Golden, Levy and Vohra's orienteering problem: start and end
points are specified, the other locations have scores, and the competitor visits, within the
time limit, a subset of the locations on the way from the start to the end so as to maximize the
total score. The graph is Mathlib's complete graph `⊤ : SimpleGraph (Fin n)`, the route is a
`SimpleGraph.Walk` with `Walk.IsPath`, its travel time is the sum of the travel times of its
darts and its score is the sum of the scores of its support (the visited vertices). Only the
locations other than the start and the end have scores in Golden, Levy and Vohra's formulation,
so the score list gives `s` and `t` the score `0`. Travel times are given as an `n × n` matrix
that is symmetric, so each edge has one travel time; the diagonal is unused.

Golden, Levy and Vohra show that the orienteering problem is NP-hard. For this decision version:
it is in NP, since a certificate is the vertex sequence of the path (at most `n` vertices), and
checking that it starts at `s`, ends at `t`, repeats no vertex, and meets the time and score
bounds takes polynomial time. It is NP-hard by a reduction from HAMILTONIAN PATH with both
endpoints specified ([GT39]): for a graph on `n` vertices with specified `s ≠ t`, give `s` and `t`
score `0` and the other vertices score `1`, travel time `1` on edges and `2` on non-edges,
`T = n - 1` and `S = n - 2`. A path with score `n - 2` visits all `n` vertices, so it has `n - 1`
darts, and time at most `n - 1` forces every dart to be an edge; conversely a Hamiltonian
`s`-`t` path has time `n - 1` and score `n - 2`. Numbers are written in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of vertices, the travel-time matrix (row `u`, column `v`), the
start `s`, the end `t`, the scores, the time limit `T` and the target score `S`. -/
abbrev OrienteeringInstance := ℕ × List (List ℕ) × ℕ × ℕ × List ℕ × ℕ × ℕ

/-- The travel time between `u` and `v`. -/
def travelTime (i : OrienteeringInstance) (u v : ℕ) : ℕ :=
  (i.2.1.getD u []).getD v 0

/-- The score of vertex `v`. -/
def score (i : OrienteeringInstance) (v : ℕ) : ℕ :=
  i.2.2.2.2.1.getD v 0

/-- Well-formedness of an instance: the travel-time matrix is `n × n` and symmetric, `s` and
`t` are different vertices, there is one score per vertex, and `s` and `t` have score `0`. -/
def WellFormed (i : OrienteeringInstance) : Prop :=
  i.2.1.length = i.1 ∧ (∀ row ∈ i.2.1, row.length = i.1) ∧
    (∀ u < i.1, ∀ v < i.1, travelTime i u v = travelTime i v u) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ i.2.2.1 ≠ i.2.2.2.1 ∧ i.2.2.2.2.1.length = i.1 ∧
    score i i.2.2.1 = 0 ∧ score i i.2.2.2.1 = 0

/-- There is a path from `s` to `t` in the complete graph whose total travel time is at most
`T` and whose visited vertices have total score at least `S`. -/
def OrienteeringFeasible (i : OrienteeringInstance) : Prop :=
  ∃ (u v : Fin i.1) (W : (⊤ : SimpleGraph (Fin i.1)).Walk u v),
    (u : ℕ) = i.2.2.1 ∧ (v : ℕ) = i.2.2.2.1 ∧ W.IsPath ∧
      (W.darts.map fun d => travelTime i d.fst d.snd).sum ≤ i.2.2.2.2.2.1 ∧
      i.2.2.2.2.2.2 ≤ (W.support.map fun w : Fin i.1 => score i w).sum

open Classical in
/-- ORIENTEERING as a decision problem over bitstrings. -/
noncomputable def orienteeringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OrienteeringInstance) x with
  | some i => decide (WellFormed i ∧ OrienteeringFeasible i)
  | none => false

/-- **ORIENTEERING is NP-complete.** Source: Golden, Levy and Vohra (1987) (problem, NP-hardness);
Garey and Johnson (1979), [GT39] (reduction in the module docstring). -/
public theorem_wanted orienteering_npComplete :
    orienteeringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L orienteeringDec

end MetaMathlibExt.Complexity.NPComplete.Orienteering
