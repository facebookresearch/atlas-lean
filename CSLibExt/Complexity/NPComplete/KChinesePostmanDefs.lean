/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# k-CHINESE POSTMAN: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MINIMUM K-CHINESE POSTMAN PROBLEM;
G. N. Frederickson, M. S. Hecht and C. E. Kim, "Approximation algorithms for some routing
problems", SIAM Journal on Computing 7 (1978), 178-193, doi:10.1137/0207017 (the k-person
minimax Chinese postman problem, among the NP-complete routing problems treated there).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ChinesePostmanMixedGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.KChinesePostman

open ChinesePostmanMixedGraphs (ChinesePostmanMixedGraphsInstance Step stepEnds stepLength)

/-- An instance: vertex count `n`, the edges `(u, v, l)`, the initial vertex `s`, the number `k`
of cycles, and the bound `K`. -/
abbrev KChinesePostmanInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The multigraph as a mixed graph with no directed edges, whose steps are reused. -/
def mixed (i : KChinesePostmanInstance) : ChinesePostmanMixedGraphsInstance :=
  (i.1, [], i.2.1, i.2.2.2.2)

/-- A closed walk from `s`, possibly empty: a list of undirected steps along edges of the
multigraph in which consecutive steps meet and, if the list is nonempty, the first step starts
at `s` and the last step ends at `s`. -/
def IsCycleFrom (i : KChinesePostmanInstance) (w : List Step) : Prop :=
  (∀ st ∈ w, st.1 = false ∧ st.2.1 < i.2.1.length) ∧
    w.IsChain (fun a b => (stepEnds (mixed i) a).2 = (stepEnds (mixed i) b).1) ∧
    (∀ st ∈ w.head?, (stepEnds (mixed i) st).1 = i.2.2.1) ∧
    ∀ st ∈ w.getLast?, (stepEnds (mixed i) st).2 = i.2.2.1

/-- Well-formedness of an instance: every edge joins vertices below `n`, `s` is a vertex, and `k`
and `K` are positive. -/
def WellFormed (i : KChinesePostmanInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1) ∧ i.2.2.1 < i.1 ∧ 0 < i.2.2.2.1 ∧ 0 < i.2.2.2.2

/-- Some `k` closed walks from `s`, possibly empty, each of length at most `K`, together traverse
every edge. -/
def KChinesePostmanFeasible (i : KChinesePostmanInstance) : Prop :=
  ∃ cycles : List (List Step), cycles.length = i.2.2.2.1 ∧
    (∀ w ∈ cycles, IsCycleFrom i w ∧ (w.map (stepLength (mixed i))).sum ≤ i.2.2.2.2) ∧
    ∀ j < i.2.1.length, ∃ w ∈ cycles, ∃ st ∈ w, st.2.1 = j

open Classical in
/-- k-CHINESE POSTMAN as a decision problem over bitstrings. -/
noncomputable def kChinesePostmanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KChinesePostmanInstance) x with
  | some i => decide (WellFormed i ∧ KChinesePostmanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.KChinesePostman
