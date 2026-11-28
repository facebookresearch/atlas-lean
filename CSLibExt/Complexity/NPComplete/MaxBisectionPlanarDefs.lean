/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM BISECTION on planar graphs: definitions

Source:
K. Jansen, M. Karpinski, A. Lingas, and E. Seidel, "Polynomial time approximation schemes for
MAX-BISECTION on planar and geometric graphs", SIAM Journal on Computing 35 (2005), 110-119,
doi:10.1137/S009753970139567X (NP-hardness of exact MAX-BISECTION on planar graphs, credited
there to M. Jerrum, personal communication);
J. Díaz and M. Kamiński, "MAX-CUT and MAX-BISECTION are NP-hard on unit disk graphs",
Theoretical Computer Science 377 (2007), 271-276, doi:10.1016/j.tcs.2007.02.013 (records the
result: "max-bisection remains NP-hard on planar graphs (result of Jerrum presented in [JKLS])");
ISGCI, class "planar" (gc_43), problem Maximum bisection, NP-complete.
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxBisectionPlanar

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance)

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is planar, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧ (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsPlanar ∧ 0 < i.2.2

/-- A bisection: a side `A = S` with `|A| = ⌊|V| / 2⌋` (so `B = V - S` has `|B| = |A|` or
`|B| = |A| + 1`), and at least `K` edges with one endpoint in `A` and the other in `B`. -/
def MaxBisectionFeasible (i : MaxCutInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ v ∈ S, v < i.1) ∧ S.card = i.1 / 2 ∧
    ∃ cut : List (ℕ × ℕ), cut.Sublist i.2.1 ∧ i.2.2 ≤ cut.length ∧
      ∀ e ∈ cut, (e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S)

open Classical in
/-- MAXIMUM BISECTION on planar graphs as a decision problem over bitstrings. -/
noncomputable def maxBisectionPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxBisectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaxBisectionPlanar
