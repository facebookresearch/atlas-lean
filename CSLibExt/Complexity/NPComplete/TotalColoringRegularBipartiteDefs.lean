/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOTAL COLORING OF REGULAR BIPARTITE GRAPHS is NP-complete for every fixed k ≥ 3: definitions

Source:
C. J. H. McDiarmid and A. Sánchez-Arroyo, "Total colouring regular bipartite graphs is
NP-hard", Discrete Mathematics 124 (1994), 155-162, doi:10.1016/0012-365X(92)00058-Y;
A. Sánchez-Arroyo, "Determining the total colouring number is NP-hard", Discrete Mathematics
78 (1989), 315-319, doi:10.1016/0012-365X(89)90187-8.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TotalColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TotalColoringRegularBipartite

open MetaMathlibExt.Complexity.NPComplete.TotalColoring (TotalColoringInstance Graph)

open Classical in
/-- Well-formedness of an instance for the fixed degree `k`: a well-formed TOTAL COLORING
instance whose number of colors is `k + 1` and whose graph is nonempty, `k`-regular and
bipartite. -/
def WellFormed (k : ℕ) (i : TotalColoringInstance) : Prop :=
  TotalColoring.WellFormed i ∧ i.2.2 = k + 1 ∧ 0 < i.1 ∧ (Graph i).IsRegularOfDegree k ∧
    (Graph i).IsBipartite

open Classical in
/-- TOTAL COLORING OF `k`-REGULAR BIPARTITE GRAPHS with `k + 1` colors, for the fixed degree
`k`, as a decision problem over bitstrings. -/
noncomputable def totalColoringRegularBipartiteDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := TotalColoringInstance) x with
  | some i => decide (WellFormed k i ∧ TotalColoring.TotalColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TotalColoringRegularBipartite
