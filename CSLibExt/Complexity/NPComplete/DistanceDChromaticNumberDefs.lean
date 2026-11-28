/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISTANCE-d CHROMATIC NUMBER (fixed d ≥ 2): definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3(2)
(1982), 182-195, doi:10.1016/0196-6774(82)90018-9, problem DISTANCE-d CHROMATIC NUMBER;
S. T. McCormick, "Optimal approximation of sparse Hessians and its equivalence to a graph
coloring problem", Mathematical Programming 26(2) (1983), 153-171, doi:10.1007/BF02592052;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (the case `d = 1`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DistanceDChromaticNumber

/-- Well-formedness of an instance `(n, E, K)`: the edge list describes a simple graph on
`Fin n` (`GraphColoring.WellFormed`) and `0 < K ≤ n`. -/
def WellFormed (i : GraphColoring.GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- There is a partition of the vertices into `K` blocks (`c v` is the block of `v`) such that
no two distinct vertices of a block are joined by a path of length `d` or less. -/
def DistanceDChromaticNumberFeasible (d : ℕ) (i : GraphColoring.GraphColoringInstance) :
    Prop :=
  ∃ c : Fin i.1 → Fin i.2.2, ∀ u v : Fin i.1, u ≠ v → c u = c v →
    ∀ p : (GraphColoring.Graph i).Walk u v, p.IsPath → d < p.length

open Classical in
/-- DISTANCE-`d` CHROMATIC NUMBER as a decision problem over bitstrings. -/
noncomputable def distanceDChromaticNumberDec (d : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoring.GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ DistanceDChromaticNumberFeasible d i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DistanceDChromaticNumber
