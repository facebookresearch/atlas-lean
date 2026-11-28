/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC SUM: definitions

Source:
E. Kubicka and A. J. Schwenk, "An introduction to chromatic sums", Proceedings of the 17th ACM
Annual Computer Science Conference (1989), 39-45, doi:10.1145/75427.75430;
D. Marx, "A short proof of the NP-completeness of minimum sum interval coloring", Operations
Research Letters 33(4) (2005), 382-384, doi:10.1016/j.orl.2004.07.006.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.PNat.Basic
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticSum

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`
(`GraphColoring.WellFormed`), and `0 < K`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2

/-- Some proper coloring of the graph by positive integers has sum at most `K`. -/
def ChromaticSumFeasible (i : GraphColoringInstance) : Prop :=
  ∃ c : (Graph i).Coloring ℕ+, ∑ v, (c v : ℕ) ≤ i.2.2

open Classical in
/-- CHROMATIC SUM as a decision problem over bitstrings. -/
noncomputable def chromaticSumDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ ChromaticSumFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChromaticSum
