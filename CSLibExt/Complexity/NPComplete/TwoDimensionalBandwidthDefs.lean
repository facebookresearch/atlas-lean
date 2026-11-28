/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 2-DIMENSIONAL BANDWIDTH: definitions

Source:
Z. Miller and J. B. Orlin, "NP-completeness for minimizing maximum edge length in grid
embeddings", Journal of Algorithms 6(1) (1985), 10-16, doi:10.1016/0196-6774(85)90016-1
(problem EDGE LENGTH);
S. N. Bhatt and S. S. Cosmadakis, "The complexity of minimizing wire lengths in VLSI
layouts", Information Processing Letters 25 (1987), 263-267,
doi:10.1016/0020-0190(87)90173-6 (the case `K = 1`, `G` a tree);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT40] BANDWIDTH (the one-dimensional
problem).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BandwidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoDimensionalBandwidth

open Bandwidth (BandwidthInstance)

/-- Some one-to-one map of the vertices into `ℤ²` puts the endpoints of every edge at `ℓ¹`
distance at most `K`. -/
def TwoDimensionalBandwidthFeasible (i : BandwidthInstance) : Prop :=
  ∃ f : Fin i.1 → StatMech.Lattice.Site 2, Function.Injective f ∧
    ∀ u v, (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).Adj u v →
      ∑ j, (f u j - f v j).natAbs ≤ i.2.2

open Classical in
/-- 2-DIMENSIONAL BANDWIDTH as a decision problem over bitstrings. -/
noncomputable def twoDimensionalBandwidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BandwidthInstance) x with
  | some i => decide (Bandwidth.WellFormed i ∧ TwoDimensionalBandwidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoDimensionalBandwidth
