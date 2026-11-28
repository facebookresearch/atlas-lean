/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BRIDGE-CONNECTIVITY AUGMENTATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND18] BICONNECTIVITY
AUGMENTATION, p. 210, comment: "The related problem in which G' must be bridge connected,
i.e., cannot be disconnected by removing a single edge, is also NP-complete";
K. P. Eswaran and R. E. Tarjan, "Augmentation problems", SIAM Journal on Computing 5 (1976),
653-665, doi:10.1137/0205044.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import CSLibExt.Complexity.NPComplete.BiconnectivityAugmentationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BridgeConnectivityAugmentation

/-- Well-formedness of an instance: `n ≥ 1`; the edge list is simple (in range, no loops, no
repeated edge in either orientation); `w` is an `n × n` symmetric matrix with positive
off-diagonal entries; and `B` is positive. -/
def WellFormed (i : BiconnectivityAugmentation.BiconnectivityAugmentationInstance) : Prop :=
  0 < i.1 ∧ i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1 ∧ (∀ row ∈ i.2.2.1, row.length = i.1) ∧
    (∀ u < i.1, ∀ v < i.1,
      BiconnectivityAugmentation.weight i.2.2.1 u v =
        BiconnectivityAugmentation.weight i.2.2.1 v u) ∧
    (∀ u < i.1, ∀ v < i.1, u ≠ v → 0 < BiconnectivityAugmentation.weight i.2.2.1 u v) ∧
    0 < i.2.2.2

/-- Some list `E'` of pairs of distinct vertices has total weight at most `B`, and adding its
pairs to `G` gives a bridge-connected graph. -/
def BridgeConnectivityAugmentationFeasible
    (i : BiconnectivityAugmentation.BiconnectivityAugmentationInstance) : Prop :=
  ∃ E' : List (ℕ × ℕ), (∀ e ∈ E', e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    (E'.map fun e => BiconnectivityAugmentation.weight i.2.2.1 e.1 e.2).sum ≤ i.2.2.2 ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1 ++ E')).IsEdgeConnected 2

open Classical in
/-- BRIDGE-CONNECTIVITY AUGMENTATION as a decision problem over bitstrings. -/
noncomputable def bridgeConnectivityAugmentationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BiconnectivityAugmentation.BiconnectivityAugmentationInstance) x with
  | some i => decide (WellFormed i ∧ BridgeConnectivityAugmentationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BridgeConnectivityAugmentation
