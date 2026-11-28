/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEFECTIVE SORTING NETWORK: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3(3)
(1982), 288-300, doi:10.1016/0196-6774(82)90026-8, problem [7] DEFECTIVE SORTING NETWORK
(credited there to M. O. Rabin, private communication (1981), a transformation from
3-DIMENSIONAL MATCHING; the original was not available);
I. Parberry, "On the computational complexity of optimal sorting network verification", in
*PARLE '91 Parallel Architectures and Languages Europe*, Lecture Notes in Computer Science 506
(1991), 252-269, doi:10.1007/978-3-662-25209-3_18 (problem NONSORT: "Is there an input which C
does not sort?", proved NP-complete).
-/
module

public import CSLibExt.Algorithms.Lean.SortingNetworks.ZeroOne
public import Mathlib.Data.Int.Order.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DefectiveSortingNetwork

/-- An instance: the number `n` of variables and the statements `(i, j)` in program order. -/
abbrev DefectiveSortingNetworkInstance := ℕ × List (ℕ × ℕ)

/-- Well-formedness of an instance: every statement `(i, j)` has `i < j < n`. -/
def WellFormed (i : DefectiveSortingNetworkInstance) : Prop :=
  ∀ c ∈ i.2, c.1 < c.2 ∧ c.2 < i.1

/-- The program as a comparator network on `n` wires (statements with an index out of range,
which `WellFormed` excludes, are dropped). -/
def network (i : DefectiveSortingNetworkInstance) :
    Cslib.Algorithms.Lean.SortingNetworks.Network i.1 :=
  i.2.filterMap fun c =>
    if h : c.1 < i.1 ∧ c.2 < i.1 then some (⟨c.1, h.1⟩, ⟨c.2, h.2⟩) else none

/-- Some integer input is not sorted into nondecreasing order by the program. -/
def DefectiveSortingNetworkFeasible (i : DefectiveSortingNetworkInstance) : Prop :=
  ¬ Cslib.Algorithms.Lean.SortingNetworks.Sorts (network i) ℤ

open Classical in
/-- DEFECTIVE SORTING NETWORK as a decision problem over bitstrings. -/
noncomputable def defectiveSortingNetworkDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DefectiveSortingNetworkInstance) x with
  | some i => decide (WellFormed i ∧ DefectiveSortingNetworkFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DefectiveSortingNetwork
