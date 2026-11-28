/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.SortingNetworks.ZeroOne
public import Mathlib.Data.Int.Order.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

/-!
# DEFECTIVE SORTING NETWORK: definitions

INSTANCE: a sequence `x₁, x₂, …, xₙ` of input variables and a program `P` consisting of a
sequence of statements of the form "if `xᵢ ≥ xⱼ`, then interchange their values", where `i < j`.
QUESTION: is there an input to program `P` which `P` fails to sort into nondecreasing order,
i.e., are there integer input values `xᵢ = zᵢ`, `1 ≤ i ≤ n`, and an index `k`, `1 ≤ k < n`,
such that, after program `P` has been executed, `x_k > x_{k+1}`?

The program is a comparator network in the sense of
`CSLibExt.Algorithms.Lean.SortingNetworks.ZeroOne` (Knuth, *The Art of Computer Programming*,
Vol. 3, Section 5.3.4, as in Johnson's column): the comparator `(i, j)`
(`Cslib.Algorithms.Lean.SortingNetworks.comparator`) puts the minimum of wires `i` and `j` on
wire `i` and the maximum on wire `j`, which for `i < j` is the statement "if `xᵢ ≥ xⱼ`, then
interchange their values" (an interchange of equal values changes nothing), and `run` executes
the statements in order. The question is the negation of `Sorts (network i) ℤ`: some integer
input has an output that is not monotone in the wire order. For outputs indexed by `Fin n`,
monotone is equivalent to `x_k ≤ x_{k+1}` for all consecutive `k` (`Fin.monotone_iff_le_succ`),
so this is the source's question.

The variables are indexed `0, …, n - 1` and the program is a list of index pairs `(i, j)`;
`WellFormed` asks `i < j < n` for every statement (statements may repeat). Membership in NP:
the certificate is the input (by the 0-1 principle, a `0`/`1` input suffices).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

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
