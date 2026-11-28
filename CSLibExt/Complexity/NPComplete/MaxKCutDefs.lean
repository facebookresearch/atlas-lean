/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAXIMUM k-CUT: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MAXIMUM k-CUT (the `k =
2` slice is MAX CUT).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxKCut

/-- **Instances of MAXIMUM k-CUT.** An instance of MAXIMUM k-CUT is a quadruple $(n, E, k, K)$ of
a natural number $n$ (the number of vertices), a finite list $E$ of ordered pairs of natural
numbers (the edges), a natural number $k$ (the number of parts) and a natural number $K$ (the
bound). -/
abbrev MaxKCutInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- **Well-formed MAXIMUM k-CUT instances.** An instance $(n, E, k, K)$ of MAXIMUM k-CUT is well
formed when the list $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies
$u < n$, $v < n$ and $u \ne v$, and the reversed pair $(v, u)$ does not occur in $E$. -/
def WellFormed (i : MaxKCutInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1)

/-- **Feasible MAXIMUM k-CUT instances.** An instance $(n, E, k, K)$ of MAXIMUM k-CUT is feasible
when there are a list $(a_0, \dots, a_{n-1})$ of $n$ natural numbers, each less than $k$, and a
list $C$ of length at least $K$ obtained from $E$ by deleting zero or more of its entries, such
that $a_u \ne a_v$ for every pair $(u, v)$ in $C$, where $a_w$ is read as $0$ when $w \ge n$. -/
def MaxKCutFeasible
    (i : MaxKCutInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1 ∧ (∀ v < i.1, assign.getD v 0 < i.2.2.1) ∧
    ∃ cut : List (ℕ × ℕ), cut.Sublist i.2.1 ∧ i.2.2.2 ≤ cut.length ∧
      ∀ e ∈ cut, assign.getD e.1 0 ≠ assign.getD e.2 0

open Classical in
/-- **MAXIMUM k-CUT as a decision problem.** The decision problem MAXIMUM k-CUT accepts a
bitstring $x$ exactly when decoding $x$ with the canonical bitstring encoding of instances of
MAXIMUM k-CUT succeeds and yields an instance that is well formed and feasible. All other
bitstrings, including those that fail to decode, are rejected. -/
noncomputable def maxKCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxKCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxKCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaxKCut
