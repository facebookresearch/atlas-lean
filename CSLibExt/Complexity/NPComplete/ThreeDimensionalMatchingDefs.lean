/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-DIMENSIONAL MATCHING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), 3-DIMENSIONAL MATCHING;
R. M. Karp, "Reducibility among combinatorial problems" (1972).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatching

/-- **3-dimensional matching instances.** An instance of 3-DIMENSIONAL MATCHING is a pair $(n, T)$
of a natural number $n$, the part size, and a finite list $T$ of triples of natural numbers. -/
abbrev ThreeDimensionalMatchingInstance := ℕ × List (ℕ × ℕ × ℕ)

/-- **Well-formed 3-dimensional matching instances.** A 3-dimensional matching instance $(n, T)$
is well formed when each of the three coordinates of every triple in $T$ is less than $n$. -/
def WellFormed (i : ThreeDimensionalMatchingInstance) : Prop :=
  ∀ t ∈ i.2, t.1 < i.1 ∧ t.2.1 < i.1 ∧ t.2.2 < i.1

/-- **Feasible 3-dimensional matching instances.** A 3-dimensional matching instance $(n, T)$ is
feasible, or has a perfect matching, when there is a list $M$ of length $n$, obtained from the
list of triples $T$ by deleting some of its entries, such that for each of the three coordinate
positions, every natural number $a < n$ occurs in that position in exactly one triple of $M$. -/
def ThreeDimensionalMatchingFeasible
    (i : ThreeDimensionalMatchingInstance) : Prop :=
  ∃ matching : List (ℕ × ℕ × ℕ), matching.Sublist i.2 ∧ matching.length = i.1 ∧
    (∀ a < i.1, ∃! t ∈ matching, t.1 = a) ∧
    (∀ b < i.1, ∃! t ∈ matching, t.2.1 = b) ∧
    ∀ c < i.1, ∃! t ∈ matching, t.2.2 = c

open Classical in
/-- **3-DIMENSIONAL MATCHING as a decision problem.** The decision problem 3-DIMENSIONAL MATCHING
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
3-dimensional matching instance $(n, T)$ that is well formed (every coordinate of every triple in
$T$ is less than $n$) and feasible (it has a perfect matching). Bitstrings that do not decode to
an instance are rejected. -/
noncomputable def threeDimensionalMatchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ThreeDimensionalMatchingInstance) x with
  | some i => decide (WellFormed i ∧ ThreeDimensionalMatchingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeDimensionalMatching
