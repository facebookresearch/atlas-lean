/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPARATIVE DIVISIBILITY: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN4] COMPARATIVE DIVISIBILITY;
D. A. Plaisted, "Some polynomial and integer divisibility problems are NP-hard",
Proc. 17th Annual Symposium on Foundations of Computer Science (1976), 264-267,
doi:10.1109/SFCS.1976.29; journal version SIAM Journal on Computing 7 (1978), 458-464,
doi:10.1137/0207036.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibility

/-- An instance: the sequence `a₁, …, aₙ` and the sequence `b₁, …, bₘ`. -/
abbrev ComparativeDivisibilityInstance := List ℕ × List ℕ

/-- Well-formedness of an instance: every entry of both sequences is positive. -/
def WellFormed (i : ComparativeDivisibilityInstance) : Prop :=
  (∀ a ∈ i.1, 0 < a) ∧ ∀ b ∈ i.2, 0 < b

/-- Some positive integer `c` divides more entries of the first sequence than of the second,
counting entries with multiplicity. -/
def ComparativeDivisibilityFeasible (i : ComparativeDivisibilityInstance) : Prop :=
  ∃ c : ℕ, 0 < c ∧ i.2.countP (fun b => c ∣ b) < i.1.countP (fun a => c ∣ a)

open Classical in
/-- COMPARATIVE DIVISIBILITY as a decision problem over bitstrings. -/
noncomputable def comparativeDivisibilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ComparativeDivisibilityInstance) x with
  | some i => decide (WellFormed i ∧ ComparativeDivisibilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibility
