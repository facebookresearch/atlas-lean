/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CYCLIC ORDERING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS2] CYCLIC ORDERING;
Z. Galil and N. Megiddo, "Cyclic ordering is NP-complete", Theoretical Computer
Science 5 (1977), 179-182, doi:10.1016/0304-3975(77)90005-6.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CyclicOrdering

/-- An instance: the size `n` of `A = Fin n` and the triples of `C`. -/
abbrev CyclicOrderingInstance := ℕ × List (ℕ × ℕ × ℕ)

/-- Well-formedness of an instance: every triple consists of three distinct elements of `A`. -/
def WellFormed (i : CyclicOrderingInstance) : Prop :=
  ∀ t ∈ i.2, t.1 < i.1 ∧ t.2.1 < i.1 ∧ t.2.2 < i.1 ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2

/-- Some one-to-one `f : A → Fin n` puts every triple `(a, b, c)` of `C` in cyclic order:
`f a < f b < f c`, `f b < f c < f a`, or `f c < f a < f b`. -/
def CyclicOrderingFeasible (i : CyclicOrderingInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.1, Function.Injective f ∧
    ∀ a b c : Fin i.1, ((a : ℕ), (b : ℕ), (c : ℕ)) ∈ i.2 →
      (f a < f b ∧ f b < f c) ∨ (f b < f c ∧ f c < f a) ∨ (f c < f a ∧ f a < f b)

open Classical in
/-- CYCLIC ORDERING as a decision problem over bitstrings. -/
noncomputable def cyclicOrderingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CyclicOrderingInstance) x with
  | some i => decide (WellFormed i ∧ CyclicOrderingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CyclicOrdering
