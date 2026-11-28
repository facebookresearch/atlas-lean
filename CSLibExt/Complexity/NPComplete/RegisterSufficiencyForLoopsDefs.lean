/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGISTER SUFFICIENCY FOR LOOPS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO3] REGISTER
SUFFICIENCY FOR LOOPS;
M. R. Garey, D. S. Johnson, G. L. Miller, and C. H. Papadimitriou, "The
complexity of coloring circular arcs and chords", SIAM Journal on Algebraic and
Discrete Methods 1 (1980), 216-227, doi:10.1137/0601025.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegisterSufficiencyForLoops

/-- An instance: the loop length `N`, the list of variables as (start time, duration) pairs,
and the number `K` of registers. -/
abbrev RegisterSufficiencyForLoopsInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: `N`, every duration, and `K` are positive. -/
def WellFormed (i : RegisterSufficiencyForLoopsInstance) : Prop :=
  0 < i.1 ∧ (∀ v ∈ i.2.1, 0 < v.2) ∧ 0 < i.2.2

/-- Two variables `(s, l)` and `(s', l')` overlap on a loop of length `N`: some time slot is
occupied by both, modulo `N`. -/
def Overlap (N : ℕ) (u v : ℕ × ℕ) : Prop :=
  ∃ t₁ < u.2, ∃ t₂ < v.2, (u.1 + t₁) % N = (v.1 + t₂) % N

/-- An assignment of the variables to `K` registers in which distinct variables sharing a
register never overlap. -/
def RegisterSufficiencyForLoopsFeasible (i : RegisterSufficiencyForLoopsInstance) : Prop :=
  ∃ f : Fin i.2.1.length → Fin i.2.2, ∀ u v, u ≠ v → f u = f v →
    ¬ Overlap i.1 (i.2.1.get u) (i.2.1.get v)

open Classical in
/-- REGISTER SUFFICIENCY FOR LOOPS as a decision problem over bitstrings. -/
noncomputable def registerSufficiencyForLoopsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RegisterSufficiencyForLoopsInstance) x with
  | some i => decide (WellFormed i ∧ RegisterSufficiencyForLoopsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RegisterSufficiencyForLoops
