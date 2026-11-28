/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISTINGUISHING STRING SELECTION: definitions

Source:
J. K. Lanctot, M. Li, B. Ma, S. Wang, and L. Zhang, "Distinguishing string
selection problems", Information and Computation 185 (2003), 41-55,
doi:10.1016/S0890-5401(03)00057-9 (preliminary version: Proc. 10th ACM-SIAM SODA
(1999)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.InformationTheory.Hamming

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DistinguishingStringSelection

/-- An instance: alphabet size `q` (symbols `0, ..., q - 1`), string length `L`, the bad strings,
the good strings, `k_b`, `k_g`. -/
abbrev DistinguishingStringSelectionInstance :=
  ℕ × ℕ × List (List ℕ) × List (List ℕ) × ℕ × ℕ

/-- A string read as a function on positions `Fin L`. -/
def asWord (L : ℕ) (s : List ℕ) : Fin L → ℕ := fun k => s.getD k 0

/-- A string over the alphabet `{0, ..., q - 1}` of length `L`. -/
def IsWord (q L : ℕ) (s : List ℕ) : Prop :=
  s.length = L ∧ ∀ a ∈ s, a < q

/-- Well-formedness of an instance: every bad and every good string has length `L` over the
alphabet `{0, ..., q - 1}`. -/
def WellFormed (i : DistinguishingStringSelectionInstance) : Prop :=
  (∀ s ∈ i.2.2.1, IsWord i.1 i.2.1 s) ∧ ∀ s ∈ i.2.2.2.1, IsWord i.1 i.2.1 s

/-- A string `t ∈ Σ^L` within Hamming distance `k_b` of every bad string and at Hamming distance
at least `k_g` from every good string. -/
def DistinguishingStringSelectionFeasible
    (i : DistinguishingStringSelectionInstance) : Prop :=
  ∃ t : List ℕ, IsWord i.1 i.2.1 t ∧
    (∀ s ∈ i.2.2.1, hammingDist (asWord i.2.1 t) (asWord i.2.1 s) ≤ i.2.2.2.2.1) ∧
    ∀ s ∈ i.2.2.2.1, i.2.2.2.2.2 ≤ hammingDist (asWord i.2.1 t) (asWord i.2.1 s)

open Classical in
/-- DISTINGUISHING STRING SELECTION as a decision problem over bitstrings. -/
noncomputable def distinguishingStringSelectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DistinguishingStringSelectionInstance) x with
  | some i => decide (WellFormed i ∧ DistinguishingStringSelectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DistinguishingStringSelection
