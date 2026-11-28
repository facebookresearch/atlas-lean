/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN HEMISPHERE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP6] OPEN HEMISPHERE;
D. S. Johnson and F. P. Preparata, "The densest hemisphere problem", Theoretical
Computer Science 6 (1978), 93-107, doi:10.1016/0304-3975(78)90006-3.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OpenHemisphere

/-- An instance: the length `m` of the tuples, the list `X` of `m`-tuples of encoded integers,
and the bound `K`. -/
abbrev OpenHemisphereInstance := ℕ × List (List (ℕ × ℕ)) × ℕ

/-- The integer `p.1 - p.2` encoded by a pair of naturals. -/
def intOf (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- Well-formedness of an instance: every element of `X` is an `m`-tuple, the decoded integer
tuples are pairwise distinct (`X` is a set), and `0 < K ≤ |X|`. -/
def WellFormed (i : OpenHemisphereInstance) : Prop :=
  (∀ x ∈ i.2.1, x.length = i.1) ∧ (i.2.1.map fun x => x.map intOf).Nodup ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- A rational `m`-tuple `y` with `x · y > 0` for at least `K` elements `x` of `X`. -/
def OpenHemisphereFeasible (i : OpenHemisphereInstance) : Prop :=
  ∃ y : Fin i.1 → ℚ, i.2.2 ≤
    (i.2.1.filter fun x => 0 < ∑ j : Fin i.1, (intOf (x.getD j (0, 0)) : ℚ) * y j).length

open Classical in
/-- OPEN HEMISPHERE as a decision problem over bitstrings. -/
noncomputable def openHemisphereDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenHemisphereInstance) x with
  | some i => decide (WellFormed i ∧ OpenHemisphereFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OpenHemisphere
