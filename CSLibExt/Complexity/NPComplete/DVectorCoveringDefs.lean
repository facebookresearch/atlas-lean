/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# D-VECTOR COVERING: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, web edition
(2000), problem MAXIMUM D-VECTOR COVERING (decision version);
S. F. Assmann, D. S. Johnson, D. J. Kleitman and J. Y.-T. Leung, "On a dual version of the
one-dimensional bin packing problem", Journal of Algorithms 5(4) (1984), 502-525,
doi:10.1016/0196-6774(84)90004-x (bin covering, the case `d = 1`; the paper was not available,
and its NP-hardness result is the one recorded by J. Csirik, J. B. G. Frenk, M. Labbé and
S. Zhang, "Two simple algorithms for bin covering", Acta Cybernetica 14(1) (1999), 13-25).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DVectorCovering

/-- An instance: the dimension `d`, the vectors of `X` (each a list of `d` components
`(numerator, denominator)`), and the bound `K`. -/
abbrev DVectorCoveringInstance := ℕ × List (List (ℕ × ℕ)) × ℕ

/-- The rational number `p / q` encoded by the pair `(p, q)`. -/
def toRat (q : ℕ × ℕ) : ℚ := (q.1 : ℚ) / (q.2 : ℚ)

/-- Well-formedness of an instance: `d` is positive, every vector has `d` components, each in
`[0, 1]` with a positive denominator, and `K` is positive. -/
def WellFormed (i : DVectorCoveringInstance) : Prop :=
  0 < i.1 ∧ (∀ x ∈ i.2.1, x.length = i.1 ∧ ∀ q ∈ x, 0 < q.2 ∧ q.1 ≤ q.2) ∧ 0 < i.2.2

/-- The `t`-th component of the vector at position `j` of `X`. -/
def component (i : DVectorCoveringInstance) (j : Fin i.2.1.length) (t : ℕ) : ℚ :=
  toRat ((i.2.1.get j).getD t (0, 1))

/-- The vectors at the positions in `S` form a unit cover: for every coordinate `t < d`, their
`t`-th components sum to at least `1`. -/
def IsUnitCover (i : DVectorCoveringInstance) (S : Finset (Fin i.2.1.length)) : Prop :=
  ∀ t < i.1, 1 ≤ ∑ j ∈ S, component i j t

open Classical in
/-- Some partition of `X` into subsets `S₀, …, Sₘ₋₁` (the preimages of a map `f` from positions
to `Fin m`) has at least `K` unit covers among its subsets. -/
def DVectorCoveringFeasible (i : DVectorCoveringInstance) : Prop :=
  ∃ (m : ℕ) (f : Fin i.2.1.length → Fin m),
    i.2.2 ≤ (Finset.univ.filter fun s : Fin m =>
      IsUnitCover i (Finset.univ.filter fun j => f j = s)).card

open Classical in
/-- D-VECTOR COVERING as a decision problem over bitstrings. -/
noncomputable def dVectorCoveringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DVectorCoveringInstance) x with
  | some i => decide (WellFormed i ∧ DVectorCoveringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DVectorCovering
