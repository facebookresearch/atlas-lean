/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COST-PARAMETRIC LINEAR PROGRAMMING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [MP3] COST-PARAMETRIC LINEAR PROGRAMMING,
p. 245, crediting R. G. Jeroslow, "Bracketing discrete problems by two problems of linear
optimization", Proceedings of the First Symposium on Operations Research (Heidelberg), Verlag
Anton Hain, Meisenheim (1976), 205-216 (transformation from 3SAT).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Bounds.Defs
public import CSLibExt.Complexity.NPComplete.IntegerProgrammingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgramming

open MetaMathlibExt.Complexity.NPComplete.IntegerProgramming (toInt)

/-- An instance: the dimension `m`, the constraint pairs `(x, b)`, the coordinate list `J`, and
`q` as `(numerator, denominator)`. -/
abbrev CostParametricLinearProgrammingInstance :=
  ℕ × List (List (ℕ × ℕ) × (ℕ × ℕ)) × List ℕ × (ℕ × ℕ)

/-- The coordinates in `J`, as a `Finset` of `Fin m`. -/
def coords (i : CostParametricLinearProgrammingInstance) : Finset (Fin i.1) :=
  Finset.univ.filter fun j => (j : ℕ) ∈ i.2.2.1

/-- The rational number `q`. -/
def qVal (i : CostParametricLinearProgrammingInstance) : ℚ :=
  (i.2.2.2.1 : ℚ) / i.2.2.2.2

/-- The feasible set `Y`: non-negative rational `m`-tuples `y` with `x · y ≥ b` for all
`(x, b) ∈ X`. -/
def feasibleSet (i : CostParametricLinearProgrammingInstance) : Set (Fin i.1 → ℚ) :=
  {y | (∀ j, 0 ≤ y j) ∧
    ∀ xb ∈ i.2.1, (toInt xb.2 : ℚ) ≤ ∑ j : Fin i.1, (toInt (xb.1.getD j (0, 0)) : ℚ) * y j}

/-- The threshold `½ max {|cⱼ| : j ∈ J} + ∑_{j ∈ J} min {0, cⱼ}`. -/
def threshold (i : CostParametricLinearProgrammingInstance) (c : Fin i.1 → ℚ) : ℚ :=
  (coords i).fold max 0 (fun j => |c j|) / 2 + ∑ j ∈ coords i, min 0 (c j)

/-- Well-formedness of an instance: every tuple has length `m`, `J` is a nonempty set of
coordinates below `m`, and `q` is positive. -/
def WellFormed (i : CostParametricLinearProgrammingInstance) : Prop :=
  (∀ xb ∈ i.2.1, xb.1.length = i.1) ∧ i.2.2.1 ≠ [] ∧ (∀ j ∈ i.2.2.1, j < i.1) ∧
    0 < i.2.2.2.1 ∧ 0 < i.2.2.2.2

/-- A rational cost vector `c` with `c · c ≤ q²` for which the minimum of `∑_{j ∈ J} cⱼ yⱼ` over
`Y` exists and exceeds the threshold. -/
def CostParametricLinearProgrammingFeasible (i : CostParametricLinearProgrammingInstance) :
    Prop :=
  ∃ c : Fin i.1 → ℚ, ∑ j, c j * c j ≤ qVal i ^ 2 ∧
    ∃ μ : ℚ, IsLeast ((fun y => ∑ j ∈ coords i, c j * y j) '' feasibleSet i) μ ∧
      threshold i c < μ

open Classical in
/-- COST-PARAMETRIC LINEAR PROGRAMMING as a decision problem over bitstrings. -/
noncomputable def costParametricLinearProgrammingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CostParametricLinearProgrammingInstance) x with
  | some i => decide (WellFormed i ∧ CostParametricLinearProgrammingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgramming
