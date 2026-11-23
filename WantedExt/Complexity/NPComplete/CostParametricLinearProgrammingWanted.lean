/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COST-PARAMETRIC LINEAR PROGRAMMING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [MP3] COST-PARAMETRIC LINEAR PROGRAMMING,
p. 245, crediting R. G. Jeroslow, "Bracketing discrete problems by two problems of linear
optimization", Proceedings of the First Symposium on Operations Research (Heidelberg), Verlag
Anton Hain, Meisenheim (1976), 205-216 (transformation from 3SAT).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Bounds.Defs
public import WantedExt.Complexity.NPComplete.IntegerProgrammingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgramming

open MetaMathlibExt.Complexity.NPComplete.IntegerProgramming (toInt)

/-!
# COST-PARAMETRIC LINEAR PROGRAMMING is NP-complete

INSTANCE: a finite set `X` of pairs `(x, b)`, where `x` is an `m`-tuple of integers and `b` is an
integer, a set `J ⊆ {1, 2, …, m}`, and a positive rational number `q`.
QUESTION: is there an `m`-tuple `c` with rational entries such that `(c · c)^{1/2} ≤ q` and such
that, if `Y` is the set of all `m`-tuples `y` with non-negative rational entries satisfying
`x · y ≥ b` for all `(x, b) ∈ X`, then the minimum of `∑_{j ∈ J} cⱼ yⱼ` over all `y ∈ Y` exceeds
`½ max {|cⱼ| : j ∈ J} + ∑_{j ∈ J} min {0, cⱼ}`?

Conventions. Coordinates are `0`-based, so `J ⊆ {0, …, m - 1}`. `(c · c)^{1/2} ≤ q` is stated as
`c · c ≤ q²`, which is equivalent because both sides of the original are nonnegative. "The
minimum ... exceeds `T`" is stated as: the set of values `{∑_{j ∈ J} cⱼ yⱼ : y ∈ Y}` has a least
element (Mathlib's `IsLeast`) and it is greater than `T`; when `Y` is empty or the objective is
unbounded below there is no minimum. `max {|cⱼ| : j ∈ J}` needs `J ≠ ∅`, which `WellFormed`
requires; it is computed as `Finset.fold max 0`, which equals the maximum because every `|cⱼ|` is
nonnegative.

Encoding: `X` is a list of constraints in the encoding of INTEGER PROGRAMMING
(`IntegerProgramming.toInt` reads an integer from a `(positive part, negative part)` pair), `J`
is a list of coordinates, and `q` is a pair `(numerator, denominator)` of positive naturals. The
instance is decoded from a bitstring with the repository's canonical
`MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and bitstrings decoding to malformed
instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **COST-PARAMETRIC LINEAR PROGRAMMING is NP-complete.** Source: Garey and Johnson (1979),
[MP3]; Jeroslow (1976). -/
public theorem_wanted costParametricLinearProgramming_npComplete :
    costParametricLinearProgrammingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L costParametricLinearProgrammingDec

end MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgramming
