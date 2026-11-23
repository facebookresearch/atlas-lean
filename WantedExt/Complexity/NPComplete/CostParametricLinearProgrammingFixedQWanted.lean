/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COST-PARAMETRIC LINEAR PROGRAMMING for fixed q > 0 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [MP3] COST-PARAMETRIC LINEAR PROGRAMMING,
p. 245 ("Reference: [Jeroslow, 1976]. Transformation from 3SAT. Comment: Remains NP-complete for
any fixed q > 0."), crediting R. G. Jeroslow, "Bracketing discrete problems by two problems of
linear optimization", Proceedings of the First Symposium on Operations Research (Heidelberg),
Verlag Anton Hain, Meisenheim (1976), 205-216.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CostParametricLinearProgrammingWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgrammingFixedQ

open MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgramming
  (CostParametricLinearProgrammingInstance qVal CostParametricLinearProgrammingFeasible)

/-!
# COST-PARAMETRIC LINEAR PROGRAMMING for fixed q > 0 is NP-complete

For a fixed positive rational `q`: COST-PARAMETRIC LINEAR PROGRAMMING ([MP3],
`CostParametricLinearProgrammingWanted`) restricted to instances whose bound is `q`.
INSTANCE: a finite set `X` of pairs `(x, b)`, where `x` is an `m`-tuple of integers and `b` is an
integer, and a set `J ⊆ {1, 2, …, m}`. QUESTION: is there an `m`-tuple `c` with rational entries
such that `(c · c)^{1/2} ≤ q` and such that, if `Y` is the set of all `m`-tuples `y` with
non-negative rational entries satisfying `x · y ≥ b` for all `(x, b) ∈ X`, then the minimum of
`∑_{j ∈ J} cⱼ yⱼ` over all `y ∈ Y` exceeds `½ max {|cⱼ| : j ∈ J} + ∑_{j ∈ J} min {0, cⱼ}`?

The instance and the question are those of `CostParametricLinearProgrammingWanted`; `q` is a
parameter of the decision problem and of the theorem, and `WellFormed q` requires the encoded
bound of the instance to equal `q` (as a rational number, whatever numerator and denominator
encode it).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance for the fixed bound `q`: the [MP3] well-formedness, and the
instance's bound is `q`. -/
def WellFormed (q : ℚ) (i : CostParametricLinearProgrammingInstance) : Prop :=
  CostParametricLinearProgramming.WellFormed i ∧ qVal i = q

open Classical in
/-- COST-PARAMETRIC LINEAR PROGRAMMING with the bound fixed to `q` as a decision problem over
bitstrings. -/
noncomputable def costParametricLinearProgrammingFixedQDec (q : ℚ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CostParametricLinearProgrammingInstance) x with
  | some i => decide (WellFormed q i ∧ CostParametricLinearProgrammingFeasible i)
  | none => false

/-- **COST-PARAMETRIC LINEAR PROGRAMMING is NP-complete for every fixed `q > 0`.** Source: Garey
and Johnson (1979), [MP3], comment; Jeroslow (1976). -/
public theorem_wanted costParametricLinearProgrammingFixedQ_npComplete (q : ℚ) (hq : 0 < q) :
    costParametricLinearProgrammingFixedQDec q ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (costParametricLinearProgrammingFixedQDec q)

end MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgrammingFixedQ
