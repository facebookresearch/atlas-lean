/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COST-PARAMETRIC LINEAR PROGRAMMING for fixed q > 0: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [MP3] COST-PARAMETRIC LINEAR PROGRAMMING,
p. 245 ("Reference: [Jeroslow, 1976]. Transformation from 3SAT. Comment: Remains NP-complete for
any fixed q > 0."), crediting R. G. Jeroslow, "Bracketing discrete problems by two problems of
linear optimization", Proceedings of the First Symposium on Operations Research (Heidelberg),
Verlag Anton Hain, Meisenheim (1976), 205-216.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CostParametricLinearProgrammingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgrammingFixedQ

open MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgramming
  (CostParametricLinearProgrammingInstance qVal CostParametricLinearProgrammingFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.CostParametricLinearProgrammingFixedQ
