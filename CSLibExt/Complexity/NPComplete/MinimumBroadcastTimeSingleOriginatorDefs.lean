/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM BROADCAST TIME with a single originator: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND49] MINIMUM BROADCAST TIME,
p. 219 (comment: "The special case where `|V₀| = 1` remains NP-complete");
P. J. Slater, E. J. Cockayne and S. T. Hedetniemi, "Information dissemination in trees", SIAM
Journal on Computing 10 (1981), 692-701, doi:10.1137/0210052.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumBroadcastTimeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTimeSingleOriginator

open MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTime (MinimumBroadcastTimeInstance)

/-- Well-formedness of an instance: a well-formed MINIMUM BROADCAST TIME instance whose base set
`V₀` is a single vertex. -/
def WellFormed (i : MinimumBroadcastTimeInstance) : Prop :=
  MinimumBroadcastTime.WellFormed i ∧ i.2.2.1.length = 1

open Classical in
/-- MINIMUM BROADCAST TIME with a single originator as a decision problem over bitstrings. -/
noncomputable def minimumBroadcastTimeSingleOriginatorDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MinimumBroadcastTimeInstance) x with
  | some i => decide (WellFormed i ∧ MinimumBroadcastTime.MinimumBroadcastTimeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinimumBroadcastTimeSingleOriginator
