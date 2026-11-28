/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST COMMON SUPERSTRING over a binary alphabet: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR9] SHORTEST COMMON SUPERSTRING,
p. 228, comment: "Remains NP-complete even if |Σ| = 2";
J. Gallant, D. Maier, and J. A. Storer, "On finding minimal length superstrings", Journal of
Computer and System Sciences 20 (1980), 50-58, doi:10.1016/0022-0000(80)90004-5.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ShortestCommonSuperstringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstringBinary

/-- Well-formedness of an instance: the instance is well-formed for SHORTEST COMMON
SUPERSTRING, and the alphabet has two symbols. -/
def WellFormed (i : ShortestCommonSuperstring.ShortestCommonSuperstringInstance) : Prop :=
  ShortestCommonSuperstring.WellFormed i ∧ i.1 = 2

open Classical in
/-- SHORTEST COMMON SUPERSTRING over a binary alphabet as a decision problem over bitstrings. -/
noncomputable def shortestCommonSuperstringBinaryDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestCommonSuperstring.ShortestCommonSuperstringInstance) x with
  | some i =>
      decide (WellFormed i ∧ ShortestCommonSuperstring.ShortestCommonSuperstringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstringBinary
