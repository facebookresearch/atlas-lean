/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST COMMON SUPERSTRING with short repetition-free strings: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR9] SHORTEST COMMON SUPERSTRING,
p. 228, comment: "Remains NP-complete even if ... all x ∈ R have |x| ≤ 8 and contain no
repeated symbols", reference [Maier and Storer, 1977], Report No. 233, Princeton University;
J. Gallant, D. Maier and J. A. Storer, "On finding minimal length superstrings", Journal of
Computer and System Sciences 20 (1980), 50-58, doi:10.1016/0022-0000(80)90004-5.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ShortestCommonSuperstringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstringShortRepetitionFree

open MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstring
  (ShortestCommonSuperstringInstance ShortestCommonSuperstringFeasible)

/-- Well-formedness of an instance: the instance is well-formed for SHORTEST COMMON
SUPERSTRING, and every string of `R` has length at most `8` and no repeated symbol. -/
def WellFormed (i : ShortestCommonSuperstringInstance) : Prop :=
  ShortestCommonSuperstring.WellFormed i ∧ ∀ x ∈ i.2.1, x.length ≤ 8 ∧ x.Nodup

open Classical in
/-- SHORTEST COMMON SUPERSTRING with short repetition-free strings as a decision problem over
bitstrings. -/
noncomputable def shortestCommonSuperstringShortRepetitionFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestCommonSuperstringInstance) x with
  | some i => decide (WellFormed i ∧ ShortestCommonSuperstringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShortestCommonSuperstringShortRepetitionFree
