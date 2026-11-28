/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPARATIVE DIVISIBILITY with distinct elements: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN4] COMPARATIVE DIVISIBILITY,
p. 249, comment: "Remains NP-complete even if all `aᵢ` are different and all `bⱼ` are
different", credited there to Garey and Johnson (unpublished; no published proof was
available). The general problem is due to D. A. Plaisted, "Some polynomial and integer
divisibility problems are NP-hard", SIAM Journal on Computing 7 (1978), 458-464,
doi:10.1137/0207036.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ComparativeDivisibilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibilityDistinct

open MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibility

/-- Well-formedness of an instance: every entry is positive (`ComparativeDivisibility`), the
`aᵢ` are pairwise different, and the `bⱼ` are pairwise different. -/
def WellFormed (i : ComparativeDivisibilityInstance) : Prop :=
  ComparativeDivisibility.WellFormed i ∧ i.1.Nodup ∧ i.2.Nodup

open Classical in
/-- COMPARATIVE DIVISIBILITY with distinct elements as a decision problem over bitstrings. -/
noncomputable def comparativeDivisibilityDistinctDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ComparativeDivisibilityInstance) x with
  | some i => decide (WellFormed i ∧ ComparativeDivisibilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ComparativeDivisibilityDistinct
