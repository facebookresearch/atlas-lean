/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM BISECTION on unit disk graphs: definitions

Source:
J. Díaz and G. B. Mertzios, "Minimum bisection is NP-hard on unit disk graphs", Information and
Computation 256 (2017), 83-92, doi:10.1016/j.ic.2017.04.010 (conference version MFCS 2014,
LNCS 8635, 251-262, doi:10.1007/978-3-662-44465-8_22; preprint arXiv:1404.0117).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxCutUnitDiskGraphsDefs
public import CSLibExt.Complexity.NPComplete.MinBisectionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinBisectionUnitDiskGraphs

open MetaMathlibExt.Complexity.NPComplete.MaxCutUnitDiskGraphs
  (MaxCutUnitDiskGraphsInstance toMaxCut)
open MetaMathlibExt.Complexity.NPComplete.MinBisection (MinBisectionFeasible)

open Classical in
/-- MINIMUM BISECTION on unit disk graphs as a decision problem over bitstrings. -/
noncomputable def minBisectionUnitDiskGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutUnitDiskGraphsInstance) x with
  | some i => decide (MaxCutUnitDiskGraphs.WellFormed i ∧ MinBisectionFeasible (toMaxCut i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MinBisectionUnitDiskGraphs
