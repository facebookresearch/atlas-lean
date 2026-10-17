/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.Composition
public import CSLibExt.Computability.Complexity.PairEncodingConverter

/-!
# Dense CNF-SAT is in NP

`Cslib.Complexity.DenseSAT.denseSatDec`, the decision problem of the dense CNF-SAT language
`Cslib.Complexity.DenseSAT.SAT`, belongs to formal-math's canonical class
`MetaMathlibExt.ComplexityTheory.NP`. The definition of `NP` is used unchanged: the polynomial
is `X` (an assignment needs no more bits than the formula), the verifier relation is
`fun p => check p.1 p.2`, and its `IsPolyTime` witness is the composite of the pair-encoding
converter (`Converter.computable`) and the verifier machine (`Verifier.verifier`), glued by
`MetaMathlibExt.tm2ComputableInPolyTime_comp`.

This is SAT ∈ NP for the dense clause encoding only. For `Cslib.CookLevin.satDec`, whose formulas
use binary variable indices, see `SatVerifier.Machine.satDec_mem_NP`.
-/

@[expose] public section

namespace Cslib.Complexity.DenseSAT

open MetaMathlibExt ComplexityTheory

open Classical in
/-- Dense CNF-SAT as a decision problem: accept exactly the bit strings in `SAT`. -/
noncomputable def denseSatDec : DecisionProblem := fun w => decide (SAT w)

/-- The certificate check is polynomial-time computable in formal-math's sense. -/
theorem isPolyTime_check : IsPolyTime (fun p : List Bool × List Bool => check p.1 p.2) :=
  tm2ComputableInPolyTime_comp Converter.computable Verifier.verifier

/-- **Dense CNF-SAT is in NP.** -/
theorem denseSatDec_mem_NP : denseSatDec ∈ NP :=
  ⟨Polynomial.X, fun p => check p.1 p.2, isPolyTime_check, fun w => by
    simpa [denseSatDec] using sat_iff_check w⟩

end Cslib.Complexity.DenseSAT
