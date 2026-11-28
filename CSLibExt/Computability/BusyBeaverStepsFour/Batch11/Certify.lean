/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.BusyBeaverStepsFour.Checker
import all CSLibExt.Computability.BusyBeaverStepsFour.Checker
meta import all CSLibExt.Computability.BusyBeaverStepsFour.Checker
import Mathlib.Tactic.Eval

/-!
# Certificate tactic for the split four-state batch

The largest row is split by initial write and by the lower and upper halves of the next index.
The smaller modules can be checked independently, retaining one kernel proof per subtree.
-/

namespace Cslib.BusyBeaverWanted.busyBeaverSteps_four_wanted

open Lean in
macro "checkFourStateBatch11Part" w:num offset:num k:term : tactic => do
  let proofs ← (List.range 8).toArray.mapM fun index => do
    let middle := Syntax.mkNumLit (toString (offset.getNat + index))
    let subproofs ← (List.range 16).toArray.mapM fun subindex => do
      let last := Syntax.mkNumLit (toString subindex)
      `(tactic| · exact ⟨eval% batchHints $w 11 $middle $last, by decide +kernel⟩)
    `(tactic| · intro l
                fin_cases l
                $subproofs*)
  `(tactic| (
    unfold BatchCertified isBatchCertified
    fin_cases $k:term
    $proofs*
  ))

end Cslib.BusyBeaverWanted.busyBeaverSteps_four_wanted
