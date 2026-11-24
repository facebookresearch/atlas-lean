/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import all CSLibExt.Computability.Complexity.OracleNPCoNPSeparation

namespace MetaMathlibExt.Complexity.KeyTheorems.OracleNPCoNPSeparation

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

-- The moved theorem is available with the original statement from the new module alone.
example : ∃ O : List Bool → Bool, NPWithOracle O ≠ {L | Lᶜ ∈ NPWithOracle O} :=
  oracle_np_co_np_separation

-- Complementation gives explicit membership differences in both directions for one oracle.
example :
    ∃ O : List Bool → Bool, ∃ L : DecisionProblem,
      L ∈ NPWithOracle O ∧ L ∉ {L | Lᶜ ∈ NPWithOracle O} ∧
      Lᶜ ∉ NPWithOracle O ∧ Lᶜ ∈ {L | Lᶜ ∈ NPWithOracle O} := by
  classical
  obtain ⟨O, hO⟩ := oracle_np_co_np_separation
  have h : ∃ L : DecisionProblem, L ∈ NPWithOracle O ∧ Lᶜ ∉ NPWithOracle O := by
    by_contra! hclosed
    apply hO
    ext L
    change L ∈ NPWithOracle O ↔ Lᶜ ∈ NPWithOracle O
    exact ⟨hclosed L, fun h => by simpa only [compl_compl] using hclosed Lᶜ h⟩
  obtain ⟨L, hL, hcompl⟩ := h
  refine ⟨O, L, hL, hcompl, hcompl, ?_⟩
  change Lᶜᶜ ∈ NPWithOracle O
  simpa only [compl_compl] using hL

-- The result uses the last answer even when preceding queries received different answers.
example : finalAnswer ([], [([], true), ([true], false)]) = false := by decide

-- Repeated calls still count as one distinct queried word.
example :
    evalOracle 1 Prod.fst finalAnswer (· == [true]) [true] 3 [] = true ∧
    querySet 1 Prod.fst (· == [true]) [true] 3 [] = {[true]} := by decide

-- An adaptive query beyond the cap is excluded from the trace.
example :
    querySet 1 (fun (_, hist) => if hist.isEmpty then [false] else [true, true])
      (fun _ => true) [] 3 [] = {[false]} := by decide

end MetaMathlibExt.Complexity.KeyTheorems.OracleNPCoNPSeparation
