/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.EnvyFreePricingUnitDemandDefs

namespace MetaMathlibExt.Complexity.NPComplete.EnvyFreePricingUnitDemand

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : EnvyFreePricingInstance) :
    envyFreePricingDec (bitEncode i) = true ↔ WellFormed i ∧ EnvyFreePricingFeasible i := by
  simp [envyFreePricingDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : envyFreePricingDec [true] = false := by
  have h : bitDecode (α := EnvyFreePricingInstance) [true] = none := rfl
  simp [envyFreePricingDec, h]

/-- One item valued `2` and `3` by two consumers: at price `2` both buy, for revenue `4`. -/
example : envyFreePricingDec (bitEncode ((1, [[2], [3]], 4) : EnvyFreePricingInstance)) =
    true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, fun _ => 2, fun _ => some 0,
    ?_, by decide⟩
  intro c
  refine ⟨?_, fun j' => le_of_eq (congrArg _ (Subsingleton.elim j' 0))⟩
  revert c
  decide

/-- The same consumers with revenue goal `5`: a single price `p` earns `2p ≤ 4` when both buy
and at most `3` when only one does. -/
example : envyFreePricingDec (bitEncode ((1, [[2], [3]], 5) : EnvyFreePricingInstance)) =
    false := by
  cases h : envyFreePricingDec (bitEncode ((1, [[2], [3]], 5) : EnvyFreePricingInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, p, a, hd, hrev⟩ := (accepts_encoding _).1 h
    change 5 ≤ ∑ c : Fin 2, (a c).elim 0 p at hrev
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide,
      Finset.sum_pair (by decide)] at hrev
    have h₀ := hd 0
    have h₁ := hd 1
    have hp : ∀ j : Fin 1, j = 0 := fun j => Subsingleton.elim j 0
    revert h₀ h₁ hrev
    cases a 0 <;> cases a 1 <;>
      simp only [hp, InDemandSet, utility, Option.elim] <;> intros <;> simp_all <;> omega

end MetaMathlibExt.Complexity.NPComplete.EnvyFreePricingUnitDemand
