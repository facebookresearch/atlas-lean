/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismIncidence

/-! Actual dodecad labels and their outside-coordinate counts, from the published encoder. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The labels whose original Golay codeword has twelve nonzero coordinates. -/
def golayDodecads : Finset (Fin 4096) :=
  Finset.univ.filter (fun d => golayMaskWeight (golayEncodedMask d.val) = 12)

/-- Actual dodecads with a specified physical coordinate outside their support. -/
def golayDodecadsOutside (i : Fin 24) : Finset (Fin 4096) :=
  golayDodecads.filter (fun d => !(golayEncodedMask d.val).testBit i.val)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check the twelve-bit encoder and 24-coordinate weight on all 4096 labels.
/-- Counting all 4096 actual encoder outputs gives 2576 dodecads. -/
theorem golayDodecads_card : golayDodecads.card = 2576 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Check all 4096 original labels, including the outside-coordinate condition.
/-- Exactly 1288 actual dodecads have coordinate zero outside their support. -/
theorem golayDodecadsOutside_zero_card : (golayDodecadsOutside 0).card = 1288 := by
  decide +kernel

/-- Dodecad membership is the actual codeword's weight condition. -/
theorem golayDodecads_mem_iff (d : Fin 4096) :
    d ∈ golayDodecads ↔ (∑ i, ((golayCodeLabelEquiv d).val i).val) = 12 := by
  simp only [golayDodecads, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [golayLabel_weight, golayCodeLabelEquiv_val]

/-- Automorphisms preserve the genuine dodecad set. -/
theorem golayLabelPermutation_dodecad (p : golayAutomorphismSubgroup) (d : Fin 4096) :
    golayLabelPermutation p d ∈ golayDodecads ↔ d ∈ golayDodecads := by
  simp only [golayDodecads_mem_iff, golayCodeLabelEquiv_val, golayLabelPermutation_word]
  change (∑ i, (golayEncoder (golayLabelCoefficients d) (p.val.symm i)).val) = 12 ↔ _
  exact (congrArg (fun w : ℕ => w = 12)
    (Equiv.sum_comp p.val.symm
      (fun i => (golayEncoder (golayLabelCoefficients d) i).val))).to_iff

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
