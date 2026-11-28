/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HaplotypeInferencePureParsimonyDefs

namespace MetaMathlibExt.Complexity.NPComplete.HaplotypeInferencePureParsimony

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HaplotypeInferencePureParsimonyInstance) :
    haplotypeInferencePureParsimonyDec (bitEncode i) = true ↔
      WellFormed i ∧ HaplotypeInferencePureParsimonyFeasible i := by
  simp [haplotypeInferencePureParsimonyDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : haplotypeInferencePureParsimonyDec [true] = false := by
  have h : bitDecode (α := HaplotypeInferencePureParsimonyInstance) [true] = none := rfl
  simp [haplotypeInferencePureParsimonyDec, h]

/-- The genotypes `20`, `00` and `10` on two sites: the haplotypes `00` and `10` explain all
three, so two haplotypes suffice. -/
example : haplotypeInferencePureParsimonyDec
    (bitEncode ((2, [[2, 0], [0, 0], [1, 0]], 2) : HaplotypeInferencePureParsimonyInstance)) =
      true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide,
    {fun _ => false, fun k => decide (k.val = 0)}, by decide, ?_⟩
  unfold Explains
  decide

/-- With a bound of one haplotype the same genotypes are well formed but unexplained: the
heterozygous site of `20` needs two different haplotypes. -/
example : haplotypeInferencePureParsimonyDec
    (bitEncode ((2, [[2, 0], [0, 0], [1, 0]], 1) : HaplotypeInferencePureParsimonyInstance)) =
      false := by
  have h : ¬ HaplotypeInferencePureParsimonyFeasible (2, [[2, 0], [0, 0], [1, 0]], 1) := by
    rintro ⟨H, hcard, hexp⟩
    obtain ⟨h₁, h₁H, h₂, h₂H, hx⟩ := hexp [2, 0] (by simp)
    have heq : h₁ = h₂ := Finset.card_le_one.1 hcard _ h₁H _ h₂H
    exact ((hx 0).2.2 rfl) (heq ▸ rfl)
  simpa [haplotypeInferencePureParsimonyDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.HaplotypeInferencePureParsimony
