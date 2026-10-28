/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowDescriptorData

/-! Chronological row addresses enumerate exactly all original4136 source labels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The chronological address of each original signed pair or octad-sign source label. -/
def generatedNinthShortRowAddress : generatedNinthOriginalShortLabel → Fin 4136
  | Sum.inl (s, p) => ⟨s.val * 276 + p.val, by omega⟩
  | Sum.inr (j, e) => ⟨552 + j.val * 64 + e.val, by omega⟩

/-- Decoding the chronological address recovers its full original source label. -/
theorem generatedNinth_short_row_source_address (a : generatedNinthOriginalShortLabel) :
    generatedNinthShortRowSource (generatedNinthShortRowAddress a) = a := by
  rcases a with ⟨s, p⟩ | ⟨j, e⟩
  · simp only [generatedNinthShortRowAddress, generatedNinthShortRowSource]
    split
    · congr 1
      apply Prod.ext
      · apply Fin.ext
        change (s.val * 276 + p.val) / 276 = s.val
        omega
      · apply Fin.ext
        change (s.val * 276 + p.val) % 276 = p.val
        omega
    · exfalso
      omega
  · simp only [generatedNinthShortRowAddress, generatedNinthShortRowSource]
    split
    · exfalso
      omega
    · congr 1
      apply Prod.ext
      · apply Fin.ext
        change (552 + j.val * 64 + e.val - 552) / 64 = j.val
        omega
      · apply Fin.ext
        change (552 + j.val * 64 + e.val - 552) % 64 = e.val
        omega

/-- Encoding a decoded chronological row recovers the exact finite address. -/
theorem generatedNinth_short_row_address_source (k : Fin 4136) :
    generatedNinthShortRowAddress (generatedNinthShortRowSource k) = k := by
  unfold generatedNinthShortRowSource
  split
  · simp only [generatedNinthShortRowAddress]
    apply Fin.ext
    change k.val / 276 * 276 + k.val % 276 = k.val
    omega
  · simp only [generatedNinthShortRowAddress]
    apply Fin.ext
    change 552 + (k.val - 552) / 64 * 64 + (k.val - 552) % 64 = k.val
    omega

/-- The row addresses are equivalent to the complete original source-label catalogue. -/
def generatedNinthShortRowSourceEquiv : Fin 4136 ≃ generatedNinthOriginalShortLabel where
  toFun := generatedNinthShortRowSource
  invFun := generatedNinthShortRowAddress
  left_inv := generatedNinth_short_row_address_source
  right_inv := generatedNinth_short_row_source_address

/-- Every original source label occurs at a chronological row address. -/
theorem generatedNinth_short_row_source_surjective :
    Function.Surjective generatedNinthShortRowSource := generatedNinthShortRowSourceEquiv.surjective

/-- Distinct chronological row addresses denote distinct original source labels. -/
theorem generatedNinth_short_row_source_injective :
    Function.Injective generatedNinthShortRowSource := generatedNinthShortRowSourceEquiv.injective

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
