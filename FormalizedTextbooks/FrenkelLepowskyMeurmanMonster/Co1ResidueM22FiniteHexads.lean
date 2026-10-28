/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1ResidueM22FiniteData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2OctadCoordinates

/-! Binding the 77 literal auxiliary hexads to the original Golay octad catalogue. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every cached code is an actual weight-eight Golay word
containing both distinguished positions. -/
theorem co1ResidueM22FiniteHexadCodes_valid : ∀ i : Fin 77,
    golayMaskWeight (golayEncodedMask (co1ResidueM22FiniteHexadCodes i).val) = 8 ∧
      (golayEncodedMask (co1ResidueM22FiniteHexadCodes i).val).testBit 0 = true ∧
      (golayEncodedMask (co1ResidueM22FiniteHexadCodes i).val).testBit 1 = true := by
  decide +kernel

/-- The cached code addresses are distinct. -/
theorem co1ResidueM22FiniteHexadCodes_injective :
    Function.Injective co1ResidueM22FiniteHexadCodes := by
  decide +kernel

/-- A literal hexad address denotes its genuine rooted Golay codeword. -/
def co1ResidueM22FiniteHexadCode (i : Fin 77) : leechRootedA2OctadCode :=
  ⟨co1ResidueM22FiniteHexadCodes i, co1ResidueM22FiniteHexadCodes_valid i⟩

/-- The literal 77 addresses enumerate all genuine rooted octad words. -/
def co1ResidueM22FiniteHexadCodeEquiv : Fin 77 ≃ leechRootedA2OctadCode :=
  Equiv.ofBijective co1ResidueM22FiniteHexadCode
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro i j h
      exact co1ResidueM22FiniteHexadCodes_injective (congrArg Subtype.val h), by
      rw [Fintype.card_fin, leechRootedA2OctadCode_card]⟩)

/-- The original octad index associated to the literal hexad address. -/
def co1ResidueM22FiniteOctad (i : Fin 77) : leechRootedA2OctadIndex :=
  leechRootedA2OctadIndexEquiv.symm (co1ResidueM22FiniteHexadCode i)

/-- The cached word equals the word at its original sorted octad index. -/
theorem co1ResidueM22FiniteOctad_label (i : Fin 77) :
    golayOctadLabel (co1ResidueM22FiniteOctad i).val = co1ResidueM22FiniteHexadCodes i := by
  exact congrArg Subtype.val
    (leechRootedA2OctadIndexEquiv.apply_symm_apply (co1ResidueM22FiniteHexadCode i))

/-- Exact enumeration of the original sorted octad indices containing the two positions. -/
def co1ResidueM22FiniteOctadEquiv : Fin 77 ≃ leechRootedA2OctadIndex :=
  co1ResidueM22FiniteHexadCodeEquiv.trans leechRootedA2OctadIndexEquiv.symm

/-- Removing distinguished coordinates from each genuine octad
gives the cached shifted hexad mask. -/
theorem co1ResidueM22FiniteHexadMasks_correct : ∀ i : Fin 77,
    golayEncodedMask (co1ResidueM22FiniteHexadCodes i).val >>> 2 =
      co1ResidueM22FiniteHexadMasks i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
