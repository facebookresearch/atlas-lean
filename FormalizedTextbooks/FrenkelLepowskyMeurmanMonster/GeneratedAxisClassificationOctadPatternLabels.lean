/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPropagationData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadIntegralSpan
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadSupportCount

/-! Physical catalogue bindings for the 120 finite root patterns. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The original preferred-short label of each checked coordinate root. -/
noncomputable def generatedOctadPatternLabel (p : Fin 120) : GriessShortIndex :=
  if h : p.val < 56 then
    let ij := generatedOctadPatternPair ⟨p.val % 28, Nat.mod_lt _ (by decide)⟩
    Sum.inl (⟨p.val / 28, by omega⟩,
      griessPairIndex ⟨8 + ij.1.val, by omega⟩ ⟨8 + ij.2.val, by omega⟩ (by
        intro he
        have he' := congrArg Fin.val he
        have hl := generatedOctadPatternPair_lt
          ⟨p.val % 28, Nat.mod_lt _ (by decide)⟩
        dsimp [ij] at he'
        omega))
  else Sum.inr (Sum.inl (generatedOctadBasisOctad, ⟨p.val - 56, by omega⟩))

/-- The named preferred-short vector is exactly the inserted local integer root. -/
theorem generatedOctadPatternLabel_integral (p : Fin 120) :
    griessShortIntegral (generatedOctadPatternLabel p) =
      generatedOctadIntegerInsert (generatedOctadPatternVector p) := by
  unfold generatedOctadPatternLabel generatedOctadPatternVector
  split_ifs with h
  · rw [generatedOctadIntegerPair_insert_certificate]
    have hl : (⟨8 + (generatedOctadPatternPair
        ⟨p.val % 28, Nat.mod_lt _ (by decide)⟩).1.val, by omega⟩ : Fin 24) <
        ⟨8 + (generatedOctadPatternPair
          ⟨p.val % 28, Nat.mod_lt _ (by decide)⟩).2.val, by omega⟩ := by
      have hp := generatedOctadPatternPair_lt
        ⟨p.val % 28, Nat.mod_lt _ (by decide)⟩
      change 8 + _ < 8 + _
      omega
    simp only [griessShortIntegral, griessPairIndex_coordinates, hl, ite_true]
  · rw [generatedOctadIntegerSigns_insert_certificate]
    simp only [griessShortIntegral, generatedOctadBasisOctad_mask,
      generatedOctadBasisOctad_sign_mask]

/-- Each preferred-short lattice vector has the exact checked integer coefficients. -/
theorem generatedOctadPatternLabel_lattice (p : Fin 120) :
    griessShortLatticeVector (generatedOctadPatternLabel p) =
      ∑ j, generatedOctadIntegerRootCoordinates (generatedOctadPatternVector p) j •
        griessShortLatticeVector (generatedOctadBasisLabel j) := by
  apply Subtype.ext
  have h := generatedOctadIntegerRoot_insert_sum
    (generatedOctadIntegerRootCoordinates (generatedOctadPatternVector p))
  rw [generatedOctadPatternVector_span, ← generatedOctadPatternLabel_integral] at h
  simpa only [Submodule.coe_sum, Submodule.coe_smul, griessShortLatticeVector] using h

/-- The actual preferred Q lift has the checked eight-bit root coordinates. -/
theorem generatedOctadPatternLabel_base (p : Fin 120) :
    toAdd (griessShortQ (generatedOctadPatternLabel p)).base =
      generatedOctadBasisBinaryMatrix *ᵥ generatedOctadPatternBits p := by
  change leechHyperbolicCoordinates
    (leechReduction (griessShortLatticeVector (generatedOctadPatternLabel p))) = _
  rw [generatedOctadPatternLabel_lattice, map_sum, map_sum]
  have hs : ∀ j : Fin 8,
      leechHyperbolicCoordinates (leechReduction
        (generatedOctadIntegerRootCoordinates (generatedOctadPatternVector p) j •
          griessShortLatticeVector (generatedOctadBasisLabel j))) =
        generatedOctadPatternBits p j • generatedOctadBasisBinaryMatrix.col j := by
    intro j
    rw [map_zsmul, map_zsmul]
    change _ • toAdd (griessShortQ (generatedOctadBasisLabel j)).base = _
    rw [generatedOctadBasis_actual_base]
    exact (Int.cast_smul_eq_zsmul (ZMod 2) _ _).symm
  simp_rw [hs]
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.col_apply]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

/-- Distinct finite patterns give distinct actual preferred-short labels. -/
theorem generatedOctadPatternLabel_injective : Function.Injective generatedOctadPatternLabel := by
  intro p q h
  apply generatedOctadPatternBits_injective
  apply generatedOctadBasis_binary_injective
  change generatedOctadBasisBinaryMatrix *ᵥ generatedOctadPatternBits p =
    generatedOctadBasisBinaryMatrix *ᵥ generatedOctadPatternBits q
  rw [← generatedOctadPatternLabel_base, ← generatedOctadPatternLabel_base, h]

/-- Every finite pattern belongs to the genuine supported short catalogue. -/
theorem generatedOctadPatternLabel_supported (p : Fin 120) :
    generatedOctadShortSupport generatedOctadBasisOctad (generatedOctadPatternLabel p) := by
  have hc : ∀ i : Fin 8, (0xff00 : ℕ).testBit (8 + i.val) = true := by decide +kernel
  unfold generatedOctadPatternLabel
  split_ifs
  · simp only [generatedOctadShortSupport, generatedOctadPairSupport,
      griessPairIndex_coordinates, generatedOctadBasisOctad_mask]
    split_ifs <;> exact ⟨hc _, hc _⟩
  · rfl

/-- The finite patterns give all 120 actual supported short labels. -/
noncomputable def generatedOctadPatternEquiv : Fin 120 ≃
    {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} := by
  let f (p : Fin 120) :=
    (⟨generatedOctadPatternLabel p, generatedOctadPatternLabel_supported p⟩ :
      {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r})
  have hi : Function.Injective f := by
    intro p q h
    exact generatedOctadPatternLabel_injective (congrArg Subtype.val h)
  have hc : Nat.card (Fin 120) = Nat.card
      {r : GriessShortIndex // generatedOctadShortSupport generatedOctadBasisOctad r} := by
    rw [generatedOctad_short_support_card, Nat.card_fin]
  exact Equiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hi, hc⟩)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
