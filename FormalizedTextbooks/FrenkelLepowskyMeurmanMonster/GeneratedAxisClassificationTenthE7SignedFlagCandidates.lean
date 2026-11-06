/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7StandardOutsideAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderMonomial

/-! Complete genuine signed flag candidates with their actual Golay correction fibers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original signs of the standard norm-twelve vector in the complete outside order. -/
def generatedTenthE7StandardOutsideSigns : Fin 6 → ZMod 2 := ![1, 0, 1, 0, 0, 0]

/-- The complete outside phase difference for the actual inverse permutation action. -/
def generatedTenthE7SignedFlagPhase (p : generatedTenthE7StandardFlagPermutationGroup) :
    Fin 6 → ZMod 2 := fun i =>
  generatedTenthE7StandardOutsideSigns i + generatedTenthE7StandardOutsideSigns
    ((generatedTenthE7StandardOutsidePermutation p).symm i)

/-- Every actual whole flag permutation has an even complete outside phase. -/
theorem generatedTenth_e7_signed_flag_phase_even
    (p : generatedTenthE7StandardFlagPermutationGroup) :
    ∑ i, generatedTenthE7SignedFlagPhase p i = 0 :=
  generatedTenth_e7_permutation_phase_even
    (generatedTenthE7StandardOutsidePermutation p).symm generatedTenthE7StandardOutsideSigns

/-- All actual Golay corrections for one entire original permutation flag. -/
abbrev generatedTenthE7SignedFlagFiber (p : generatedTenthE7StandardFlagPermutationGroup) :=
  {c : golayCode // generatedTenthE7StandardTwistedSignCondition
    (generatedTenthE7SignedFlagPhase p) c}

/-- Each actual entire flag permutation has exactly128 original code corrections. -/
theorem generatedTenth_e7_signed_flag_fiber_card
    (p : generatedTenthE7StandardFlagPermutationGroup) :
    Nat.card (generatedTenthE7SignedFlagFiber p) = 128 :=
  generatedTenth_e7_standard_twisted_sign_fiber_card _
    (generatedTenth_e7_signed_flag_phase_even p)

/-- The entire actual720 permutation flags with every actual128 code correction. -/
abbrev generatedTenthE7SignedFlagCandidates :=
  Σ p : generatedTenthE7StandardFlagPermutationGroup, generatedTenthE7SignedFlagFiber p

/-- The complete original candidate enumeration has exactly92160 members. -/
theorem generatedTenth_e7_signed_flag_candidates_card :
    Nat.card generatedTenthE7SignedFlagCandidates = 92160 := by
  let _ := Fintype.ofFinite generatedTenthE7StandardFlagPermutationGroup
  rw [Nat.card_sigma]
  simp_rw [generatedTenth_e7_signed_flag_fiber_card]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, generatedTenth_e7_standard_flag_permutation_card]

/-- Every candidate is a genuine original signed Golay Leech isometry. -/
def generatedTenthE7SignedFlagSpatial (v : generatedTenthE7SignedFlagCandidates) :
    leechIsomSubgroup :=
  golayMonomialPair (v.2.val, v.1.val.val)

/-- No two complete candidates give the same actual Leech isometry. -/
theorem generatedTenth_e7_signed_flag_spatial_injective :
    Function.Injective generatedTenthE7SignedFlagSpatial := by
  rintro ⟨p, c⟩ ⟨q, d⟩ h
  have hm := golayMonomialPair_injective h
  have hp : p = q := Subtype.ext (Subtype.ext (congrArg Prod.snd hm))
  cases hp
  have hc : c = d := Subtype.ext (congrArg Prod.fst hm)
  cases hc
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
