/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTransitionMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationTrialitySource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinLeechCompatibility

/-! A short actual generated-group candidate beyond the first three local
families. No assertion of a fourth class or source label is made until its
original matrix and stabilizer are verified. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The selected genuine octad is the actual published code label sixteen. -/
noncomputable def generatedFourthOctad : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨(⟨16, by decide⟩ : Fin 4096), by decide +kernel⟩

/-- The finite octad index retains its original code label exactly. -/
theorem generatedFourthOctad_label : golayOctadLabel generatedFourthOctad = 16 := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨(⟨16, by decide⟩ : Fin 4096), by decide +kernel⟩)

/-- The actual selected code word has two coordinates in each of four MOG tetrads. -/
theorem generatedFourthOctad_mask :
    golayEncodedMask (golayOctadLabel generatedFourthOctad).val = 0xcccc00 := by
  rw [generatedFourthOctad_label]
  decide +kernel

/-- The five-factor palindrome uses original triality and verified local generators. -/
noncomputable def generatedFourthAxisWord : ↥G :=
  extraIntoGenerated * xiSpinGenerated⁻¹ * (monsterSourcePermutationGenerated 0)⁻¹ *
    xiSpinGenerated⁻¹ * extraIntoGenerated

/-- The actual candidate is the literal word applied to a genuine signed-short axis. -/
noncomputable def generatedFourthAxis : GriessSpace :=
  generatedFourthAxisWord.val
    (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)

/-- This literal candidate lies in the actual global orbit of every genuine signed-short axis. -/
theorem generatedFourthAxis_mem_generatedOrbit (r : GriessShortIndex) (c : ZMod 2) :
    generatedFourthAxis ∈ generatedVectorOrbit (conwayShortAxis r c) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r
    (Sum.inr (Sum.inl (generatedFourthOctad, 0))) c 0
  refine ⟨generatedFourthAxisWord * localIntoGenerated h, ?_⟩
  change generatedFourthAxisWord.val (rhoLocal h (conwayShortAxis r c)) = _
  rw [hh]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
