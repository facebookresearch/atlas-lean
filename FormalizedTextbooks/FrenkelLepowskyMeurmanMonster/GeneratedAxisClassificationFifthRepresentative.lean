/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRepresentative

/-! A literal original-triality transition from the counted octad-image orbit.
The coefficient and stabilizer calculations are separate obligations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual coordinate octad 0 through 3 and 16 through 19, with code label 2052. -/
def generatedFifthFlagOctad : Fin 759 :=
  (golayOctads.orderIsoOfFin golayOctads_card).symm
    ⟨(⟨2052, by decide⟩ : Fin 4096), by decide +kernel⟩

/-- The chosen actual octad retains its genuine encoder label. -/
theorem generatedFifthFlagOctad_label : golayOctadLabel generatedFifthFlagOctad = 2052 := by
  exact congrArg Subtype.val ((golayOctads.orderIsoOfFin golayOctads_card).apply_symm_apply
    ⟨(⟨2052, by decide⟩ : Fin 4096), by decide +kernel⟩)

/-- The genuine coordinate octad is exactly the stated physical support. -/
theorem generatedFifthFlagOctad_mask :
    golayEncodedMask (golayOctadLabel generatedFifthFlagOctad).val = 0x0f000f := by
  rw [generatedFifthFlagOctad_label]
  decide +kernel

/-- The middle local word uses both actual source permutation lifts, including their phases. -/
def generatedFifthLocalFiber : localFiberSubgroup :=
  xiSpinLocalFiber⁻¹ * (monsterSourcePermutationFiber 0)⁻¹ *
    (monsterSourcePermutationFiber 1)⁻¹ * xiSpinLocalFiber⁻¹

/-- The actual six-factor word includes two original triality elements. -/
def generatedFifthAxisWord : ↥G :=
  extraIntoGenerated * xiSpinGenerated⁻¹ * (monsterSourcePermutationGenerated 0)⁻¹ *
    (monsterSourcePermutationGenerated 1)⁻¹ * xiSpinGenerated⁻¹ * extraIntoGenerated

/-- The literal candidate is the actual word applied to a genuine signed-short axis. -/
def generatedFifthAxis : GriessSpace :=
  generatedFifthAxisWord.val
    (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)

set_option maxRecDepth 10000 in
/-- The literal candidate has the exact original triality/local/triality expression. -/
theorem generatedFifthAxis_local_expression :
    generatedFifthAxis = sExtra (rhoLocal (localFiberIntoH generatedFifthLocalFiber)
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))) := by
  simp only [generatedFifthAxis, generatedFifthAxisWord, xiSpinGenerated,
    monsterSourcePermutationGenerated, generatedFifthLocalFiber, map_mul, map_inv]
  rfl

set_option maxRecDepth 10000 in
/-- This literal candidate belongs to the genuine global orbit of every actual signed-short axis. -/
theorem generatedFifthAxis_mem_generatedOrbit (r : GriessShortIndex) (c : ZMod 2) :
    generatedFifthAxis ∈ generatedVectorOrbit (conwayShortAxis r c) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r
    (Sum.inr (Sum.inl (generatedFourthOctad, 0))) c 0
  refine ⟨generatedFifthAxisWord * localIntoGenerated h, ?_⟩
  change generatedFifthAxisWord.val (rhoLocal h (conwayShortAxis r c)) = _
  rw [hh]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
