/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddTensorFixed

/-! A further actual axis given by original source generators.
Source names and orbit counts require separate proofs. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original seven local factors, retaining all spin phases. -/
def generatedEighthLocalFiber : localFiberSubgroup :=
  xiSpinLocalFiber *
    monsterSourcePermutationFiber 1 *
    monsterSourcePermutationFiber 0 *
    xiSpinLocalFiber *
    monsterSourcePermutationFiber 1 *
    monsterSourcePermutationFiber 0 *
    xiSpinLocalFiber

/-- Both exterior generators are actual triality. -/
def generatedEighthAxisWord : ↥G :=
  extraIntoGenerated * localIntoGenerated (localFiberIntoH generatedEighthLocalFiber) *
    extraIntoGenerated

/-- The literal word applied to an actual signed-short axis. -/
def generatedEighthAxis : GriessSpace :=
  generatedEighthAxisWord.val (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0)

/-- The actual local/triality expression of this prototype. -/
theorem generatedEighthAxis_local_expression :
    generatedEighthAxis =
      sExtra (rhoLocal (localFiberIntoH generatedEighthLocalFiber) generatedOddAxis) := by
  rfl

/-- This prototype belongs to every actual signed-short global orbit. -/
theorem generatedEighthAxis_mem_generatedOrbit (r : GriessShortIndex) (c : ZMod 2) :
    generatedEighthAxis ∈ generatedVectorOrbit (conwayShortAxis r c) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r (Sum.inr (Sum.inr (0, 0))) c 0
  refine ⟨generatedEighthAxisWord * localIntoGenerated h, ?_⟩
  change generatedEighthAxisWord.val (rhoLocal h (conwayShortAxis r c)) = _
  rw [hh]
  rfl

/-- The genuine full-coordinate extraspecial stabilizer, without an assumed order. -/
def generatedEighthAxisQStabilizer : Subgroup Q :=
  (MulAction.stabilizer H generatedEighthAxis).comap inclQ

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
