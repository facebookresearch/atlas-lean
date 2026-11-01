/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddTensorFixed

/-! An original generated-group word for a further local-axis prototype.
The source class name, coordinates and stabilizer are separate proof obligations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original local word, in application order P0, Xi, P0, P1, P0, Xi, P1, Xi. -/
def generatedSixthLocalFiber : localFiberSubgroup :=
  xiSpinLocalFiber * monsterSourcePermutationFiber 1 * xiSpinLocalFiber *
    monsterSourcePermutationFiber 0 * monsterSourcePermutationFiber 1 *
    monsterSourcePermutationFiber 0 * xiSpinLocalFiber * monsterSourcePermutationFiber 0

/-- Both exterior factors are the original triality generator. -/
def generatedSixthAxisWord : ↥G :=
  extraIntoGenerated * localIntoGenerated (localFiberIntoH generatedSixthLocalFiber) *
    extraIntoGenerated

/-- The prototype is a genuine generated-group image of the preferred odd short axis. -/
def generatedSixthAxis : GriessSpace :=
  generatedSixthAxisWord.val (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0)

/-- The prototype has its literal triality/local/third-axis expression. -/
theorem generatedSixthAxis_local_expression :
    generatedSixthAxis =
      sExtra (rhoLocal (localFiberIntoH generatedSixthLocalFiber) generatedOddAxis) := by
  rfl

/-- This literal prototype belongs to the global orbit of every actual signed-short axis. -/
theorem generatedSixthAxis_mem_generatedOrbit (r : GriessShortIndex) (c : ZMod 2) :
    generatedSixthAxis ∈ generatedVectorOrbit (conwayShortAxis r c) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r (Sum.inr (Sum.inr (0, 0))) c 0
  refine ⟨generatedSixthAxisWord * localIntoGenerated h, ?_⟩
  change generatedSixthAxisWord.val (rhoLocal h (conwayShortAxis r c)) = _
  rw [hh]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
