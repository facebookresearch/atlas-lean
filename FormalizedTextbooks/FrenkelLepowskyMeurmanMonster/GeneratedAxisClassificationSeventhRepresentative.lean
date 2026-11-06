/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthRepresentative
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQFixedCriteria

/-! A short genuine generated-group prototype for the next local-axis family.
No external class identification, stabilizer count or orbit coverage is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original local word in application order Xi, P0, P1, P0, Xi, P1, Xi. -/
def generatedSeventhLocalFiber : localFiberSubgroup :=
  xiSpinLocalFiber * monsterSourcePermutationFiber 1 * xiSpinLocalFiber *
    monsterSourcePermutationFiber 0 * monsterSourcePermutationFiber 1 *
    monsterSourcePermutationFiber 0 * xiSpinLocalFiber

/-- The two original triality factors surround the actual seven-factor local word. -/
def generatedSeventhAxisWord : G :=
  extraIntoGenerated * localIntoGenerated (localFiberIntoH generatedSeventhLocalFiber) *
    extraIntoGenerated

/-- The genuine prototype is an actual generated-group image of the preferred odd short axis. -/
def generatedSeventhAxis : GriessSpace :=
  generatedSeventhAxisWord.val (conwayShortAxis (Sum.inr (Sum.inr (0, 0))) 0)

/-- The exact triality/local/odd-axis expression retains the full original operators. -/
theorem generatedSeventhAxis_local_expression :
    generatedSeventhAxis =
      sExtra (rhoLocal (localFiberIntoH generatedSeventhLocalFiber) generatedOddAxis) := by
  rfl

/-- The prototype belongs to the genuine global orbit of every actual signed-short axis. -/
theorem generatedSeventhAxis_mem_generatedOrbit (r : GriessShortIndex) (c : ZMod 2) :
    generatedSeventhAxis ∈ generatedVectorOrbit (conwayShortAxis r c) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r (Sum.inr (Sum.inr (0, 0))) c 0
  refine ⟨generatedSeventhAxisWord * localIntoGenerated h, ?_⟩
  change generatedSeventhAxisWord.val (rhoLocal h (conwayShortAxis r c)) = _
  rw [hh]
  rfl

/-- The genuine full-coordinate extraspecial stabilizer of this actual prototype. -/
def generatedSeventhAxisQStabilizer : Subgroup Q :=
  (MulAction.stabilizer H generatedSeventhAxis).comap inclQ

/-- Membership is fixation of the entire original Griess vector. -/
theorem generatedSeventhAxisQStabilizer_mem (q : Q) :
    q ∈ generatedSeventhAxisQStabilizer ↔
      rhoLocal (inclQ q) generatedSeventhAxis = generatedSeventhAxis := Iff.rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
