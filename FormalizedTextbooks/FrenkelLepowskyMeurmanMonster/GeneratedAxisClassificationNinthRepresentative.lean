/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthRepresentative

/-! A third original-triality transition from the actual fifth prototype.
The source catalogue label and stabilizer order require separate comparisons.
Seysen, arXiv:2203.04223, Figure 2, guides the choice of this transition. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Nine literal local factors retain their original spin phases. -/
def generatedNinthLocalFiber : localFiberSubgroup :=
  xiSpinLocalFiber *
    xiSpinLocalFiber *
    monsterSourcePermutationFiber 1 *
    monsterSourcePermutationFiber 0 *
    xiSpinLocalFiber *
    monsterSourcePermutationFiber 1 *
    monsterSourcePermutationFiber 0 *
    xiSpinLocalFiber *
    monsterSourcePermutationFiber 1

/-- The actual word includes one further original triality after the fifth word. -/
def generatedNinthAxisWord : ↥G :=
  extraIntoGenerated * localIntoGenerated (localFiberIntoH generatedNinthLocalFiber) *
    generatedFifthAxisWord

/-- The literal word acts on the original signed octad-short axis. -/
def generatedNinthAxis : GriessSpace :=
  generatedNinthAxisWord.val
    (conwayShortAxis (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0)

/-- The candidate is exactly the original triality applied to its local fifth image. -/
theorem generatedNinthAxis_local_expression :
    generatedNinthAxis = sExtra (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis) := by
  rfl

/-- The prototype belongs to the actual global orbit of every signed-short axis. -/
theorem generatedNinthAxis_mem_generatedOrbit (r : GriessShortIndex) (c : ZMod 2) :
    generatedNinthAxis ∈ generatedVectorOrbit (conwayShortAxis r c) := by
  obtain ⟨h, hh⟩ := generatedAxis_local_signed_transitive r
    (Sum.inr (Sum.inl (generatedFourthOctad, 0))) c 0
  refine ⟨generatedNinthAxisWord * localIntoGenerated h, ?_⟩
  change generatedNinthAxisWord.val (rhoLocal h (conwayShortAxis r c)) = _
  rw [hh]
  rfl

/-- The actual spatial word uses the same nine original factors. -/
theorem generatedNinth_local_spatial :
    generatedNinthLocalFiber.val.2 =
      co1XiIsometry *
        co1XiIsometry *
        omegaOrbitPermutationIsometry 1 *
        omegaOrbitPermutationIsometry 0 *
        co1XiIsometry *
        omegaOrbitPermutationIsometry 1 *
        omegaOrbitPermutationIsometry 0 *
        co1XiIsometry *
        omegaOrbitPermutationIsometry 1 := by
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
