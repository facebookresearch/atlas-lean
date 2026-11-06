/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingCompactQBasis
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQFastBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightRepresentative

/-! The compact incoming root-eight model retains the entire original extraspecial action. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

set_option maxHeartbeats 4000000 in
-- Compare all twenty-four bits and the central coefficient of every recorded image.
/-- Recorded compact basis images equal the original checked word-eight full-Q cache. -/
theorem generatedRootEight_incoming_compact_basis_source : ∀ j : Fin 24,
    generatedRootEightIncomingCompactBasisImage 0 j = generatedAxisGlobalFifthQCache 8 j := by
  decide +kernel

/-- The compact model agrees with the original incoming word on every actual Q element. -/
theorem generatedRootEight_incoming_compact_source_Q (q : Q) :
    spinConjugation (generatedRootEightIncomingCompactSpin 0) q =
      spinConjugation (generatedTenthQWordFiber 8).val.1 q := by
  have hc := monsterNortonCoordinateEvaluation_eq (generatedRootEightIncomingCompactSpin 0)
    (generatedAxisGlobalFifthQCache 8)
    (fun j => (generatedRootEight_incoming_compact_conjugation 0 _).trans
      ((generatedRootEight_incoming_compact_q_basis_00 j).trans
        (generatedRootEight_incoming_compact_basis_source j))) q
  rw [generatedTenth_Q_word_image,
    generatedTenth_Q_word_fast 8 generatedAxisGlobalFifthQCache08_actual]
  exact hc

/-- Complete extraspecial conjugation equality retains every original central phase. -/
theorem generatedRootEight_incoming_compact_source_conjugation :
    spinConjugation (generatedRootEightIncomingCompactSpin 0) =
      spinConjugation (generatedTenthQWordFiber 8).val.1 :=
  MulEquiv.ext generatedRootEight_incoming_compact_source_Q

/-- The compact spin acts on the binary quotient exactly as the actual original spatial word. -/
theorem generatedRootEight_incoming_compact_compatibility :
    spinBinaryAction (generatedRootEightIncomingCompactSpin 0) =
      leechBinaryAction (generatedTenthQWordFiber 8).val.2 := by
  have hb : spinBinaryAction (generatedRootEightIncomingCompactSpin 0) =
      spinBinaryAction (generatedTenthQWordFiber 8).val.1 :=
    congrArg qBinaryAction generatedRootEight_incoming_compact_source_conjugation
  exact hb.trans (generatedTenthQWordFiber 8).property

/-- A genuine incoming fiber with compact spin and the unchanged literal word-eight isometry. -/
def generatedRootEightIncomingCertifiedFiber : localFiberSubgroup :=
  ⟨(generatedRootEightIncomingCompactSpin 0, (generatedTenthQWordFiber 8).val.2),
    generatedRootEight_incoming_compact_compatibility⟩

/-- The complete genuine local element for the certified compact incoming word. -/
def generatedRootEightIncomingCertifiedLocal : H :=
  localFiberIntoH generatedRootEightIncomingCertifiedFiber

/-- The original full spatial projection is retained in the actual compact local element. -/
theorem generatedRootEight_incoming_certified_projection :
    projH generatedRootEightIncomingCertifiedLocal = projH generatedFifthRootEightLocal := by
  rw [show generatedFifthRootEightLocal = localFiberIntoH (generatedTenthQWordFiber 8) from
    (generatedTenth_Q_word_fiber_local 8).symm]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
