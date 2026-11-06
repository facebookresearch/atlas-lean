/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCompactQConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightGeneratorCandidates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

/-! Compact normalizers paired with the spatial component of the literal original source.
The complete source Q comparison is an explicit prerequisite, not a fixation assumption. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Twelve uncorrected source generators, canonical transport, and canonical incoming word. -/
def generatedRootEightCompactSourceFiber (i : Fin 14) : localFiberSubgroup :=
  if h : i.val < 12 then generatedRootEightGeneratorPrimitiveFiber ⟨i.val, h⟩
  else if i.val = 12 then generatedRootEightCanonicalFiber
  else generatedRootEightCanonicalFiber * generatedTenthQWordFiber 8

/-- The source family retains each literal uncorrected generator. -/
theorem generatedRootEight_compact_source_generator (j : Fin 12) :
    generatedRootEightCompactSourceFiber (Fin.castAdd 2 j) =
      generatedRootEightGeneratorPrimitiveFiber j := by
  simp only [generatedRootEightCompactSourceFiber, Fin.val_castAdd, j.isLt, dite_true]

/-- Source index twelve is the entire original canonical transport. -/
theorem generatedRootEight_compact_source_canonical :
    generatedRootEightCompactSourceFiber 12 = generatedRootEightCanonicalFiber := by
  simp only [generatedRootEightCompactSourceFiber]
  norm_num

/-- Source index thirteen is canonical transport after the incoming seven-stage local word. -/
theorem generatedRootEight_compact_source_incoming :
    generatedRootEightCompactSourceFiber 13 =
      generatedRootEightCanonicalFiber * generatedTenthQWordFiber 8 := by
  simp only [generatedRootEightCompactSourceFiber]
  norm_num

/-- Complete extraspecial conjugation equality, including every central phase. -/
def generatedRootEightCompactSourceCondition (i : Fin 14) : Prop :=
  spinConjugation (generatedRootEightCompactSpin i) =
    spinConjugation (generatedRootEightCompactSourceFiber i).val.1

/-- Twenty-four full coordinate images suffice for the complete source comparison. -/
theorem generatedRootEight_compact_source_condition_of_basis (i : Fin 14)
    (h : ∀ j : Fin 24, spinConjugation (generatedRootEightCompactSpin i)
      (qCoordinateGenerator j) =
        spinConjugation (generatedRootEightCompactSourceFiber i).val.1
          (qCoordinateGenerator j)) : generatedRootEightCompactSourceCondition i := by
  apply MulEquiv.ext
  intro q
  let images := fun j => spinConjugation (generatedRootEightCompactSourceFiber i).val.1
    (qCoordinateGenerator j)
  exact (monsterNortonCoordinateEvaluation_eq (generatedRootEightCompactSpin i) images h q).trans
    (monsterNortonCoordinateEvaluation_eq (generatedRootEightCompactSourceFiber i).val.1
      images (fun _ => rfl) q).symm

/-- Equal complete Q actions make the compact spin compatible with the actual source isometry. -/
theorem generatedRootEight_compact_source_compatibility (i : Fin 14)
    (h : generatedRootEightCompactSourceCondition i) :
    spinBinaryAction (generatedRootEightCompactSpin i) =
      leechBinaryAction (generatedRootEightCompactSourceFiber i).val.2 := by
  have hb : spinBinaryAction (generatedRootEightCompactSpin i) =
      spinBinaryAction (generatedRootEightCompactSourceFiber i).val.1 := by
    exact congrArg qBinaryAction h
  exact hb.trans (generatedRootEightCompactSourceFiber i).property

/-- A genuine local fiber with compact spin and unchanged original source spatial component. -/
def generatedRootEightCompactSourceCertifiedFiber (i : Fin 14)
    (h : generatedRootEightCompactSourceCondition i) : localFiberSubgroup :=
  ⟨(generatedRootEightCompactSpin i, (generatedRootEightCompactSourceFiber i).val.2),
    generatedRootEight_compact_source_compatibility i h⟩

/-- The compatible compact model is an actual element of the original local group. -/
def generatedRootEightCompactSourceLocal (i : Fin 14)
    (h : generatedRootEightCompactSourceCondition i) : H :=
  localFiberIntoH (generatedRootEightCompactSourceCertifiedFiber i h)

/-- Its Conway projection is exactly the literal original source projection. -/
theorem generatedRootEight_compact_source_projection (i : Fin 14)
    (h : generatedRootEightCompactSourceCondition i) :
    projH (generatedRootEightCompactSourceLocal i h) =
      projH (localFiberIntoH (generatedRootEightCompactSourceFiber i)) := rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
