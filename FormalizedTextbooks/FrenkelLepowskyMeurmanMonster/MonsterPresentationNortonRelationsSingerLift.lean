/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine source Parker lift of the exact p43549632 coordinate permutation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerLattice
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerPolarization
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialGenerators

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual standard spin lift has no diagonal phase, as certified by the theta formula. -/
noncomputable def monsterNortonSingerSpin : SpinHolomorph :=
  monsterMonomialPermutationHolomorph (monsterNortonSingerCode 0)

/-- Its full action on Q, including the genuine central coefficient. -/
def monsterNortonSingerImage (q : Q) : Q :=
  monsterMonomialPermutationImage (monsterNortonSingerCode 0) q

/-- The explicit source image is the actual spin conjugation action. -/
theorem monsterNortonSingerSpin_conjugation (q : Q) :
    spinConjugation monsterNortonSingerSpin q = monsterNortonSingerImage q :=
  monsterMonomialPermutationHolomorph_conjugation _ q

set_option maxRecDepth 4096 in
/-- The physical binary columns are the actual spin images of the hyperbolic basis. -/
theorem monsterNortonSingerBinary_column (j : Fin 24) :
    spinBinaryAction monsterNortonSingerSpin (Pi.single j 1) =
      monsterNortonSingerBinaryMatrix.col j := by
  have h := qBinaryAction_apply (spinConjugation monsterNortonSingerSpin)
    (xiSpinBinaryBasisLift j)
  change spinBinaryAction monsterNortonSingerSpin (Pi.single j 1) =
    toAdd (spinConjugation monsterNortonSingerSpin (xiSpinBinaryBasisLift j)).base at h
  rw [monsterNortonSingerSpin_conjugation] at h
  exact h

set_option maxRecDepth 4096 in
/-- Extending the basis identities identifies the entire actual binary spin action. -/
theorem monsterNortonSingerBinary_linear :
    (spinBinaryAction monsterNortonSingerSpin).toLinearMap =
      monsterNortonSingerBinaryMatrix.mulVecLin := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
  intro j
  simpa only [Pi.basisFun_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one] using monsterNortonSingerBinary_column j

/-- The standard spin lift and genuine Leech permutation have the same quotient action. -/
theorem monsterNortonSinger_compatibility :
    spinBinaryAction monsterNortonSingerSpin =
      leechBinaryAction (monsterNortonSingerPermutationIsometry 0) := by
  apply LinearEquiv.toLinearMap_injective
  rw [monsterNortonSingerBinary_linear]
  apply LinearMap.ext
  intro v
  exact (monsterNortonSingerPermutation_binary v).symm

/-- The actual compatible pair in the defining local fiber product. -/
noncomputable def monsterNortonSingerFiber : localFiberSubgroup :=
  ⟨(monsterNortonSingerSpin, monsterNortonSingerPermutationIsometry 0),
    monsterNortonSinger_compatibility⟩

/-- Its genuine local image with the Parker phase fixed by the defining source equation. -/
noncomputable def monsterNortonSingerLocal : H :=
  QuotientGroup.mk' localDiagonalSubgroup monsterNortonSingerFiber

/-- The source inverse permutation convention in the actual generated group. -/
noncomputable def monsterNortonSingerGenerated : G :=
  localIntoGenerated monsterNortonSingerLocal⁻¹

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
