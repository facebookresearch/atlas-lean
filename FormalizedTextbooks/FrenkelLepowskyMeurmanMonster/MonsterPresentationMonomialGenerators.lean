/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual source permutation generators in H and G, including their exact Parker phases. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationSpinPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationMonomialPolarization
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechOrbitActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinBinaryAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalLocal

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The checked compact phase coefficients, for efficient evaluation of concrete words. -/
def monsterSourcePermutationPhaseData (k : Fin 2) : Fin 12 → Fin 12 → ZMod 2 :=
  fun i j => golayBooleanCast ((monsterSourcePermutationPhaseRows k i).testBit j.val)

/-- The compact coefficients equal the defining source theta expression entry by entry. -/
theorem monsterSourcePermutationPhaseData_eq (k : Fin 2) :
    monsterSourcePermutationPhaseData k = monsterSourcePermutationPhaseMatrix k := by
  funext i j
  exact (monsterSourcePermutationPhase_certificate k i j).symm

/-- The genuine signed diagonal involution retains its explicit coordinate operator. -/
theorem monsterMonomialDiagonalEquiv_toLinearMap (M : Fin 12 → Fin 12 → ZMod 2) :
    (monsterMonomialDiagonalEquiv M).toLinearMap = monsterMonomialDiagonal M := rfl

/-- Its proved coordinate image is the actual Q conjugation automorphism. -/
theorem monsterMonomialDiagonalHolomorph_conjugation
    (M : Fin 12 → Fin 12 → ZMod 2) (q : Q) :
    spinConjugation (monsterMonomialDiagonalHolomorph M) q =
      monsterMonomialDiagonalImage M q := by
  apply spinRepresentation_injective
  rw [spinConjugation_representation]
  have hs : monsterMonomialDiagonalEquiv M * monsterMonomialDiagonalEquiv M = 1 := by
    apply LinearEquiv.ext
    exact monsterMonomialDiagonal_involutive M
  have hi : (monsterMonomialDiagonalEquiv M)⁻¹ = monsterMonomialDiagonalEquiv M :=
    inv_eq_of_mul_eq_one_right hs
  change monsterMonomialDiagonalEquiv M * spinRepresentation q *
    (monsterMonomialDiagonalEquiv M)⁻¹ = spinRepresentation (monsterMonomialDiagonalImage M q)
  rw [hi]
  apply LinearEquiv.toLinearMap_injective
  simp only [LinearEquiv.coe_toLinearMap_mul, monsterMonomialDiagonalEquiv_toLinearMap,
    xiSpinRepresentation_toLinearMap]
  exact monsterMonomialDiagonal_conjugation M q

/-- The genuine relabeling also has the actual coordinate conjugation automorphism. -/
theorem monsterMonomialPermutationHolomorph_conjugation
    (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex) (q : Q) :
    spinConjugation (monsterMonomialPermutationHolomorph P) q =
      monsterMonomialPermutationImage P q := by
  apply spinRepresentation_injective
  rw [spinConjugation_representation]
  exact monsterMonomialPermutation_conjugation P q

/-- The full source lift: the coordinate relabeling follows the exact quadratic sign. -/
noncomputable def monsterSourcePermutationSpin (k : Fin 2) : SpinHolomorph :=
  monsterMonomialPermutationHolomorph (monsterSourcePermutationCode k) *
    monsterMonomialDiagonalHolomorph (monsterSourcePermutationPhaseData k)

/-- The source lift's explicit action on every genuine Q element, including its central sign. -/
def monsterSourcePermutationImage (k : Fin 2) (q : Q) : Q :=
  monsterMonomialPermutationImage (monsterSourcePermutationCode k)
    (monsterMonomialDiagonalImage (monsterSourcePermutationPhaseData k) q)

/-- Conjugation in the actual spin normalizer is the stated full source formula. -/
theorem monsterSourcePermutationSpin_conjugation (k : Fin 2) (q : Q) :
    spinConjugation (monsterSourcePermutationSpin k) q = monsterSourcePermutationImage k q := by
  rw [monsterSourcePermutationSpin, map_mul]
  change spinConjugation (monsterMonomialPermutationHolomorph (monsterSourcePermutationCode k))
    (spinConjugation (monsterMonomialDiagonalHolomorph (monsterSourcePermutationPhaseData k)) q) = _
  rw [monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation]
  rfl

/-- The binary action obtained from the actual checked Q conjugation formula. -/
def monsterSourcePermutationBinaryMatrix (k : Fin 2) :
    Matrix (Fin 24) (Fin 24) (ZMod 2) :=
  fun i j => toAdd (monsterSourcePermutationImage k (xiSpinBinaryBasisLift j)).base i

set_option maxRecDepth 4096 in
/-- Each matrix column is the actual spin action on a genuine hyperbolic basis class. -/
theorem monsterSourcePermutationBinary_column (k : Fin 2) (j : Fin 24) :
    spinBinaryAction (monsterSourcePermutationSpin k) (Pi.single j 1) =
      (monsterSourcePermutationBinaryMatrix k).col j := by
  have h := qBinaryAction_apply (spinConjugation (monsterSourcePermutationSpin k))
    (xiSpinBinaryBasisLift j)
  change spinBinaryAction (monsterSourcePermutationSpin k) (Pi.single j 1) =
    toAdd (spinConjugation (monsterSourcePermutationSpin k) (xiSpinBinaryBasisLift j)).base at h
  rw [monsterSourcePermutationSpin_conjugation] at h
  exact h

set_option maxRecDepth 4096 in
/-- The full binary linear action agrees with the actual coordinate matrix. -/
theorem monsterSourcePermutationBinary_linear (k : Fin 2) :
    (spinBinaryAction (monsterSourcePermutationSpin k)).toLinearMap =
      (monsterSourcePermutationBinaryMatrix k).mulVecLin := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
  intro j
  simpa only [Pi.basisFun_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one] using monsterSourcePermutationBinary_column k j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
-- Compare both actual 24 by 24 binary actions, including the Parker phase shear.
/-- The full source spin lifts have the same binary actions as the genuine Leech permutations. -/
theorem monsterSourcePermutationBinary_certificate : ∀ k : Fin 2,
    monsterSourcePermutationBinaryMatrix k = omegaOrbitBinaryMatrices (Fin.natAdd 3 k) := by
  decide +kernel

/-- Spin and Leech operators agree on the actual common quotient Q/Z(Q)=Λ/2Λ. -/
theorem monsterSourcePermutation_compatibility (k : Fin 2) :
    spinBinaryAction (monsterSourcePermutationSpin k) =
      leechBinaryAction (omegaOrbitPermutationIsometry k) := by
  apply LinearEquiv.toLinearMap_injective
  rw [monsterSourcePermutationBinary_linear, monsterSourcePermutationBinary_certificate k]
  apply LinearMap.ext
  intro v
  have h := omegaOrbitIsometry_binary (Fin.natAdd 3 k) v
  have hi : omegaOrbitIsometry (Fin.natAdd 3 k) = omegaOrbitPermutationIsometry k := by
    fin_cases k <;> rfl
  rw [hi] at h
  exact h.symm

/-- The two exact standard source permutation lifts in the defining fiber product. -/
noncomputable def monsterSourcePermutationFiber (k : Fin 2) : localFiberSubgroup :=
  ⟨(monsterSourcePermutationSpin k, omegaOrbitPermutationIsometry k),
    monsterSourcePermutation_compatibility k⟩

/-- Their actual local images, with the source Parker phase fixed. -/
noncomputable def monsterSourcePermutationLocal (k : Fin 2) : H :=
  QuotientGroup.mk' localDiagonalSubgroup (monsterSourcePermutationFiber k)

/-- Concrete source permutation generators in the named generated group G. -/
noncomputable def monsterSourcePermutationGenerated (k : Fin 2) : ↥G :=
  localIntoGenerated (monsterSourcePermutationLocal k)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
