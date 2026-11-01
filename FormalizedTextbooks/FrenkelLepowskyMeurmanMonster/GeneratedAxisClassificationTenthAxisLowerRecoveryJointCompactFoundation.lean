/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactFoundation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactBinaryCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

/-! Genuine compact constructors and exact full-source certificate obligations for the literal
  joint9*1 lift. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Both complete original compact coordinate maps have their exact two-sided inverses. -/
theorem generatedTenth_axis_lower_recovery_joint_compact_matrix_inverse : ∀ g : Fin 1,
    (generatedTwelfthSpinCompactMatrix
        (generatedTenthAxisLowerRecoveryJointCompactLeftInverseColumns g) *
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoveryJointCompactLeftColumns g) =
        1 ∧
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoveryJointCompactLeftColumns g) *
        generatedTwelfthSpinCompactMatrix
          (generatedTenthAxisLowerRecoveryJointCompactLeftInverseColumns g) = 1) ∧
    (generatedTwelfthSpinCompactMatrix
        (generatedTenthAxisLowerRecoveryJointCompactRightInverseColumns g) *
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoveryJointCompactRightColumns g)
        = 1 ∧
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoveryJointCompactRightColumns g)
        *
        generatedTwelfthSpinCompactMatrix
          (generatedTenthAxisLowerRecoveryJointCompactRightInverseColumns g) = 1) := by
  decide +kernel

/-- The actual left original binary coordinate equivalence. -/
def generatedTenthAxisLowerRecoveryJointCompactLeft (g : Fin 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedTwelfthSpinCompactEquiv (generatedTenthAxisLowerRecoveryJointCompactLeftColumns g)
    (generatedTenthAxisLowerRecoveryJointCompactLeftInverseColumns g)
    (generatedTenth_axis_lower_recovery_joint_compact_matrix_inverse g).1.1
    (generatedTenth_axis_lower_recovery_joint_compact_matrix_inverse g).1.2

/-- The actual right original binary coordinate equivalence. -/
def generatedTenthAxisLowerRecoveryJointCompactRight (g : Fin 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedTwelfthSpinCompactEquiv (generatedTenthAxisLowerRecoveryJointCompactRightColumns g)
    (generatedTenthAxisLowerRecoveryJointCompactRightInverseColumns g)
    (generatedTenth_axis_lower_recovery_joint_compact_matrix_inverse g).2.1
    (generatedTenth_axis_lower_recovery_joint_compact_matrix_inverse g).2.2

/-- The full actual original Pauli factor, retaining its central phase. -/
def generatedTenthAxisLowerRecoveryJointCompactPauli (g : Fin 1) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients (generatedTenthAxisLowerRecoveryJointCompactPauliLabels g).1)
    (golayLabelCoefficients (generatedTenthAxisLowerRecoveryJointCompactPauliLabels g).2.1)),
    ofAdd (generatedTenthAxisLowerRecoveryJointCompactPauliLabels g).2.2⟩

/-- All prescribed original Fourier factors in their actual coordinate order. -/
def generatedTenthAxisLowerRecoveryJointCompactHadamardWord (g : Fin 1) : List (Fin 12) :=
  (List.finRange 12).filter fun k =>
    k.val < (generatedTenthAxisLowerRecoveryJointCompactHadamardRank g).val

/-- The joint proposed spin lift is an actual product of genuine original orthogonal spin
  normalizers. -/
def generatedTenthAxisLowerRecoveryJointCompactSpin (g : Fin 1) : SpinHolomorph :=
  spinHolomorphIncl (generatedTenthAxisLowerRecoveryJointCompactPauli g) *
    monsterMonomialPermutationHolomorph (generatedTenthAxisLowerRecoveryJointCompactLeft g) *
    monsterMonomialDiagonalHolomorph (generatedTwelfthSpinCompactPhase
      (generatedTenthAxisLowerRecoveryJointCompactFirstPhaseRows g)) *
    ((generatedTenthAxisLowerRecoveryJointCompactHadamardWord g).map
      generatedNinthLowerSpinHadamard).prod *
    monsterMonomialDiagonalHolomorph (generatedTwelfthSpinCompactPhase
      (generatedTenthAxisLowerRecoveryJointCompactSecondPhaseRows g)) *
    monsterMonomialPermutationHolomorph (generatedTenthAxisLowerRecoveryJointCompactRight g)

/-- Full actual extraspecial Fourier-word action, retaining every central coefficient. -/
def generatedTenthAxisLowerRecoveryJointCompactFourierQImage (g : Fin 1) (q : Q) : Q :=
  (generatedTenthAxisLowerRecoveryJointCompactHadamardWord g).foldr
    generatedNinthLowerSpinHadamardQImage q

/-- The full actual extraspecial action of the complete joint compact source product. -/
def generatedTenthAxisLowerRecoveryJointCompactQImage (g : Fin 1) (q : Q) : Q :=
  generatedTenthAxisLowerRecoveryJointCompactPauli g *
    monsterMonomialPermutationImage (generatedTenthAxisLowerRecoveryJointCompactLeft g)
      (monsterMonomialDiagonalImage (generatedTwelfthSpinCompactPhase
        (generatedTenthAxisLowerRecoveryJointCompactFirstPhaseRows g))
        (generatedTenthAxisLowerRecoveryJointCompactFourierQImage g
          (monsterMonomialDiagonalImage (generatedTwelfthSpinCompactPhase
            (generatedTenthAxisLowerRecoveryJointCompactSecondPhaseRows g))
            (monsterMonomialPermutationImage (generatedTenthAxisLowerRecoveryJointCompactRight g)
              q)))) *
    (generatedTenthAxisLowerRecoveryJointCompactPauli g)⁻¹

private theorem fourier_list_conjugation (w : List (Fin 12)) (q : Q) :
    spinConjugation ((w.map generatedNinthLowerSpinHadamard).prod) q =
      w.foldr generatedNinthLowerSpinHadamardQImage q := by
  induction w with
  | nil => simp only [List.map_nil, List.prod_nil, List.foldr_nil, map_one, MulAut.one_apply]
  | cons k w ih =>
    rw [List.map_cons, List.prod_cons, List.foldr_cons, map_mul]
    change spinConjugation (generatedNinthLowerSpinHadamard k)
      (spinConjugation ((w.map generatedNinthLowerSpinHadamard).prod) q) = _
    rw [ih, generatedNinth_lower_spin_hadamard_conjugation]

/-- The entire genuine compact conjugation is exactly its full original coordinate formula. -/
theorem generatedTenth_axis_lower_recovery_joint_compact_conjugation (g : Fin 1) (q : Q) :
    spinConjugation (generatedTenthAxisLowerRecoveryJointCompactSpin g) q =
      generatedTenthAxisLowerRecoveryJointCompactQImage g q := by
  rw [generatedTenthAxisLowerRecoveryJointCompactSpin]
  simp only [map_mul, MulAut.mul_apply]
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation, fourier_list_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation, spinConjugation_incl]
  rfl

/-- Complete original 24-coordinate binary certificate required of a genuine compact model. -/
def generatedTenthAxisLowerRecoveryJointCompactBinaryCondition (g : Fin 1) : Prop :=
  ∀ j : Fin 24,
    toAdd (qQuotHom (generatedTenthAxisLowerRecoveryJointCompactQImage g (qCoordinateGenerator j)))
      =
      monsterCo1GeometryBinaryMaskDecode (generatedTenthAxisLowerRecoveryJointCompactBinaryColumns g
        j)

/-- The complete original preferred extraspecial coordinate image, including its central phase. -/
def generatedTenthAxisLowerRecoveryJointCompactFullQCache (g : Fin 1) (j : Fin 24) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode
    (generatedTenthAxisLowerRecoveryJointCompactBinaryColumns g j)),
    ofAdd (generatedTenthAxisLowerRecoveryJointCompactFullQPhase g j)⟩

/-- Complete original 24-coordinate full-Q certificate required for fast actual C actions. -/
def generatedTenthAxisLowerRecoveryJointCompactFullQCondition (g : Fin 1) : Prop :=
  ∀ j : Fin 24,
    generatedTenthAxisLowerRecoveryJointCompactQImage g (qCoordinateGenerator j) =
      generatedTenthAxisLowerRecoveryJointCompactFullQCache g j

/-- The full-Q cache evaluates the actual original group normal form on arbitrary inputs. -/
def generatedTenthAxisLowerRecoveryJointCompactFullQFast (g : Fin 1) (q : Q) : Q :=
  monsterNortonCoordinateEvaluation (generatedTenthAxisLowerRecoveryJointCompactFullQCache g) q

/-- Whole genuine extraspecial action follows from its complete 24 full-coordinate certificates. -/
theorem generatedTenth_axis_lower_recovery_joint_compact_full_Q_fast (g : Fin 1)
    (h : generatedTenthAxisLowerRecoveryJointCompactFullQCondition g) (q : Q) :
    spinConjugation (generatedTenthAxisLowerRecoveryJointCompactSpin g) q =
      generatedTenthAxisLowerRecoveryJointCompactFullQFast g q := by
  apply monsterNortonCoordinateEvaluation_eq
  intro j
  rw [generatedTenth_axis_lower_recovery_joint_compact_conjugation]
  exact h j

/-- The actual joint spatial element is literally original9 times original1. -/
def generatedTenthAxisLowerRecoveryJointCompactSpatial (_g : Fin 1) : leechIsomSubgroup :=
  generatedTenthAxisLowerRecoveryCompactSpatial 9 * generatedTenthAxisLowerRecoveryCompactSpatial 1

/-- Every actual original lattice coordinate must match the entire retained binary source data. -/
def generatedTenthAxisLowerRecoveryJointCompactSpatialBinaryCondition (g : Fin 1) : Prop :=
  ∀ j : Fin 24,
    leechBinaryAction (generatedTenthAxisLowerRecoveryJointCompactSpatial g)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
        monsterCo1GeometryBinaryMaskDecode
          (generatedTenthAxisLowerRecoveryJointCompactBinaryColumns g j)

/-- The actual whole physical numerator and denominator must match the retained source data. -/
def generatedTenthAxisLowerRecoveryJointCompactPhysicalCondition (g : Fin 1) : Prop :=
  (generatedTenthAxisLowerRecoveryJointCompactSpatialDenominator g : ℝ) •
    leechIsomMatrix (generatedTenthAxisLowerRecoveryJointCompactSpatial g) =
      (generatedTenthAxisLowerRecoveryJointCompactSpatialNumerator g).map (Int.castRingHom ℝ)

private theorem binary_equiv_eq_of_columns
    (e f : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (h : ∀ j : Fin 24,
      e (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
        f (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val))) : e = f := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext'
  intro j
  simpa only [Pi.basisFun_apply, generatedTwelfth_spin_compact_binary_basis] using h j

/-- Genuine compatibility follows only from complete actual spin and lattice binary certificates. -/
theorem generatedTenth_axis_lower_recovery_joint_compact_compatibility (g : Fin 1)
    (hspin : generatedTenthAxisLowerRecoveryJointCompactBinaryCondition g)
    (hspatial : generatedTenthAxisLowerRecoveryJointCompactSpatialBinaryCondition g) :
    spinBinaryAction (generatedTenthAxisLowerRecoveryJointCompactSpin g) =
      leechBinaryAction (generatedTenthAxisLowerRecoveryJointCompactSpatial g) := by
  apply binary_equiv_eq_of_columns
  intro j
  rw [hspatial j, generatedTwelfth_spin_compact_binary_basis]
  change qBinaryAction (spinConjugation (generatedTenthAxisLowerRecoveryJointCompactSpin g))
    (toAdd (qQuotHom (qCoordinateGenerator j))) = _
  rw [qBinaryAction_apply, generatedTenth_axis_lower_recovery_joint_compact_conjugation]
  exact hspin j

/-- A certified model is a genuine element of the original defining compatible fiber product. -/
def generatedTenthAxisLowerRecoveryJointCompactFiber (g : Fin 1)
    (hspin : generatedTenthAxisLowerRecoveryJointCompactBinaryCondition g)
    (hspatial : generatedTenthAxisLowerRecoveryJointCompactSpatialBinaryCondition g) :
    localFiberSubgroup :=
  ⟨(generatedTenthAxisLowerRecoveryJointCompactSpin g,
    generatedTenthAxisLowerRecoveryJointCompactSpatial g),
    generatedTenth_axis_lower_recovery_joint_compact_compatibility g hspin hspatial⟩

/-- The certified compact fiber is an actual element of the genuine original local group. -/
def generatedTenthAxisLowerRecoveryJointCompactLocal (g : Fin 1)
    (hspin : generatedTenthAxisLowerRecoveryJointCompactBinaryCondition g)
    (hspatial : generatedTenthAxisLowerRecoveryJointCompactSpatialBinaryCondition g) : H :=
  localFiberIntoH (generatedTenthAxisLowerRecoveryJointCompactFiber g hspin hspatial)

/-- Full signed-short support, zero coefficients, and preferred phases remain obligatory. -/
def generatedTenthAxisLowerRecoveryJointCompactShortCondition (g : Fin 1)
    (hspin : generatedTenthAxisLowerRecoveryJointCompactBinaryCondition g)
    (hspatial : generatedTenthAxisLowerRecoveryJointCompactSpatialBinaryCondition g) : Prop :=
  ∀ r : GriessShortIndex,
    qSign (localShortPhase (generatedTenthAxisLowerRecoveryJointCompactFiber g hspin hspatial) r) *
      (griessConwayEncode generatedTenthAxis).2.1 r =
        (griessConwayEncode generatedTenthAxis).2.1
          (griessShortPermutation (generatedTenthAxisLowerRecoveryJointCompactSpatial g) r)

/-- Every full actual tensor column, with the entire original normalization, remains obligatory. -/
def generatedTenthAxisLowerRecoveryJointCompactTensorCondition (g : Fin 1)
    (hspin : generatedTenthAxisLowerRecoveryJointCompactBinaryCondition g)
    (hspatial : generatedTenthAxisLowerRecoveryJointCompactSpatialBinaryCondition g) : Prop :=
  localTensorRepresentation (generatedTenthAxisLowerRecoveryJointCompactFiber g hspin hspatial)
    (griessConwayEncode generatedTenthAxis).2.2 = (griessConwayEncode generatedTenthAxis).2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
