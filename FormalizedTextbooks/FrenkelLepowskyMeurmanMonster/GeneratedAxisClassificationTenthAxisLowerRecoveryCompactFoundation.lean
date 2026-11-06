/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactBinaryCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

/-! Genuine compact constructors and exact full-source certificate obligations
for all eleven lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Both complete original compact coordinate maps have their exact two-sided inverses. -/
theorem generatedTenth_axis_lower_recovery_compact_matrix_inverse : ∀ g : Fin 11,
    (generatedTwelfthSpinCompactMatrix
        (generatedTenthAxisLowerRecoveryCompactLeftInverseColumns g) *
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoveryCompactLeftColumns g) = 1 ∧
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoveryCompactLeftColumns g) *
        generatedTwelfthSpinCompactMatrix
          (generatedTenthAxisLowerRecoveryCompactLeftInverseColumns g) = 1) ∧
    (generatedTwelfthSpinCompactMatrix
        (generatedTenthAxisLowerRecoveryCompactRightInverseColumns g) *
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoveryCompactRightColumns g) = 1 ∧
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoveryCompactRightColumns g) *
        generatedTwelfthSpinCompactMatrix
          (generatedTenthAxisLowerRecoveryCompactRightInverseColumns g) = 1) := by
  decide +kernel

/-- The actual left original binary coordinate equivalence. -/
def generatedTenthAxisLowerRecoveryCompactLeft (g : Fin 11) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedTwelfthSpinCompactEquiv (generatedTenthAxisLowerRecoveryCompactLeftColumns g)
    (generatedTenthAxisLowerRecoveryCompactLeftInverseColumns g)
    (generatedTenth_axis_lower_recovery_compact_matrix_inverse g).1.1
    (generatedTenth_axis_lower_recovery_compact_matrix_inverse g).1.2

/-- The actual right original binary coordinate equivalence. -/
def generatedTenthAxisLowerRecoveryCompactRight (g : Fin 11) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedTwelfthSpinCompactEquiv (generatedTenthAxisLowerRecoveryCompactRightColumns g)
    (generatedTenthAxisLowerRecoveryCompactRightInverseColumns g)
    (generatedTenth_axis_lower_recovery_compact_matrix_inverse g).2.1
    (generatedTenth_axis_lower_recovery_compact_matrix_inverse g).2.2

/-- The full actual original Pauli factor, retaining its central phase. -/
def generatedTenthAxisLowerRecoveryCompactPauli (g : Fin 11) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients (generatedTenthAxisLowerRecoveryCompactPauliLabels g).1)
    (golayLabelCoefficients (generatedTenthAxisLowerRecoveryCompactPauliLabels g).2.1)),
    ofAdd (generatedTenthAxisLowerRecoveryCompactPauliLabels g).2.2⟩

/-- All prescribed original Fourier factors in their actual coordinate order. -/
def generatedTenthAxisLowerRecoveryCompactHadamardWord (g : Fin 11) : List (Fin 12) :=
  (List.finRange 12).filter fun k =>
    k.val < (generatedTenthAxisLowerRecoveryCompactHadamardRank g).val

/-- Each proposed spin lift is an actual product of genuine original orthogonal spin normalizers. -/
def generatedTenthAxisLowerRecoveryCompactSpin (g : Fin 11) : SpinHolomorph :=
  spinHolomorphIncl (generatedTenthAxisLowerRecoveryCompactPauli g) *
    monsterMonomialPermutationHolomorph (generatedTenthAxisLowerRecoveryCompactLeft g) *
    monsterMonomialDiagonalHolomorph (generatedTwelfthSpinCompactPhase
      (generatedTenthAxisLowerRecoveryCompactFirstPhaseRows g)) *
    ((generatedTenthAxisLowerRecoveryCompactHadamardWord g).map
      generatedNinthLowerSpinHadamard).prod *
    monsterMonomialDiagonalHolomorph (generatedTwelfthSpinCompactPhase
      (generatedTenthAxisLowerRecoveryCompactSecondPhaseRows g)) *
    monsterMonomialPermutationHolomorph (generatedTenthAxisLowerRecoveryCompactRight g)

/-- Full actual extraspecial Fourier-word action, retaining every central coefficient. -/
def generatedTenthAxisLowerRecoveryCompactFourierQImage (g : Fin 11) (q : Q) : Q :=
  (generatedTenthAxisLowerRecoveryCompactHadamardWord g).foldr
    generatedNinthLowerSpinHadamardQImage q

/-- The full actual extraspecial action of every complete compact source product. -/
def generatedTenthAxisLowerRecoveryCompactQImage (g : Fin 11) (q : Q) : Q :=
  generatedTenthAxisLowerRecoveryCompactPauli g *
    monsterMonomialPermutationImage (generatedTenthAxisLowerRecoveryCompactLeft g)
      (monsterMonomialDiagonalImage (generatedTwelfthSpinCompactPhase
        (generatedTenthAxisLowerRecoveryCompactFirstPhaseRows g))
        (generatedTenthAxisLowerRecoveryCompactFourierQImage g
          (monsterMonomialDiagonalImage (generatedTwelfthSpinCompactPhase
            (generatedTenthAxisLowerRecoveryCompactSecondPhaseRows g))
            (monsterMonomialPermutationImage (generatedTenthAxisLowerRecoveryCompactRight g) q)))) *
    (generatedTenthAxisLowerRecoveryCompactPauli g)⁻¹

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
theorem generatedTenth_axis_lower_recovery_compact_conjugation (g : Fin 11) (q : Q) :
    spinConjugation (generatedTenthAxisLowerRecoveryCompactSpin g) q =
      generatedTenthAxisLowerRecoveryCompactQImage g q := by
  rw [generatedTenthAxisLowerRecoveryCompactSpin]
  simp only [map_mul, MulAut.mul_apply]
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation, fourier_list_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation, spinConjugation_incl]
  rfl

/-- Complete original 24-coordinate binary certificate required of a genuine compact model. -/
def generatedTenthAxisLowerRecoveryCompactBinaryCondition (g : Fin 11) : Prop :=
  ∀ j : Fin 24,
    toAdd (qQuotHom (generatedTenthAxisLowerRecoveryCompactQImage g (qCoordinateGenerator j))) =
      monsterCo1GeometryBinaryMaskDecode (generatedTenthAxisLowerRecoveryCompactBinaryColumns g j)

/-- The complete original preferred extraspecial coordinate image, including its central phase. -/
def generatedTenthAxisLowerRecoveryCompactFullQCache (g : Fin 11) (j : Fin 24) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode
    (generatedTenthAxisLowerRecoveryCompactBinaryColumns g j)),
    ofAdd (generatedTenthAxisLowerRecoveryCompactFullQPhase g j)⟩

/-- Complete original 24-coordinate full-Q certificate required for fast actual C actions. -/
def generatedTenthAxisLowerRecoveryCompactFullQCondition (g : Fin 11) : Prop :=
  ∀ j : Fin 24,
    generatedTenthAxisLowerRecoveryCompactQImage g (qCoordinateGenerator j) =
      generatedTenthAxisLowerRecoveryCompactFullQCache g j

/-- The full-Q cache evaluates the actual original group normal form on arbitrary inputs. -/
def generatedTenthAxisLowerRecoveryCompactFullQFast (g : Fin 11) (q : Q) : Q :=
  monsterNortonCoordinateEvaluation (generatedTenthAxisLowerRecoveryCompactFullQCache g) q

/-- Whole genuine extraspecial action follows from its complete 24 full-coordinate certificates. -/
theorem generatedTenth_axis_lower_recovery_compact_full_Q_fast (g : Fin 11)
    (h : generatedTenthAxisLowerRecoveryCompactFullQCondition g) (q : Q) :
    spinConjugation (generatedTenthAxisLowerRecoveryCompactSpin g) q =
      generatedTenthAxisLowerRecoveryCompactFullQFast g q := by
  apply monsterNortonCoordinateEvaluation_eq
  intro j
  rw [generatedTenth_axis_lower_recovery_compact_conjugation]
  exact h j

/-- The entire eleven-element actual standard-coordinate spatial enumeration. -/
def generatedTenthAxisLowerRecoveryCompactStandardSpatial (g : Fin 11) : leechIsomSubgroup :=
  if h : g.val < 7 then
    golaySignIsometry (generatedTenthAxisLowerRecoveryCode
      (generatedTenthAxisLowerRecoverySignBasis ⟨g.val, h⟩))
  else if h' : g.val < 9 then
    generatedTenthAxisLowerRecoverySignedPermutationSpatial ⟨g.val - 7, by omega⟩
  else generatedTenthE7OrbitSpatialLetter ⟨g.val - 9, by omega⟩

/-- Every proposed spatial lift is the actual original-coordinate conjugate of its source. -/
def generatedTenthAxisLowerRecoveryCompactSpatial (g : Fin 11) : leechIsomSubgroup :=
  generatedTenthE7OrbitConjugation (generatedTenthAxisLowerRecoveryCompactStandardSpatial g)

/-- Every actual original lattice coordinate must match the entire retained binary source data. -/
def generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition (g : Fin 11) : Prop :=
  ∀ j : Fin 24,
    leechBinaryAction (generatedTenthAxisLowerRecoveryCompactSpatial g)
      (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
        monsterCo1GeometryBinaryMaskDecode
          (generatedTenthAxisLowerRecoveryCompactBinaryColumns g j)

/-- The actual whole physical numerator and denominator must match the retained source data. -/
def generatedTenthAxisLowerRecoveryCompactPhysicalCondition (g : Fin 11) : Prop :=
  (generatedTenthAxisLowerRecoveryCompactSpatialDenominator g : ℝ) •
    leechIsomMatrix (generatedTenthAxisLowerRecoveryCompactSpatial g) =
      (generatedTenthAxisLowerRecoveryCompactSpatialNumerator g).map (Int.castRingHom ℝ)

private theorem binary_equiv_eq_of_columns
    (e f : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (h : ∀ j : Fin 24,
      e (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val)) =
        f (monsterCo1GeometryBinaryMaskDecode (n := 24) (2 ^ j.val))) : e = f := by
  apply (Pi.basisFun (ZMod 2) (Fin 24)).ext'
  intro j
  simpa only [Pi.basisFun_apply, generatedTwelfth_spin_compact_binary_basis] using h j

/-- Genuine compatibility follows only from complete actual spin and lattice binary certificates. -/
theorem generatedTenth_axis_lower_recovery_compact_compatibility (g : Fin 11)
    (hspin : generatedTenthAxisLowerRecoveryCompactBinaryCondition g)
    (hspatial : generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition g) :
    spinBinaryAction (generatedTenthAxisLowerRecoveryCompactSpin g) =
      leechBinaryAction (generatedTenthAxisLowerRecoveryCompactSpatial g) := by
  apply binary_equiv_eq_of_columns
  intro j
  rw [hspatial j, generatedTwelfth_spin_compact_binary_basis]
  change qBinaryAction (spinConjugation (generatedTenthAxisLowerRecoveryCompactSpin g))
    (toAdd (qQuotHom (qCoordinateGenerator j))) = _
  rw [qBinaryAction_apply, generatedTenth_axis_lower_recovery_compact_conjugation]
  exact hspin j

/-- A certified model is a genuine element of the original defining compatible fiber product. -/
def generatedTenthAxisLowerRecoveryCompactFiber (g : Fin 11)
    (hspin : generatedTenthAxisLowerRecoveryCompactBinaryCondition g)
    (hspatial : generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition g) :
    localFiberSubgroup :=
  ⟨(generatedTenthAxisLowerRecoveryCompactSpin g, generatedTenthAxisLowerRecoveryCompactSpatial g),
    generatedTenth_axis_lower_recovery_compact_compatibility g hspin hspatial⟩

/-- The certified compact fiber is an actual element of the genuine original local group. -/
def generatedTenthAxisLowerRecoveryCompactLocal (g : Fin 11)
    (hspin : generatedTenthAxisLowerRecoveryCompactBinaryCondition g)
    (hspatial : generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition g) : H :=
  localFiberIntoH (generatedTenthAxisLowerRecoveryCompactFiber g hspin hspatial)

/-- Full original signed-short support, zero coefficients, and preferred phases
remain obligatory. -/
def generatedTenthAxisLowerRecoveryCompactShortCondition (g : Fin 11)
    (hspin : generatedTenthAxisLowerRecoveryCompactBinaryCondition g)
    (hspatial : generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition g) : Prop :=
  ∀ r : GriessShortIndex,
    qSign (localShortPhase (generatedTenthAxisLowerRecoveryCompactFiber g hspin hspatial) r) *
      (griessConwayEncode generatedTenthAxis).2.1 r =
        (griessConwayEncode generatedTenthAxis).2.1
          (griessShortPermutation (generatedTenthAxisLowerRecoveryCompactSpatial g) r)

/-- Every full actual tensor column, with the entire original normalization, remains obligatory. -/
def generatedTenthAxisLowerRecoveryCompactTensorCondition (g : Fin 11)
    (hspin : generatedTenthAxisLowerRecoveryCompactBinaryCondition g)
    (hspatial : generatedTenthAxisLowerRecoveryCompactSpatialBinaryCondition g) : Prop :=
  localTensorRepresentation (generatedTenthAxisLowerRecoveryCompactFiber g hspin hspatial)
    (griessConwayEncode generatedTenthAxis).2.2 = (griessConwayEncode generatedTenthAxis).2.2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
