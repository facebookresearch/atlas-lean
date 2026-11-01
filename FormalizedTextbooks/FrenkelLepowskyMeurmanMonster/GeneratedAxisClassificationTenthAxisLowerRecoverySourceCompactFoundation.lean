/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinCompactBinaryCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQCoordinateEvaluation

/-! Genuine compact constructors and exact full-source certificate obligations
for the actual original Root02 source spin. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Both complete original compact coordinate maps have their exact two-sided inverses. -/
theorem generatedTenth_axis_lower_recovery_source_compact_matrix_inverse : ∀ g : Fin 1,
    (generatedTwelfthSpinCompactMatrix
        (generatedTenthAxisLowerRecoverySourceCompactLeftInverseColumns g) *
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoverySourceCompactLeftColumns
        g) = 1 ∧
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoverySourceCompactLeftColumns
        g) *
        generatedTwelfthSpinCompactMatrix
          (generatedTenthAxisLowerRecoverySourceCompactLeftInverseColumns g) = 1) ∧
    (generatedTwelfthSpinCompactMatrix
        (generatedTenthAxisLowerRecoverySourceCompactRightInverseColumns g) *
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoverySourceCompactRightColumns
        g) = 1 ∧
      generatedTwelfthSpinCompactMatrix (generatedTenthAxisLowerRecoverySourceCompactRightColumns
        g) *
        generatedTwelfthSpinCompactMatrix
          (generatedTenthAxisLowerRecoverySourceCompactRightInverseColumns g) = 1) := by
  decide +kernel

/-- The actual left original binary coordinate equivalence. -/
def generatedTenthAxisLowerRecoverySourceCompactLeft (g : Fin 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  generatedTwelfthSpinCompactEquiv (generatedTenthAxisLowerRecoverySourceCompactLeftColumns g)
    (generatedTenthAxisLowerRecoverySourceCompactLeftInverseColumns g)
    (generatedTenth_axis_lower_recovery_source_compact_matrix_inverse g).1.1
    (generatedTenth_axis_lower_recovery_source_compact_matrix_inverse g).1.2

/-- The actual right original binary coordinate equivalence. -/
def generatedTenthAxisLowerRecoverySourceCompactRight (g : Fin 1) : SpinIndex ≃ₗ[ZMod 2] SpinIndex
  :=
  generatedTwelfthSpinCompactEquiv (generatedTenthAxisLowerRecoverySourceCompactRightColumns g)
    (generatedTenthAxisLowerRecoverySourceCompactRightInverseColumns g)
    (generatedTenth_axis_lower_recovery_source_compact_matrix_inverse g).2.1
    (generatedTenth_axis_lower_recovery_source_compact_matrix_inverse g).2.2

/-- The full actual original Pauli factor, retaining its central phase. -/
def generatedTenthAxisLowerRecoverySourceCompactPauli (g : Fin 1) : Q :=
  ⟨ofAdd (Fin.append
    (golayLabelCoefficients (generatedTenthAxisLowerRecoverySourceCompactPauliLabels g).1)
    (golayLabelCoefficients (generatedTenthAxisLowerRecoverySourceCompactPauliLabels g).2.1)),
    ofAdd (generatedTenthAxisLowerRecoverySourceCompactPauliLabels g).2.2⟩

/-- All prescribed original Fourier factors in their actual coordinate order. -/
def generatedTenthAxisLowerRecoverySourceCompactHadamardWord (g : Fin 1) : List (Fin 12) :=
  (List.finRange 12).filter fun k =>
    k.val < (generatedTenthAxisLowerRecoverySourceCompactHadamardRank g).val

/-- The original source spin is an actual product of genuine original orthogonal
spin normalizers. -/
def generatedTenthAxisLowerRecoverySourceCompactSpin (g : Fin 1) : SpinHolomorph :=
  spinHolomorphIncl (generatedTenthAxisLowerRecoverySourceCompactPauli g) *
    monsterMonomialPermutationHolomorph (generatedTenthAxisLowerRecoverySourceCompactLeft g) *
    monsterMonomialDiagonalHolomorph (generatedTwelfthSpinCompactPhase
      (generatedTenthAxisLowerRecoverySourceCompactFirstPhaseRows g)) *
    ((generatedTenthAxisLowerRecoverySourceCompactHadamardWord g).map
      generatedNinthLowerSpinHadamard).prod *
    monsterMonomialDiagonalHolomorph (generatedTwelfthSpinCompactPhase
      (generatedTenthAxisLowerRecoverySourceCompactSecondPhaseRows g)) *
    monsterMonomialPermutationHolomorph (generatedTenthAxisLowerRecoverySourceCompactRight g)

/-- Full actual extraspecial Fourier-word action, retaining every central coefficient. -/
def generatedTenthAxisLowerRecoverySourceCompactFourierQImage (g : Fin 1) (q : Q) : Q :=
  (generatedTenthAxisLowerRecoverySourceCompactHadamardWord g).foldr
    generatedNinthLowerSpinHadamardQImage q

/-- The full actual extraspecial action of the complete compact source product. -/
def generatedTenthAxisLowerRecoverySourceCompactQImage (g : Fin 1) (q : Q) : Q :=
  generatedTenthAxisLowerRecoverySourceCompactPauli g *
    monsterMonomialPermutationImage (generatedTenthAxisLowerRecoverySourceCompactLeft g)
      (monsterMonomialDiagonalImage (generatedTwelfthSpinCompactPhase
        (generatedTenthAxisLowerRecoverySourceCompactFirstPhaseRows g))
        (generatedTenthAxisLowerRecoverySourceCompactFourierQImage g
          (monsterMonomialDiagonalImage (generatedTwelfthSpinCompactPhase
            (generatedTenthAxisLowerRecoverySourceCompactSecondPhaseRows g))
            (monsterMonomialPermutationImage (generatedTenthAxisLowerRecoverySourceCompactRight g)
              q)))) *
    (generatedTenthAxisLowerRecoverySourceCompactPauli g)⁻¹

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
theorem generatedTenth_axis_lower_recovery_source_compact_conjugation (g : Fin 1) (q : Q) :
    spinConjugation (generatedTenthAxisLowerRecoverySourceCompactSpin g) q =
      generatedTenthAxisLowerRecoverySourceCompactQImage g q := by
  rw [generatedTenthAxisLowerRecoverySourceCompactSpin]
  simp only [map_mul, MulAut.mul_apply]
  rw [monsterMonomialPermutationHolomorph_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation, fourier_list_conjugation,
    monsterMonomialDiagonalHolomorph_conjugation,
    monsterMonomialPermutationHolomorph_conjugation, spinConjugation_incl]
  rfl

/-- Complete original 24-coordinate binary certificate required of a genuine compact model. -/
def generatedTenthAxisLowerRecoverySourceCompactBinaryCondition (g : Fin 1) : Prop :=
  ∀ j : Fin 24,
    toAdd (qQuotHom (generatedTenthAxisLowerRecoverySourceCompactQImage g (qCoordinateGenerator
      j))) =
      monsterCo1GeometryBinaryMaskDecode
        (generatedTenthAxisLowerRecoverySourceCompactBinaryColumns g j)

/-- The complete original preferred extraspecial coordinate image, including its central phase. -/
def generatedTenthAxisLowerRecoverySourceCompactFullQCache (g : Fin 1) (j : Fin 24) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode
    (generatedTenthAxisLowerRecoverySourceCompactBinaryColumns g j)),
    ofAdd (generatedTenthAxisLowerRecoverySourceCompactFullQPhase g j)⟩

/-- Complete original 24-coordinate full-Q certificate required for fast actual C actions. -/
def generatedTenthAxisLowerRecoverySourceCompactFullQCondition (g : Fin 1) : Prop :=
  ∀ j : Fin 24,
    generatedTenthAxisLowerRecoverySourceCompactQImage g (qCoordinateGenerator j) =
      generatedTenthAxisLowerRecoverySourceCompactFullQCache g j

/-- The full-Q cache evaluates the actual original group normal form on arbitrary inputs. -/
def generatedTenthAxisLowerRecoverySourceCompactFullQFast (g : Fin 1) (q : Q) : Q :=
  monsterNortonCoordinateEvaluation (generatedTenthAxisLowerRecoverySourceCompactFullQCache g) q

/-- Whole genuine extraspecial action follows from its complete 24 full-coordinate certificates. -/
theorem generatedTenth_axis_lower_recovery_source_compact_full_Q_fast (g : Fin 1)
    (h : generatedTenthAxisLowerRecoverySourceCompactFullQCondition g) (q : Q) :
    spinConjugation (generatedTenthAxisLowerRecoverySourceCompactSpin g) q =
      generatedTenthAxisLowerRecoverySourceCompactFullQFast g q := by
  apply monsterNortonCoordinateEvaluation_eq
  intro j
  rw [generatedTenth_axis_lower_recovery_source_compact_conjugation]
  exact h j

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
