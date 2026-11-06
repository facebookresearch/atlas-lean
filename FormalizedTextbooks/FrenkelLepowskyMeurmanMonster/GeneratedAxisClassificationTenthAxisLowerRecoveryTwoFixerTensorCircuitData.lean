/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorCircuitData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoFixerSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryJointPackedCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedCandidate10Cache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryPackedInput
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalTensorSourceActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthSpinTensorFourierAddresses

/-! Ungated exact two-fixer full tensor circuit assembly. All source bindings remain explicit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The only two actual compatible fibers are the literal joint9*1 and original10. -/
def generatedTenthTwoFixerTensorFiber (g : Fin 2) : localFiberSubgroup :=
  if g = 0 then generatedTenthTwoFixerJointFiber else generatedTenthTwoFixerOriginalTenFiber

/-- Complete original spin source for the two required fixers. -/
def generatedTenthTwoFixerTensorSpin (g : Fin 2) : SpinHolomorph :=
  if g = 0 then generatedTenthAxisLowerRecoveryJointCompactSpin 0
  else generatedTenthAxisLowerRecoveryCompactSpin 10

/-- Complete original right source for the two required fixers. -/
def generatedTenthTwoFixerTensorRight (g : Fin 2) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  if g = 0 then generatedTenthAxisLowerRecoveryJointCompactRight 0
  else generatedTenthAxisLowerRecoveryCompactRight 10

/-- Complete original left source for the two required fixers. -/
def generatedTenthTwoFixerTensorLeft (g : Fin 2) : SpinIndex ≃ₗ[ZMod 2] SpinIndex :=
  if g = 0 then generatedTenthAxisLowerRecoveryJointCompactLeft 0
  else generatedTenthAxisLowerRecoveryCompactLeft 10

/-- Complete original pauli source for the two required fixers. -/
def generatedTenthTwoFixerTensorPauli (g : Fin 2) : Q :=
  if g = 0 then generatedTenthAxisLowerRecoveryJointCompactPauli 0
  else generatedTenthAxisLowerRecoveryCompactPauli 10

/-- Complete original hadamardword source for the two required fixers. -/
def generatedTenthTwoFixerTensorHadamardWord (g : Fin 2) : List (Fin 12) :=
  if g = 0 then generatedTenthAxisLowerRecoveryJointCompactHadamardWord 0
  else generatedTenthAxisLowerRecoveryCompactHadamardWord 10

/-- Complete original numerator source for the two required fixers. -/
def generatedTenthTwoFixerTensorNumerator (g : Fin 2) : Matrix (Fin 24) (Fin 24) ℤ :=
  if g = 0 then generatedTenthAxisLowerRecoveryJointCompactSpatialNumerator 0
  else generatedTenthAxisLowerRecoveryCompactSpatialNumerator 10

/-- Complete original denominator source for the two required fixers. -/
def generatedTenthTwoFixerTensorDenominator (g : Fin 2) : ℕ :=
  if g = 0 then generatedTenthAxisLowerRecoveryJointCompactSpatialDenominator 0
  else generatedTenthAxisLowerRecoveryCompactSpatialDenominator 10

/-- The complete original first quadratic source. -/
def generatedTenthTwoFixerTensorFirstPhase (g : Fin 2) : Fin 12 → Fin 12 → ZMod 2 :=
  generatedTwelfthSpinCompactPhase
    (if g = 0 then generatedTenthAxisLowerRecoveryJointCompactFirstPhaseRows 0
    else generatedTenthAxisLowerRecoveryCompactFirstPhaseRows 10)

/-- The complete original second quadratic source. -/
def generatedTenthTwoFixerTensorSecondPhase (g : Fin 2) : Fin 12 → Fin 12 → ZMod 2 :=
  generatedTwelfthSpinCompactPhase
    (if g = 0 then generatedTenthAxisLowerRecoveryJointCompactSecondPhaseRows 0
    else generatedTenthAxisLowerRecoveryCompactSecondPhaseRows 10)

/-- Cache stages apply the genuine commuting Fourier pairs in ascending bit order. -/
def generatedTenthTwoFixerTensorPairs (g : Fin 2) : List (Fin 12 × Fin 12) :=
  if g = 0 then [(0, 1), (2, 3), (4, 5), (6, 7), (8, 9)]
  else [(0, 1), (2, 3), (4, 5), (6, 7)]

/-- All signed original input digits, with no coordinate omitted. -/
def generatedTenthTwoFixerTensorInput (n : Fin 4096) (j : Fin 24) : ℤ :=
  generatedNinthLowerSpinTensorPackedCoordinate
    (generatedTenthAxisLowerRecoveryPackedInputWords j) n

/-- Every pair stage and the retained final post stage decode all4096 original signed coordinates.
-/
def generatedTenthTwoFixerTensorState (g : Fin 2) (s : ℕ) (n : Fin 4096) (j : Fin 24) : ℤ :=
  generatedNinthLowerSpinTensorPackedCoordinate
    (if g = 0 then generatedTenthAxisLowerRecoveryJointPackedCache
      ⟨s % 7, Nat.mod_lt _ (by decide)⟩ j
    else generatedTenthAxisLowerRecoveryPackedCandidate10Cache
      ⟨s % 6, Nat.mod_lt _ (by decide)⟩ j) n

/-- The actual complete integer physical numerator acts before compact spin transport. -/
def generatedTenthTwoFixerTensorSpatialInteger (g : Fin 2) (n : Fin 4096) (j : Fin 24) : ℤ :=
  ∑ k : Fin 24, generatedTenthTwoFixerTensorNumerator g j k * generatedTenthTwoFixerTensorInput n k

/-- The genuine compact pre operator keeps the complete second quadratic source. -/
def generatedTenthTwoFixerTensorPre (g : Fin 2) : SpinHolomorph :=
  monsterMonomialDiagonalHolomorph (generatedTenthTwoFixerTensorSecondPhase g) *
    monsterMonomialPermutationHolomorph (generatedTenthTwoFixerTensorRight g)

/-- The genuine compact post operator retains the actual central Pauli correction. -/
def generatedTenthTwoFixerTensorPost (g : Fin 2) : SpinHolomorph :=
  spinHolomorphIncl (generatedTenthTwoFixerTensorPauli g) *
    monsterMonomialPermutationHolomorph (generatedTenthTwoFixerTensorLeft g) *
      monsterMonomialDiagonalHolomorph (generatedTenthTwoFixerTensorFirstPhase g)

/-- Complete genuine pre-boundary source labels and signs, without assuming a cached address table.
-/
def generatedTenthTwoFixerTensorPreInteger (g : Fin 2) (v : NortonUIntegerVector)
    (n : Fin 4096) : ℤ :=
  generatedAxisGlobalIntSign (monsterMonomialQuadratic
    (generatedTenthTwoFixerTensorSecondPhase g) (golayLabelCoefficients n)) *
      v (nortonUIntegerLabel ((generatedTenthTwoFixerTensorRight g).symm (golayLabelCoefficients
        n)))

/-- All original post-boundary signs include the full actual Pauli central field. -/
def generatedTenthTwoFixerTensorPostInteger (g : Fin 2) (v : NortonUIntegerVector)
    (n : Fin 4096) : ℤ :=
  let t := golayLabelCoefficients n
  let u := (generatedTenthTwoFixerTensorLeft g).symm
    (t + spinTranslation (generatedTenthTwoFixerTensorPauli g))
  generatedAxisGlobalIntSign (spinPhase (generatedTenthTwoFixerTensorPauli g) t) *
    generatedAxisGlobalIntSign (monsterMonomialQuadratic (generatedTenthTwoFixerTensorFirstPhase g)
      u) *
      v (nortonUIntegerLabel u)

/-- Stage0 already includes division by the actual spatial denominator; this scalar is retained. -/
def GeneratedTenthTwoFixerTensorStartCondition : Prop :=
  ∀ (g : Fin 2) (j : Fin 24) (n : Fin 4096),
    (generatedTenthTwoFixerTensorDenominator g : ℤ) * generatedTenthTwoFixerTensorState g 0 n j =
      generatedTenthTwoFixerTensorPreInteger g
        (fun m => generatedTenthTwoFixerTensorSpatialInteger g m j) n

/-- All genuine Fourier pairs carry the entire signed coordinate vector to the next stage. -/
def GeneratedTenthTwoFixerTensorPairCondition : Prop :=
  ∀ (g : Fin 2) (j : Fin 24) (s : ℕ) (p : Fin 12 × Fin 12),
    (generatedTenthTwoFixerTensorPairs g)[s]? = some p → ∀ n : Fin 4096,
      generatedNinthLowerSpinTensorFourierInteger p.1
        (generatedNinthLowerSpinTensorFourierInteger p.2
          (fun m => generatedTenthTwoFixerTensorState g s m j)) n =
            2 * generatedTenthTwoFixerTensorState g (s + 1) n j

/-- The retained final post stage and every original input coordinate must both match exactly. -/
def GeneratedTenthTwoFixerTensorFinishCondition : Prop :=
  ∀ (g : Fin 2) (j : Fin 24) (n : Fin 4096),
    generatedTenthTwoFixerTensorPostInteger g
      (fun m => generatedTenthTwoFixerTensorState g (generatedTenthTwoFixerTensorPairs g).length m
        j) n =
        generatedTenthTwoFixerTensorState g ((generatedTenthTwoFixerTensorPairs g).length + 1) n j ∧
    generatedTenthTwoFixerTensorState g ((generatedTenthTwoFixerTensorPairs g).length + 1) n j =
      generatedTenthTwoFixerTensorInput n j

/-- The entire physical numerator must bind the actual chosen compatible fiber's spatial action. -/
def GeneratedTenthTwoFixerTensorPhysicalCondition : Prop :=
  ∀ g : Fin 2, (generatedTenthTwoFixerTensorDenominator g : ℝ) •
    leechIsomMatrix (generatedTenthTwoFixerTensorFiber g).val.2 =
      (generatedTenthTwoFixerTensorNumerator g).map (Int.castRingHom ℝ)

/-- Exact source input binding retains every full final tensor source numerator at scale512sqrt2. -/
def GeneratedTenthTwoFixerTensorInputCondition : Prop :=
  ∀ (n : Fin 4096) (j : Fin 24),
    8 * generatedTenthFinalTensorSourceQ n j = (generatedTenthTwoFixerTensorInput n j : ℚ)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
