/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPermutationLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100MathieuGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100MateOrientation

/-! Twelve literal original local words and explicit Q corrections for root-eight certification.
No full-axis fixation is assumed or asserted by these construction declarations. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- A complete fiber representative of each original canonical monomial factor. -/
def generatedRootEightCanonicalMonomialFiber (k : Fin 3) : localFiberSubgroup :=
  generatedFifthSignFiber (generatedFifthRootEightCanonicalSignLabels k) 0 *
    generatedFifthRootEightCanonicalPermutationFiber k

/-- The representative retains the original source sign and permutation local factors. -/
theorem generatedRootEight_canonical_monomial_fiber_local (k : Fin 3) :
    localFiberIntoH (generatedRootEightCanonicalMonomialFiber k) =
      generatedFifthRootEightCanonicalMonomialLocal k := by
  simp only [generatedRootEightCanonicalMonomialFiber, map_mul,
    generatedFifth_sign_fiber_local, generatedFifthRootEightCanonicalMonomialLocal]

/-- The entire canonical transport, represented with its full original local fiber factors. -/
def generatedRootEightCanonicalFiber : localFiberSubgroup :=
  generatedRootEightCanonicalMonomialFiber 2 * xiSpinLocalFiber * xiSpinLocalFiber *
    generatedRootEightCanonicalMonomialFiber 1 * xiSpinLocalFiber *
    generatedRootEightCanonicalMonomialFiber 0

/-- The entire fiber represents precisely the frozen three-monomial canonical local lift. -/
theorem generatedRootEight_canonical_fiber_local :
    localFiberIntoH generatedRootEightCanonicalFiber = generatedFifthRootEightCanonicalLocal := by
  simp only [generatedRootEightCanonicalFiber, map_mul,
    generatedRootEight_canonical_monomial_fiber_local, generatedFifthRootEightCanonicalLocal]

/-- The original nine-factor point-moving word with complete source spin lifts. -/
def generatedRootEightPointMoverFiber : localFiberSubgroup :=
  generatedRootEightPermutationWordFiber (leechNormSixHS100PointMoverPermutationWords 3) *
    generatedFifthSignFiber 1 0 *
    generatedRootEightPermutationWordFiber (leechNormSixHS100PointMoverPermutationWords 2) *
    xiSpinLocalFiber *
    generatedRootEightPermutationWordFiber (leechNormSixHS100PointMoverPermutationWords 1) *
    xiSpinLocalFiber * xiSpinLocalFiber * generatedFifthSignFiber 2816 0 *
    generatedRootEightPermutationWordFiber (leechNormSixHS100PointMoverPermutationWords 0)

/-- The original root-swap word followed by the genuine all-one Golay sign lift. -/
def generatedRootEightMateFiber : localFiberSubgroup :=
  generatedFifthSignFiber 2048 0 *
    generatedRootEightPermutationWordFiber leechNormSixHS100MatePermutationWord

/-- Ten original ordered-root Mathieu words, the literal mover, and the literal mate word. -/
def generatedRootEightGeneratorPrimitiveFiber (j : Fin 12) : localFiberSubgroup :=
  if h : j.val < 10 then
    generatedRootEightPermutationWordFiber (leechNormSixHS100MathieuGeneratorWords ⟨j.val, h⟩)
  else if j.val = 10 then generatedRootEightPointMoverFiber else generatedRootEightMateFiber

/-- The corresponding complete original local words before correction. -/
def generatedRootEightGeneratorPrimitiveLocal (j : Fin 12) : H :=
  localFiberIntoH (generatedRootEightGeneratorPrimitiveFiber j)

/-- Exact translation masks selected by the canonical whole-axis numerical discovery. -/
def generatedRootEightGeneratorTranslation : Fin 12 → Nat :=
  ![1839, 1760, 35, 1804, 242, 234, 85, 101, 15, 106, 3694, 2048]

/-- Exact modulation masks in the same original Schrödinger coordinates. -/
def generatedRootEightGeneratorModulation : Fin 12 → Nat :=
  ![493, 23, 1306, 351, 299, 1171, 283, 1047, 1349, 1231, 1372, 433]

/-- Exact central coefficients in the same original extraspecial coordinate model. -/
def generatedRootEightGeneratorConstant : Fin 12 → ZMod 2 :=
  ![0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1]

/-- Each correction is an actual original Q element, with all 24 base bits and central phase. -/
def generatedRootEightGeneratorCorrection (j : Fin 12) : Q :=
  ⟨ofAdd (fun i => if i.val < 12 then
      if (generatedRootEightGeneratorTranslation j).testBit i.val then 1 else 0
    else if (generatedRootEightGeneratorModulation j).testBit (i.val - 12) then 1 else 0),
    ofAdd (generatedRootEightGeneratorConstant j)⟩

/-- The corrected canonical candidate retains the entire original primitive fiber. -/
def generatedRootEightGeneratorCanonicalFiber (j : Fin 12) : localFiberSubgroup :=
  localFiberIncl (generatedRootEightGeneratorCorrection j) * generatedRootEightGeneratorPrimitiveFiber j

/-- The corresponding corrected canonical local word, with correction on the left. -/
def generatedRootEightGeneratorCanonicalLocal (j : Fin 12) : H :=
  inclQ (generatedRootEightGeneratorCorrection j) * generatedRootEightGeneratorPrimitiveLocal j

/-- The full corrected canonical fiber represents precisely its original local candidate. -/
theorem generatedRootEight_generator_canonical_fiber_local (j : Fin 12) :
    localFiberIntoH (generatedRootEightGeneratorCanonicalFiber j) =
      generatedRootEightGeneratorCanonicalLocal j := by
  rfl

/-- Each complete candidate is transported back to the original root-eight axis coordinates. -/
def generatedRootEightGeneratorFiber (j : Fin 12) : localFiberSubgroup :=
  generatedRootEightCanonicalFiber⁻¹ * generatedRootEightGeneratorCanonicalFiber j *
    generatedRootEightCanonicalFiber

/-- Twelve actual original H candidates; their whole-axis fixation remains a separate proof. -/
def generatedRootEightGeneratorCandidate (j : Fin 12) : H :=
  generatedFifthRootEightCanonicalLocal⁻¹ * generatedRootEightGeneratorCanonicalLocal j *
    generatedFifthRootEightCanonicalLocal

/-- The transported full fibers represent exactly the actual original H candidates. -/
theorem generatedRootEight_generator_fiber_local (j : Fin 12) :
    localFiberIntoH (generatedRootEightGeneratorFiber j) = generatedRootEightGeneratorCandidate j := by
  simp only [generatedRootEightGeneratorFiber, map_mul, map_inv,
    generatedRootEight_canonical_fiber_local, generatedRootEight_generator_canonical_fiber_local,
    generatedRootEightGeneratorCandidate]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
