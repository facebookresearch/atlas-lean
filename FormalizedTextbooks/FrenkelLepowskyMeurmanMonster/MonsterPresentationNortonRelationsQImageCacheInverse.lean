/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact compact inverse of the actual Norton Q action, with every central phase. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQImageCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIntegralAction

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Binary inverse images of the twenty-four coordinate lifts. -/
def monsterNortonUQInverseGeneratorMasks : Fin 24 → ℕ :=
  ![0xd5d00c, 0x3f10f0, 0x7ff3c0, 0x7fe330, 0x10a0, 0x40e220,
    0x1050, 0x40f140, 0xc, 0x40080a, 0xbfd000, 0x40000c,
    0x3f0, 0xf0952, 0x3c0153, 0x33015d, 0x110801, 0x5000e,
    0x28080f, 0xa000e, 0x80b40e, 0xc000, 0x400bf0, 0xbf17fe]

/-- Central corrections of those inverse images, retained from the full forward action. -/
def monsterNortonUQInverseGeneratorPhases : Fin 24 → ZMod 2 :=
  ![0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
    0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

/-- The fully signed inverse generator images. -/
def monsterNortonUQInverseGeneratorImage (i : Fin 24) : Q :=
  ⟨ofAdd (fun j => if (monsterNortonUQInverseGeneratorMasks i).testBit j.val then 1 else 0),
    ofAdd (monsterNortonUQInverseGeneratorPhases i)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 16000000 in
-- Check all inverse binary vectors and central signs with the already proved actual forward cache.
/-- Every inverse image maps to the actual positive coordinate generator, including its phase. -/
theorem monsterNortonUQInverseGeneratorImage_certificate (i : Fin 24) :
    monsterNortonUQFastImage (monsterNortonUQInverseGeneratorImage i) = qCoordinateGenerator i := by
  apply NormalizedCocycleExtension.Extension.ext
  · apply toAdd.injective
    change (fun j : Fin 24 =>
      toAdd (monsterNortonUQFastImage (monsterNortonUQInverseGeneratorImage i)).base j) =
        (fun j : Fin 24 => toAdd (qCoordinateGenerator i).base j)
    fin_cases i <;> decide +kernel
  · apply toAdd.injective
    change toAdd (monsterNortonUQFastImage (monsterNortonUQInverseGeneratorImage i)).coeff =
      (0 : ZMod 2)
    fin_cases i <;> decide +kernel

/-- The compact fully signed inverse evaluator. -/
def monsterNortonUQInverseFastImage (q : Q) : Q :=
  monsterNortonCoordinateEvaluation monsterNortonUQInverseGeneratorImage q

/-- Genuine inverse Norton spin conjugation agrees on every actual Q input. -/
theorem monsterNortonUQInverseFastImage_eq (q : Q) :
    spinConjugation (monsterNortonUFiber⁻¹).val.1 q = monsterNortonUQInverseFastImage q := by
  apply monsterNortonCoordinateEvaluation_eq
  intro i
  change spinConjugation (monsterNortonUFiber.val.1⁻¹) (qCoordinateGenerator i) = _
  have hc : spinConjugation monsterNortonUFiber.val.1
      (monsterNortonUQInverseGeneratorImage i) = qCoordinateGenerator i := by
    rw [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq]
    exact monsterNortonUQInverseGeneratorImage_certificate i
  have hm : spinConjugation monsterNortonUFiber.val.1 *
      spinConjugation (monsterNortonUFiber.val.1⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hx := congrArg (fun e : Q ≃* Q => e (qCoordinateGenerator i)) hm
  change spinConjugation monsterNortonUFiber.val.1
    (spinConjugation (monsterNortonUFiber.val.1⁻¹) (qCoordinateGenerator i)) =
      qCoordinateGenerator i at hx
  apply (spinConjugation monsterNortonUFiber.val.1).injective
  exact hx.trans hc.symm

/-- The actual positive short phase is now computed by the compact checked cache. -/
theorem monsterNortonUQFastImage_short_phase (z : Fin 24 → ℤ) :
    monsterNortonIntegralShortPhase monsterNortonUFiber z =
      toAdd (monsterNortonUQFastImage (monsterNortonCoordinateQ z)).coeff := by
  unfold monsterNortonIntegralShortPhase
  rw [monsterNortonUQImage_eq, monsterNortonUQFastImage_eq]

/-- The actual inverse short phase is computed by the full signed inverse cache. -/
theorem monsterNortonUQInverseFastImage_short_phase (z : Fin 24 → ℤ) :
    monsterNortonIntegralShortPhase (monsterNortonUFiber⁻¹) z =
      toAdd (monsterNortonUQInverseFastImage (monsterNortonCoordinateQ z)).coeff := by
  unfold monsterNortonIntegralShortPhase
  rw [monsterNortonUQInverseFastImage_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
