/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCertificate
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddShortPacket

/-! Three actual phase-preserving local comparison words and their complete extraspecial actions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original source roots used in the three local comparison words. -/
def generatedAxisGlobalOddComparisonRoot : Fin 3 → Fin 9 := ![0, 0, 6]

/-- Original source Golay signs, with no altered spin or source phase convention. -/
def generatedAxisGlobalOddComparisonSign : Fin 3 → Fin 4096 := ![52, 6, 4]

/-- Genuine positive extraspecial corrections in the fixed original hyperbolic coordinates. -/
def generatedAxisGlobalOddComparisonQ (k : Fin 3) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode (![3276850, 15892480, 8388608] k)), 1⟩

/-- The complete actual local fiber word, including its full extraspecial phase correction. -/
def generatedAxisGlobalOddComparisonFiber (k : Fin 3) : localFiberSubgroup :=
  localFiberIncl (generatedAxisGlobalOddComparisonQ k) *
    generatedFifthSignFiber (generatedAxisGlobalOddComparisonSign k) 0 *
      generatedAxisGlobalOddSourceRootFiber (generatedAxisGlobalOddComparisonRoot k)

/-- The corresponding literal actual local group word. -/
def generatedAxisGlobalOddComparisonLocal (k : Fin 3) : H :=
  inclQ (generatedAxisGlobalOddComparisonQ k) *
    generatedFifthSignLocal (generatedAxisGlobalOddComparisonSign k) 0 *
      generatedAxisGlobalOddSourceRootLocalWord (generatedAxisGlobalOddComparisonRoot k)

/-- The full fiber projects to precisely the stated actual local group word. -/
theorem generatedAxisGlobalOddComparisonFiber_local (k : Fin 3) :
    localFiberIntoH (generatedAxisGlobalOddComparisonFiber k) =
      generatedAxisGlobalOddComparisonLocal k := by
  rw [generatedAxisGlobalOddComparisonFiber, map_mul, map_mul,
    generatedFifth_sign_fiber_local, generatedAxisGlobalOddSourceRootFiber_local]
  rfl

/-- The original complete finite extraspecial action, retaining all central correction terms. -/
def generatedAxisGlobalOddComparisonQImage (k : Fin 3) (q : Q) : Q :=
  let r := generatedAxisGlobalSignFullImage (generatedAxisGlobalOddComparisonSign k)
    (generatedAxisGlobalOddRootQFast (generatedAxisGlobalOddComparisonRoot k) q)
  generatedAxisGlobalOddComparisonQ k * r * (generatedAxisGlobalOddComparisonQ k)⁻¹

/-- Every full extraspecial image equals genuine conjugation by the original local comparison. -/
theorem generatedAxisGlobalOddComparisonQImage_actual (k : Fin 3) (q : Q) :
    spinConjugation (generatedAxisGlobalOddComparisonFiber k).val.1 q =
      generatedAxisGlobalOddComparisonQImage k q := by
  change spinConjugation
    (spinHolomorphIncl (generatedAxisGlobalOddComparisonQ k) *
      (generatedFifthSignFiber (generatedAxisGlobalOddComparisonSign k) 0).val.1 *
        (generatedAxisGlobalOddSourceRootFiber (generatedAxisGlobalOddComparisonRoot k)).val.1)
      q = _
  rw [map_mul, map_mul]
  change spinConjugation (spinHolomorphIncl (generatedAxisGlobalOddComparisonQ k))
    (spinConjugation (generatedFifthSignFiber (generatedAxisGlobalOddComparisonSign k) 0).val.1
      (spinConjugation
        (generatedAxisGlobalOddSourceRootFiber (generatedAxisGlobalOddComparisonRoot k)).val.1
        q)) = _
  rw [spinConjugation_incl, generatedAxisGlobalSignFull_QImage,
    generatedAxisGlobalOddRootQFast_all_actual]
  rfl

/-- A full preferred-Q certificate gives the entire genuine short-unit image. -/
theorem generatedAxisGlobalOddComparison_short_basis (k : Fin 3)
    (r s : GriessShortIndex) (c : ZMod 2)
    (hc : generatedAxisGlobalOddComparisonQImage k (griessShortQ r) =
      qCentral c * griessShortQ s) :
    localShortOperator (generatedAxisGlobalOddComparisonFiber k) (Pi.single r 1) =
      qSign c • Pi.single s (1 : ℝ) := by
  apply monsterNortonShortBasis_of_Q_image
  rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq,
    generatedAxisGlobalOddComparisonQImage_actual]
  exact hc

/-- Complete preferred-Q data determine every real short coordinate of the actual comparison. -/
theorem generatedAxisGlobalOddComparison_short_transport (k : Fin 3)
    (s : GeneratedAxisGlobalOddShortPacketIndex → GriessShortIndex)
    (p : GeneratedAxisGlobalOddShortPacketIndex → ZMod 2)
    (hc : ∀ i, generatedAxisGlobalOddComparisonQImage k
        (griessShortQ (generatedAxisGlobalOddShortPacketLabel i)) =
      qCentral (p i) * griessShortQ (s i)) :
    localShortOperator (generatedAxisGlobalOddComparisonFiber k)
        ((griessConwayEncode generatedOddAxis).2.1) =
      ∑ i, (generatedAxisGlobalOddShortPacketCoefficient i * qSign (p i)) •
        Pi.single (s i) (1 : ℝ) := by
  rw [← generatedAxisGlobalOddShortPacket_eq, generatedAxisGlobalOddShortPacket, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, generatedAxisGlobalOddComparison_short_basis k _ _ _ (hc i), smul_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
