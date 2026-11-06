/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Q conjugation certificates for powers of the complete local Norton u word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonLocalWord

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual local fiber conjugates embedded Q by its proved spin normalizer. -/
theorem monsterFiberGenerated_conjugate_Q (f : localFiberSubgroup) (q : Q) :
    localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f) * qIntoGenerated q *
      (localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f))⁻¹ =
        qIntoGenerated (spinConjugation f.val.1 q) := by
  have h := localFiberIncl_conjugate f q
  have hq := congrArg (QuotientGroup.mk' localDiagonalSubgroup) h
  rw [map_mul, map_mul, map_inv] at hq
  have hg := congrArg localIntoGenerated hq
  rw [map_mul, map_mul, map_inv] at hg
  exact hg.symm

/-- Every integer power of the genuine fiber represents the corresponding actual Norton power. -/
theorem monsterNortonUFiber_generated_zpow (j : ℤ) :
    localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup (monsterNortonUFiber ^ j)) =
      y555NortonActualU ^ j := by
  rw [map_zpow, map_zpow]
  exact congrArg (fun u : ↥G => u ^ j) monsterNortonULocal_generated

/-- Conjugation by any actual Norton power has its complete central-corrected Q image. -/
theorem monsterNortonActualU_conjugate_Q_zpow (j : ℤ) (q : Q) :
    y555NortonActualU ^ j * qIntoGenerated q * (y555NortonActualU ^ j)⁻¹ =
      qIntoGenerated (spinConjugation (monsterNortonUFiber ^ j).val.1 q) := by
  have h := monsterFiberGenerated_conjugate_Q (monsterNortonUFiber ^ j) q
  rw [monsterNortonUFiber_generated_zpow] at h
  exact h

/-- Actual Q lifts for the six point parameters conjugated by any Norton power. -/
noncomputable def monsterNortonPointOrbitQ (j : ℤ) (i : Fin 6) : Q :=
  spinConjugation (monsterNortonUFiber ^ j).val.1 (y555NortonPointQ i)

/-- These orbit lifts are exactly the conjugated points in the named group G. -/
theorem monsterNortonPointOrbitQ_generated (j : ℤ) (i : Fin 6) :
    qIntoGenerated (monsterNortonPointOrbitQ j i) =
      y555NortonActualU ^ j * y555NortonPoint i * (y555NortonActualU ^ j)⁻¹ :=
  (monsterNortonActualU_conjugate_Q_zpow j (y555NortonPointQ i)).symm

/-- The actual point orbit retains the six involution relations in Q. -/
theorem monsterNortonPointOrbitQ_square (j : ℤ) (i : Fin 6) :
    monsterNortonPointOrbitQ j i ^ 2 = 1 := by
  change spinConjugation (monsterNortonUFiber ^ j).val.1 (y555NortonPointQ i) ^ 2 = 1
  rw [← map_pow, y555NortonPointQ_sq, map_one]

/-- Each conjugated six-point family still commutes in the actual extraspecial group. -/
theorem monsterNortonPointOrbitQ_commute (j : ℤ) (i k : Fin 6) :
    monsterNortonPointOrbitQ j i * monsterNortonPointOrbitQ j k =
      monsterNortonPointOrbitQ j k * monsterNortonPointOrbitQ j i := by
  change spinConjugation (monsterNortonUFiber ^ j).val.1 (y555NortonPointQ i) *
      spinConjugation (monsterNortonUFiber ^ j).val.1 (y555NortonPointQ k) =
    spinConjugation (monsterNortonUFiber ^ j).val.1 (y555NortonPointQ k) *
      spinConjugation (monsterNortonUFiber ^ j).val.1 (y555NortonPointQ i)
  rw [← map_mul, ← map_mul, y555NortonPointQ_commute]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
