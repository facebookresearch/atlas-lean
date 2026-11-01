/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Two actual monomial prefix coordinates for each of the five odd source inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsOddInverseSpinPrefix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFirstUData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The original five source basis indices with odd actual first-U images. -/
def monsterNortonOddPrefixBasisIndex : Fin 5 → Fin 23 := ![10, 13, 14, 15, 22]

/-- The two genuine original source labels after the complete monomial prefix. -/
def monsterNortonOddPrefixLabel : Fin 5 → Fin 2 → Fin 4096 :=
  ![![2057, 3747], ![2739, 3097], ![698, 1040], ![692, 1054], ![681, 1027]]

/-- The exact two signed integer coefficients before the inverse Gaussian. -/
def monsterNortonOddPrefixCoefficient : Fin 5 → Fin 2 → ℤ :=
  ![![1, 1], ![1, 1], ![1, 1], ![-1, -1], ![-1, 1]]

/-- The two source coordinates remain distinct after the actual monomial transport. -/
theorem monsterNortonOddPrefixLabel_injective (k : Fin 5) :
    Function.Injective (monsterNortonOddPrefixLabel k) := by
  intro i j h
  have hc : ∀ k : Fin 5, ∀ i j : Fin 2,
      monsterNortonOddPrefixLabel k i = monsterNortonOddPrefixLabel k j → i = j := by
    decide +kernel
  exact hc k i j h

/-- The two integer coefficients retain square one. -/
theorem monsterNortonOddPrefixCoefficient_sq (k : Fin 5) (i : Fin 2) :
    monsterNortonOddPrefixCoefficient k i ^ 2 = 1 := by
  revert k i
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Check every actual two-coordinate prefix value before the expensive Gaussian sum.
/-- Both supported values are calculated by the full actual monomial prefix. -/
theorem monsterNortonOddPrefix_coefficient (k : Fin 5) (i : Fin 2) :
    monsterNortonOddInverseSpinPrefix
      (monsterNortonEvenShortFirstUOddCode (monsterNortonOddPrefixBasisIndex k))
      (monsterNortonOddPrefixLabel k i) = monsterNortonOddPrefixCoefficient k i := by
  revert k i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
