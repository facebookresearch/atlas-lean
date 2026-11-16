/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.MotivicCohomologyProducts
import MathlibExt.AlgebraicGeometry.MotivicAffineQuotientModels
import MathlibExt.AlgebraicGeometry.MotivicCofiberComparisons
import MathlibExt.AlgebraicGeometry.GeneralEtaleDerivedEnhancements

/-!
# The two signed (1,1) shuffles

These boundary probes fix the standard Eilenberg--Zilber convention:
the identity shuffle has first/back degeneracies σ₁,σ₀ and sign +1,
while the swapped shuffle has σ₀,σ₁ and sign -1. They detect a reversed
block map or lost integral shuffle sign before Tate shift transport.
-/

open CategoryTheory
open MathlibExt.AlgebraicGeometry.MotivicCycleProducts
open scoped Simplicial

private def identityShuffle : Shuffle 1 1 :=
  ⟨Equiv.refl _, by constructor <;> intro i j h <;> omega⟩

private def transpositionShuffle : Shuffle 1 1 :=
  ⟨Equiv.swap (0 : Fin 2) 1, by constructor <;> intro i j h <;> omega⟩

example : (shuffleFirst identityShuffle).toOrderHom (1 : Fin 3) = (1 : Fin 2) := by decide
example : (shuffleSecond identityShuffle).toOrderHom (1 : Fin 3) = (0 : Fin 2) := by decide
example : (shuffleFirst transpositionShuffle).toOrderHom (1 : Fin 3) = (0 : Fin 2) := by decide
example : (shuffleSecond transpositionShuffle).toOrderHom (1 : Fin 3) = (1 : Fin 2) := by decide

example : ((Equiv.Perm.sign identityShuffle.val : ℤˣ) : ℤ) = 1 := by simp [identityShuffle]
example : ((Equiv.Perm.sign transpositionShuffle.val : ℤˣ) : ℤ) = -1 := by
  simp [transpositionShuffle]

#print axioms MathlibExt.AlgebraicGeometry.MotivicCohomologyProducts.normalizedAlexanderWhitney
#print axioms MathlibExt.AlgebraicGeometry.MotivicCohomologyProducts.externalCup
#print axioms MathlibExt.AlgebraicGeometry.MotivicCofiberComparisons.boundary
#print axioms MathlibExt.AlgebraicGeometry.MotivicAffineQuotientModels.affineK
#print axioms MathlibExt.AlgebraicGeometry.GeneralEtaleDerivedEnhancements.coefficientDG
#print axioms MathlibExt.AlgebraicGeometry.GeneralEtaleDerivedEnhancements.amplitudeNerve
