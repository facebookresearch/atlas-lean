/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactorsCompletedPlaceNorm

/-!
# Completed place norm corollaries

The local factor norm and the completed norm are multiplicative, and the completed norm
vanishes at zero.

Source: Yuan--Zhang, arXiv:2105.13587v9, Sections 3.4 and 5.3.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.FiniteAdelicTensorFactorsCompletedPlaceNorm

open MathlibExt.AlgebraicGeometry.FiniteAdelicTensorFactors
open WantedExt.AlgebraicGeometry.FiniteAdelicTensorFactors

example (K E F : Type) [Field K] [Field E] [NormedField F] [CompleteSpace F]
    [Algebra K E] [Algebra K F] [FiniteDimensional K E]
    (D : Factorization K E F) (C : CompletionData D) (a b : E) :
    completedNorm D C (a * b) = completedNorm D C a * completedNorm D C b := by
  rw [← completedPlaceNorm K E F D C (a * b), ← completedPlaceNorm K E F D C a,
    ← completedPlaceNorm K E F D C b, map_mul, map_mul, norm_mul]

example (K E F : Type) [Field K] [Field E] [NormedField F] [CompleteSpace F]
    [Algebra K E] [Algebra K F] [FiniteDimensional K E]
    (D : Factorization K E F) (C : CompletionData D) : completedNorm D C 0 = 0 := by
  simpa using (completedPlaceNorm K E F D C 0).symm

example (K E F : Type) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [FiniteDimensional K E]
    (D : Factorization K E F) (a b : E) :
    factorNorm D (a * b) = factorNorm D a * factorNorm D b := by
  rw [← tensorNorm K E F D (a * b), ← tensorNorm K E F D a, ← tensorNorm K E F D b,
    map_mul, map_mul]

end MathlibExtTest.AlgebraicGeometry.FiniteAdelicTensorFactorsCompletedPlaceNorm
