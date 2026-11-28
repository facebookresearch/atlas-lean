/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SchatunowskyImaginaryQuadraticExistsQuadPrimeNormPowLtQuadPrimorialNorm
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Norm.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Data.Nat.Nth
import MathlibExt.NumberTheory.Schatunowsky

/-! # Tests for prime norm powers falling below the quadratic primorial -/

namespace MathlibExtTest.NumberTheory.SchatunowskyImaginaryQuadraticExistsQuadPrimeNormPowLtQuadPrimorialNorm

open NumberField MetaMathlibExt

-- Squares of prime norms eventually fall below the primorial norm.
example {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ 2 < quadPrimorialNorm K n := by
  simpa using exists_quadPrimeNorm_pow_lt_quadPrimorialNorm hK 1

-- Cubes of prime norms eventually fall below the primorial norm.
example {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ 3 < quadPrimorialNorm K n := by
  simpa using exists_quadPrimeNorm_pow_lt_quadPrimorialNorm hK 2

-- Prime norms are eventually bounded above by the primorial norm.
example {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ≤ quadPrimorialNorm K n := by
  obtain ⟨n₀, hn₀⟩ := exists_quadPrimeNorm_pow_lt_quadPrimorialNorm hK 0
  refine ⟨n₀, fun n hn => ?_⟩
  have h2 : quadPrimeNorm K (n + 1) < quadPrimorialNorm K n := by
    simpa using hn₀ n hn
  exact le_of_lt h2

-- Every Schatunowsky set of an imaginary quadratic field of class number one is finite.
example {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1)
    (ℓ : ℕ) :
    (quadSchatunowskySet K ℓ).Finite := by
  obtain ⟨n₀, hn₀⟩ := exists_quadPrimeNorm_pow_lt_quadPrimorialNorm hK ℓ
  exact (quadSchatunowskySet_norm_bound_and_finite hK hK1 ℓ n₀ hn₀).2

end SchatunowskyImaginaryQuadraticExistsQuadPrimeNormPowLtQuadPrimorialNorm
