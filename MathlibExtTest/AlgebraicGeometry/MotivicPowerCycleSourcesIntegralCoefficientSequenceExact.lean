/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicPowerCycleSourcesIntegralCoefficientSequenceExact

/-!
# Integral coefficient sequence exactness probes

The integral coefficient sequence at `2` is short exact, and exactness of the
integral coefficient sequence follows at any prime.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.MotivicPowerCycleSourcesIntegralCoefficientSequenceExact

open MathlibExt.AlgebraicGeometry.MotivicBocksteinModels
open WantedExt.AlgebraicGeometry.MotivicPowerCycleSourcesWanted

example : (integralSequence 2).ShortExact :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  integralCoefficientSequenceExact 2

example (ell : ℕ) [Fact ell.Prime] : (integralSequence ell).Exact :=
  (integralCoefficientSequenceExact ell).exact

end MathlibExtTest.AlgebraicGeometry.MotivicPowerCycleSourcesIntegralCoefficientSequenceExact
