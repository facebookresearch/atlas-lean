/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.FinitelyForcibleGraphons

namespace MathlibExtTest.Combinatorics.FinitelyForcibleGraphons

open MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted (IsGraphon)

-- Constant kernels are graphons precisely for constants in the closed unit interval.
example (p : ℝ) : IsGraphon (fun _ _ => p) ↔ p ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨fun h => h.2.2 0 0, fun hp => ⟨measurable_const, fun _ _ => rfl, fun _ _ => hp⟩⟩

end MathlibExtTest.Combinatorics.FinitelyForcibleGraphons
