/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ScottishBook136

open MathlibExt.Topology.ScottishBook136Wanted

-- Check the exact dimensions via Mathlib's dimension function and that the
-- resulting open surjection cannot be injective.
example :
    ∃ (X Y : Type) (_ : TopologicalSpace X) (_ : TopologicalSpace Y) (_ : CompactSpace X)
      (_ : CompactSpace Y) (_ : TopologicalSpace.MetrizableSpace X)
      (_ : TopologicalSpace.MetrizableSpace Y),
      smallInductiveDimension X = 1 ∧ smallInductiveDimension Y = 2 ∧
        ∃ f : X → Y, Continuous f ∧ IsOpenMap f ∧ Function.Surjective f ∧
          ¬ Function.Injective f := by
  obtain ⟨X, Y, tX, tY, cX, cY, mX, mY, hX, hX₀, hY, hY₁, f, hc, ho, hs⟩ :=
    kolmogorovInteriorMapRaisesDimension
  refine ⟨X, Y, tX, tY, cX, cY, mX, mY, smallInductiveDimension_eq 1 hX hX₀,
    smallInductiveDimension_eq 2 hY hY₁, f, hc, ho, hs, ?_⟩
  intro hi
  let e := (Equiv.ofBijective f ⟨hi, hs⟩).toHomeomorphOfContinuousOpen hc ho
  exact hY₁ ((e.hasSmallInductiveDimensionLE 1).mp hX)
