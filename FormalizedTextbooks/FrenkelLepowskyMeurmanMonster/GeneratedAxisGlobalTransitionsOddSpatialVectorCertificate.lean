/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddSpatialVectorEvaluation

/-! Exact rational physical source-word direction certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxHeartbeats 80000000 in
-- Check all nine full physical 24-coordinate source-word directions over the rational field.
/-- Every candidate direction equals the complete signed original rational source product. -/
theorem generatedAxisGlobalOddSpatialRootVectorQ_certificate : ∀ k : Fin 9,
    generatedAxisGlobalOddSpatialVectorWordQ (generatedAxisGlobalOddSourceRootWords k)
        (Pi.single (0 : Fin 24) (1 : ℚ)) = generatedAxisGlobalOddSpatialRootVectorQ k := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
