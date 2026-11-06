/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original-source word images after the complete kernel-checked prefix certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCCacheBounds
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3TCCacheSourceProofs

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The actual source word of the checked base prefix is one. -/
theorem y322Orthogonal3TCCacheSource_zero : y322Orthogonal3TCCacheSource 0 = 1 :=
  y322Orthogonal3TCCacheSource_zero_of_checked y322Orthogonal3TCCache_checked

/-- Each checked prefix is literally its actual original source parent times its generator. -/
theorem y322Orthogonal3TCCacheSource_step (i : Fin 7253) (hi : i.val ≠ 0) :
    y322Orthogonal3TCCacheSource i =
      y322Orthogonal3TCCacheSource (y322Orthogonal3TCCacheParent i) *
        PresentedGroup.of (y322Orthogonal3TCCacheGenerator i) :=
  y322Orthogonal3TCCacheSource_step_of_checked y322Orthogonal3TCCache_checked i hi

/-- All literal prefix matrices and inverses are actual original source word images. -/
theorem y322Orthogonal3TCCacheSource_matrices (i : Fin 7253) :
    (y322Orthogonal3Hom (y322Orthogonal3TCCacheSource i)).val =
        y322Orthogonal3TCCacheMatrix i ∧
      ((y322Orthogonal3Hom (y322Orthogonal3TCCacheSource i))⁻¹).val =
        y322Orthogonal3TCCacheInverse i :=
  y322Orthogonal3TCCacheSource_matrices_of_checked y322Orthogonal3TCCache_checked i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
