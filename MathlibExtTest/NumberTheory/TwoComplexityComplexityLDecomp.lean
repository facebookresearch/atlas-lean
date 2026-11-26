/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoComplexityComplexityLDecomp
import MathlibExt.NumberTheory.TwoComplexityMax

/-! # Tests for adding a small multiple to a multiple of the square -/

namespace MathlibExtTest.NumberTheory.TwoComplexityComplexityLDecomp

open MathlibExt.NumberTheory.TwoComplexityWanted

example : complexityL 3 15 = 4 := by
  have hbuild : CanBuild 3 2 9 := CanBuild.base.mul CanBuild.base
  have hspec := complexityL_spec ⟨2, hbuild⟩
  have hle := complexityL_min_le hbuild
  have hpos := hspec.one_le
  have hbound := (canBuild_max 3 (complexityL 3 9) (by decide) hpos).2 9 hspec
  have hcomplexity : complexityL 3 9 = 2 := by
    by_contra h
    have he : complexityL 3 9 = 1 := by omega
    norm_num [he] at hbound
  simpa only [hcomplexity] using
    complexityL_decomp 3 15 9 2 (by decide) rfl (by decide) (by decide) (by decide)

end MathlibExtTest.NumberTheory.TwoComplexityComplexityLDecomp
