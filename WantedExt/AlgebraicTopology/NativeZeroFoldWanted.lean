/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeSZeroFoldModels

/-!
# Full native zero-fold evaluation comparison

Source: BGT arXiv:1001.2282v4, Definition 7.5, page 45. This is the
actual evaluation on every enriched empty-product diagram simplex.
The object core is not identified with the Grothendieck group.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeSZeroFoldModels

open StableInfinityCategoryModels

universe u

/-- Evaluate the full zero-fold construction on its actual unique source object. -/
def_wanted native_zero_fold_evaluation (C : StableInfinityCategory.{u}) :
  ZeroFoldEvaluationComparison C

end MathlibExt.AlgebraicTopology.NativeSZeroFoldModels
