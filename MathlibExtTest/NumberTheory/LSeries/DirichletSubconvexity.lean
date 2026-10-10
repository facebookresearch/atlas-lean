/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LSeries.DirichletSubconvexity

@[expose] public section

namespace MathlibExt.NumberTheory.DirichletSubconvexity

example {θ : ℝ} (hθ : IsDirichletSubconvexityExponent θ) :
    dirichletSubconvexityExponent ≤ (θ : EReal) :=
  dirichletSubconvexityExponent_le_of_admissible hθ

end MathlibExt.NumberTheory.DirichletSubconvexity
