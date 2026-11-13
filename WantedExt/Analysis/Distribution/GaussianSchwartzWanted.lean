/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

@[expose] public section

open scoped SchwartzMap

namespace MathlibExt.Analysis.Distribution.GaussianSchwartzWanted

/--
**The Gaussian is a Schwartz function.** Let $E$ be a finite-dimensional real inner product
space. Then there is a real-valued Schwartz function $g$ on $E$ such that
$g(x) = e^{-\|x\|^2}$ for every $x \in E$.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Spaces S(R^d)" / entry "Gaussian functions";
<https://en.wikipedia.org/wiki/Schwartz_space>.
-/
public theorem_wanted gaussian_mem_schwartz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ g : 𝓢(E, ℝ), ∀ x, g x = Real.exp (-‖x‖ ^ 2)

end MathlibExt.Analysis.Distribution.GaussianSchwartzWanted
