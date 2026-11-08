/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Distribution.Distribution

@[expose] public section

open LineDeriv TopologicalSpace
open scoped Distributions

namespace MathlibExt.Analysis.Distribution.DistributionFderivWanted

/--
Full (Fréchet) derivative of a distribution: directional derivatives assemble into a continuous
linear map `D : 𝓓'(Ω, F) →L[ℝ] (E →L[ℝ] 𝓓'(Ω, F))` with `D T v = ∂_{v} T`.
(Directional derivatives alone already exist as `Distribution.lineDerivCLM`.)

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Distributions on R^d" / entry "derivative of a distribution";
L. Schwartz, *Théorie des distributions*, Ch. II.
-/
public theorem_wanted exists_fderiv_distribution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] :
    ∃ D : 𝓓'(Ω, F) →L[ℝ] (E →L[ℝ] 𝓓'(Ω, F)), ∀ T v, D T v = ∂_{v} T

end MathlibExt.Analysis.Distribution.DistributionFderivWanted
