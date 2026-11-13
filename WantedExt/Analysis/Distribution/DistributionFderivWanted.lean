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
**The full derivative of a distribution.** Let $E$ be a real normed space, $\Omega \subseteq E$
an open set and $F$ a real topological vector space, and let $\mathcal{D}'(\Omega, F)$ be the
space of $F$-valued distributions on $\Omega$ (continuous linear maps from the real-valued test
functions on $\Omega$ to $F$), with the topology of uniform convergence on compact sets of test
functions. For $v \in E$ and $T \in \mathcal{D}'(\Omega, F)$, let $\partial_v T$ be the
directional derivative $\varphi \mapsto -T(\partial_v \varphi)$. Then there is a continuous
linear map $D$ from $\mathcal{D}'(\Omega, F)$ to the space of continuous linear maps
$E \to \mathcal{D}'(\Omega, F)$ (with the topology of uniform convergence on bounded sets) such
that $D(T)(v) = \partial_v T$ for every $T \in \mathcal{D}'(\Omega, F)$ and every $v \in E$.

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
