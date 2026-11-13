/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.InnerProductSpace.Laplacian

@[expose] public section

open Laplacian
open scoped SchwartzMap

namespace MathlibExt.Analysis.Distribution.NewtonPotentialWanted

/--
**Fundamental solution of the Laplacian in dimension three.** Let $E$ be a real inner product
space of dimension $3$. Then there is a complex-valued tempered distribution $N$ on $E$ such that
$\Delta N = \delta_0$, where $\Delta$ is the Laplacian in the sense of distributions and
$\delta_0$ is the Dirac delta at the origin.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Applications" / entry "fundamental solution of the Laplacian";
L. Evans, *Partial Differential Equations*, §2.2.
-/
public theorem_wanted exists_fundamental_solution_laplacian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) :
    ∃ N : 𝓢'(E, ℂ), Δ N = TemperedDistribution.delta (0 : E)

/--
**The Newton potential is harmonic away from the origin.** Let $E$ be a real inner product space
of dimension $3$, and define $N : E \to \mathbb{R}$ by $N(y) = -1/(4\pi\|y\|)$ for $y \neq 0$ and
$N(0) = 0$. Then the Laplacian of $N$ vanishes at every point $x \neq 0$ of $E$.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Applications" / entry "fundamental solution of the Laplacian";
L. Evans, *Partial Differential Equations*, §2.2.
-/
public theorem_wanted newton_potential_harmonic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) (x : E) (hx : x ≠ 0) :
    (Δ (fun (y : E) => (-((4 * Real.pi * ‖y‖))⁻¹ : ℝ)) : E → ℝ) x = 0

end MathlibExt.Analysis.Distribution.NewtonPotentialWanted
