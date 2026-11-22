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
Fundamental solution of the Laplacian in dimension three: the equation `Δ N = δ₀` is solvable
in tempered distributions.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Applications" / entry "fundamental solution of the Laplacian";
L. Evans, *Partial Differential Equations*, §2.2.
-/
public theorem_wanted exists_fundamental_solution_laplacian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) :
    ∃ N : 𝓢'(E, ℂ), Δ N = TemperedDistribution.delta (0 : E)

/--
The Newton potential `-1/(4π‖y‖)` is harmonic away from the origin in dimension three.

Sources: Mathlib `docs/undergrad.yaml`, section "Distribution calculus" /
"Applications" / entry "fundamental solution of the Laplacian";
L. Evans, *Partial Differential Equations*, §2.2.
-/
public theorem_wanted newton_potential_harmonic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) (x : E) (hx : x ≠ 0) :
    (Δ (fun (y : E) => (-((4 * Real.pi * ‖y‖))⁻¹ : ℝ)) : E → ℝ) x = 0

end MathlibExt.Analysis.Distribution.NewtonPotentialWanted
