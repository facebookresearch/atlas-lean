/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Distribution.TemperedDistribution
public import MathlibExt.Analysis.Distribution.NewtonPotential

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

end MathlibExt.Analysis.Distribution.NewtonPotentialWanted
