/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Local connectivity of real quadratic Julia sets (Milnor)

Milnor, Problems in holomorphic dynamics (Stony Brook, 1992), problems on local connectivity,
Problem 13: for every real `c ∈ [-2, 1/4]`, is the Julia set of `f_c(z) = z² + c` locally connected?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import WantedExt.Dynamics.NowhereDenseJuliaSetPositiveAreaAMR52Problem0041Wanted

@[expose] public section

namespace MathlibExt.Dynamics.RealQuadraticJuliaLocallyConnectedAMR52Problem0038Wanted

/-!
Source: J. Milnor (ed.), Problems in holomorphic dynamics (Stony Brook, 1992), arXiv:math/9205209,
Problems on local connectivity, Problem 13,
https://www.math.stonybrook.edu/open-problems-dynamical-systems. UnsolvedMath record UM-05300038
(`AMR-052-0038`), dataset ulamai/UnsolvedMath v1.8.0.

The Julia set of `z ↦ z² + c` is the boundary of the filled Julia set (points with bounded orbit),
`juliaSet` of the module for `AMR-052-0041`, reused here; local connectivity is
`LocallyConnectedSpace` of the subspace.
-/

open MathlibExt.Dynamics.NowhereDenseJuliaSetPositiveAreaAMR52Problem0041Wanted (juliaSet)

/-- Milnor's question, with a positive answer: for every real `c ∈ [-2, 1/4]` the Julia set of
`z ↦ z ^ 2 + c` is locally connected. -/
def realQuadraticJuliaSetsLocallyConnected : Prop :=
  ∀ c : ℝ, c ∈ Set.Icc (-2 : ℝ) (1 / 4) → LocallyConnectedSpace (juliaSet (c : ℂ))

/--
Resolved true: Levin and van Strien prove that the Julia set of `z² + c` is locally connected for
every real `c ∈ [-2, 1/4]` (and totally disconnected for the other real `c`). Source: J. Milnor
(ed.), Problems in holomorphic dynamics (Stony Brook, 1992), arXiv:math/9205209, Problems on local
connectivity, Problem 13, https://www.math.stonybrook.edu/open-problems-dynamical-systems;
resolution: G. Levin and S. van Strien, Local connectivity of the Julia set of real polynomials,
Ann. of Math. (2) 147 (1998); arXiv:math/9504227, Main Theorem (abstract): for z^d + c with d even
and c real the Julia set is either totally disconnected or locally connected; 'In particular, the
Julia set of z² + c is locally connected if c ∈ [-2, 1/4] and totally disconnected otherwise',
https://doi.org/10.2307/120958.
-/
public theorem_wanted realQuadraticJuliaSetsLocallyConnected_holds :
    realQuadraticJuliaSetsLocallyConnected

end MathlibExt.Dynamics.RealQuadraticJuliaLocallyConnectedAMR52Problem0038Wanted
