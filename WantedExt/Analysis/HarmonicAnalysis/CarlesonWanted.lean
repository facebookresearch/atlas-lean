/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Fourier.Fejer

/-!
# Carleson's theorem (statement)

Almost-everywhere convergence of the symmetric Fourier partial sums of a square-integrable
2π-periodic function, stated with the partial sums `fourierPartialSum` of
`MathlibExt.Analysis.Fourier.Fejer`.
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Analysis.HarmonicAnalysis.CarlesonWanted

open MathlibExt.Analysis.FourierConvergenceWanted.Analysis

/-- **Carleson's theorem.** For every 2π-periodic `f : ℝ → ℂ` that is square-integrable on
`(0, 2π]`, the symmetric Fourier partial sums `S_N(f)(x)` converge to `f(x)` for almost every
`x ∈ ℝ` (L. Carleson, *On convergence and growth of partial sums of Fourier series*, Acta Math.
116 (1966), 135–157, as described in L. Becker et al., *Formalizing Carleson's theorem in
Lean*, arXiv:2609.31334v1, §1.1; Theorem 2.2.1 there, formalized in Lean, is the case of
continuous `f`). -/
public theorem_wanted carleson_ae_tendsto
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi))
    (_hL2 : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi)))) :
    ∀ᵐ x, Tendsto (fun N : ℕ => fourierPartialSum f N x) atTop (𝓝 (f x))

end MathlibExt.Analysis.HarmonicAnalysis.CarlesonWanted
