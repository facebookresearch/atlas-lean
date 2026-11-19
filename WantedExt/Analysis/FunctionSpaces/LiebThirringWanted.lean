/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The Lieb–Thirring kinetic energy inequality (wanted)

Lieb and Thirring (1975) proved a Sobolev inequality for orthonormal functions: there is a
constant `K_d > 0` such that for every `N` and all `u_1, …, u_N ∈ H¹(ℝ^d)` orthonormal in
`L²(ℝ^d)`,
`∑_n ∫ |∇u_n|² ≥ K_d ∫ (∑_n |u_n|²)^{1 + 2/d}`,
with `K_d` independent of `N` (E. H. Lieb and W. Thirring, *Bound on kinetic energy of
fermions which proves stability of matter*, Phys. Rev. Lett. 35 (1975) 687–689; as stated in
R. L. Frank, *The Lieb–Thirring inequalities: recent results and open problems*,
arXiv:2007.09326v1 (preprint dated July 17, 2020), Theorem 1, equation (1)). The point is that
`K_d` does not depend on `N`: without orthonormality the constant would decay like `N^{-2/d}`.
With `d = 3` it is the kinetic energy bound in Lieb and Thirring's proof of the stability of
matter.

The wanted statement below is restricted to smooth compactly supported functions, so it is
weaker than Frank's Theorem 1, which allows all of `H¹(ℝ^d)` (by density the two are
equivalent, but that is not formalized here). The constant convention is Frank's: kinetic energy
`∫ |∇u|²` with no factor `ħ²/2m`, spinless functions, and density `ρ = ∑ |u_n|²`. The proof is
deferred.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace MathlibExt.Analysis.FunctionSpaces.LiebThirringWanted

/-- **Lieb–Thirring kinetic energy inequality.** For every dimension `d ≥ 1` there is a constant
`K > 0` such that for every `N` and every family `u_1, …, u_N` of smooth compactly supported
complex functions on `ℝ^d` that is orthonormal in `L²(ℝ^d)`,
`K ∫ (∑_n |u_n|²)^{1 + 2/d} ≤ ∑_n ∫ |∇u_n|²`, where `|∇u|² = ∑_k |∂_k u|²`
(R. L. Frank, *The Lieb–Thirring inequalities: recent results and open problems*,
arXiv:2007.09326v1, July 17, 2020 preprint, Theorem 1; E. H. Lieb and W. Thirring, Phys. Rev.
Lett. 35 (1975) 687–689). This is Frank's Theorem 1 restricted from `H¹(ℝ^d)` to smooth compactly
supported functions, hence a weaker statement. -/
theorem_wanted lieb_thirring_kinetic (d : ℕ) (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (u : Fin N → EuclideanSpace ℝ (Fin d) → ℂ),
      (∀ i, ContDiff ℝ ∞ (u i)) → (∀ i, HasCompactSupport (u i)) →
      (∀ i j, ∫ x, star (u i x) * u j x = if i = j then 1 else 0) →
      K * ∫ x, (∑ i, ‖u i x‖ ^ 2) ^ (1 + 2 / (d : ℝ)) ≤
        ∑ i, ∫ x, ∑ k, ‖fderiv ℝ (u i) x (EuclideanSpace.single k 1)‖ ^ 2

end MathlibExt.Analysis.FunctionSpaces.LiebThirringWanted
