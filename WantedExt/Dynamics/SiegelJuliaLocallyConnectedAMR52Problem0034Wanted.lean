/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Locally connected Julia sets of Siegel quadratic polynomials (Milnor, Problem 9)

Milnor, Problems on local connectivity (Stony Brook problem list, 1992), Problem 9: give any example
of a Siegel polynomial `P_α(z) = z² + e^{2πiα} z` whose Julia set is provably locally connected. Is
`J(P_α)` locally connected for Lebesgue almost every choice of `α`? What can be said about the
Hausdorff dimension of `J(P_α)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import WantedExt.Dynamics.CremerCriticalPointAccessibleAMR52Problem0030Wanted

@[expose] public section

namespace MathlibExt.Dynamics.SiegelJuliaLocallyConnectedAMR52Problem0034Wanted

/-!
Source: J. Milnor (ed.), Problems in holomorphic dynamics (Stony Brook, 1992), arXiv:math/9205209,
Problems on local connectivity, Problem 9,
https://www.math.stonybrook.edu/open-problems-dynamical-systems. UnsolvedMath record UM-05300034
(`AMR-052-0034`), dataset ulamai/UnsolvedMath v1.8.0.

`P_α`, its filled Julia set, its Julia set (the boundary of the filled Julia set) and Cremer
parameters are imported from
`WantedExt/Dynamics/CremerCriticalPointAccessibleAMR52Problem0030Wanted.lean`. As in the source,
`P_α` is a Siegel polynomial when `α` is irrational and `P_α` is holomorphically linearizable at
`0`, i.e. `0` is not a Cremer point. Local connectivity is that of the Julia set as a subspace of
`ℂ`; 'almost every `α`' is for Lebesgue measure on `ℝ` (`P_α` depends only on `α mod 1`). The
question about the Hausdorff dimension of `J(P_α)` is open-ended and is not formalized.
-/

open MeasureTheory MathlibExt.Dynamics.CremerCriticalPointAccessibleAMR52Problem0030Wanted

/-- `P_α(z) = z² + e^{2πiα} z` is a Siegel polynomial: `α` is irrational and `0` is not a Cremer
point, i.e. `P_α` is holomorphically linearizable at `0` (the rotation `z ↦ e^{2πiα} z` is
conjugate to `P_α` near `0`). -/
def IsSiegel (α : ℝ) : Prop :=
  Irrational α ∧ ¬ IsCremer α

/-- Milnor, Problem 9, first part: some Siegel polynomial `P_α` has a locally connected Julia
set. -/
def siegelJuliaSetLocallyConnectedExample : Prop :=
  ∃ α : ℝ, IsSiegel α ∧ LocallyConnectedSpace (juliaSet α)

/-- Milnor, Problem 9, second part: the Julia set of `P_α` is locally connected for Lebesgue almost
every `α`. -/
def juliaSetLocallyConnectedAlmostEvery : Prop :=
  ∀ᵐ α : ℝ ∂volume, LocallyConnectedSpace (juliaSet α)

/--
Resolved true: Petersen proves that for every `α` of bounded type (for instance the golden mean)
`P_α` is a Siegel polynomial whose Julia set is locally connected. Source: J. Milnor (ed.), Problems
in holomorphic dynamics (Stony Brook, 1992), arXiv:math/9205209, Problems on local connectivity,
Problem 9, https://www.math.stonybrook.edu/open-problems-dynamical-systems; resolution: C. L.
Petersen, Local connectivity of some Julia sets containing a circle with an irrational rotation,
Acta Math. 177 (1996), 163-224, main theorem (Zbl 0884.30020): for θ of constant (bounded) type, the
Julia set of P_θ(z) = e^{2πiθ} z + z², which has a Siegel disc around 0, is locally connected and
has Lebesgue measure zero; e.g. θ = (√5 - 1)/2, https://doi.org/10.1007/BF02392621.
-/
public theorem_wanted siegelJuliaSetLocallyConnectedExample_holds :
    siegelJuliaSetLocallyConnectedExample

/--
Resolved true: Petersen and Zakeri prove that the Julia set of `P_α` is locally connected (and of
measure zero) whenever the continued fraction digits of `α` satisfy `log a_n = O(√n)`, which holds
for Lebesgue almost every `α`. Source: J. Milnor (ed.), Problems in holomorphic dynamics (Stony
Brook, 1992), arXiv:math/9205209, Problems on local connectivity, Problem 9,
https://www.math.stonybrook.edu/open-problems-dynamical-systems; resolution: C. L. Petersen and S.
Zakeri, On the Julia set of a typical quadratic polynomial with a Siegel disk, Ann. of Math. 159
(2004), 1-52, main theorem (Zbl 1069.37038): if the continued fraction digits a_n of θ satisfy log
a_n = O(√n), a condition satisfied by a set of θ of full measure, the Julia set of z² + e^{2πiθ} z
is locally connected and has Lebesgue measure zero, https://doi.org/10.4007/annals.2004.159.1.
-/
public theorem_wanted juliaSetLocallyConnectedAlmostEvery_holds :
    juliaSetLocallyConnectedAlmostEvery

end MathlibExt.Dynamics.SiegelJuliaLocallyConnectedAMR52Problem0034Wanted
