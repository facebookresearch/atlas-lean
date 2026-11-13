/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Self-convolution of log-concave probability mass functions on ℤᵈ (Oberwolfach Report 58/2024)

M. Fradelizi (with L. Gavalakis and M. Rapaport), On the monotonicity of discrete entropy for
log-concave random vectors in `ℤᵈ`, Oberwolfach Report 58/2024, p. 3360: a probability mass function
on `ℤᵈ` is log-concave if it is the restriction of a log-concave function on `ℝᵈ`; does
self-convolution preserve this property?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Probability.DiscreteLogConcaveSelfConvolutionOWR14298808Problem013Wanted

/-!
Source: M. Fradelizi (with L. Gavalakis and M. Rapaport), On the monotonicity of discrete entropy
for log-concave random vectors in Z^d, in Convex Geometry and its Applications, Oberwolfach Reports
21 (2024), no. 58, p. 3360, DOI 10.4171/OWR/2024/58. UnsolvedMath record UM-30006136
(`OWR-14298808-013`), dataset ulamai/UnsolvedMath v1.8.0.

The report calls a probability mass function `p` on `ℤᵈ` log-concave if some log-concave `f : ℝᵈ →
ℝ` (`f ≥ 0` and `f((1 - t) x + t y) ≥ f(x)^{1 - t} f(y)^t` for `t ∈ [0, 1]`, the standard
definition) restricts to `p` on `ℤᵈ`, and states "This is an open question to know if
self-convolution preserves this definition"; the self-convolution is `(p * p)(z) = ∑ₓ p(x) p(z -
x)`. The statement is the positive answer in every dimension `d`, refuted. MathlibExt's
`ThinShell.IsLogConcaveDensity` also requires Borel measurability, which the report's definition
does not, so the property is written out here.
-/

/-- `f : ℝᵈ → ℝ` is log-concave: `f ≥ 0` and `f((1 - t) x + t y) ≥ f(x)^{1 - t} f(y)^t` for
`t ∈ [0, 1]`. -/
def IsLogConcaveFunction {d : ℕ} (f : (Fin d → ℝ) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ∀ x y : Fin d → ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f x ^ (1 - t) * f y ^ t ≤ f ((1 - t) • x + t • y)

/-- `p` is a probability mass function on `ℤᵈ`: nonnegative, summable, total mass `1`. -/
def IsProbabilityMassFunction {d : ℕ} (p : (Fin d → ℤ) → ℝ) : Prop :=
  (∀ z, 0 ≤ p z) ∧ Summable p ∧ ∑' z, p z = 1

/-- `p` is the restriction to `ℤᵈ` of a log-concave function on `ℝᵈ` (the report's definition of a
log-concave probability mass function on `ℤᵈ`). -/
def IsLogConcaveRestriction {d : ℕ} (p : (Fin d → ℤ) → ℝ) : Prop :=
  ∃ f : (Fin d → ℝ) → ℝ, IsLogConcaveFunction f ∧ ∀ z, p z = f fun i => (z i : ℝ)

/-- The self-convolution `(p * p)(z) = ∑_x p(x) p(z - x)`. -/
noncomputable def selfConvolution {d : ℕ} (p : (Fin d → ℤ) → ℝ) : (Fin d → ℤ) → ℝ :=
  fun z => ∑' x, p x * p (z - x)

/-- The open question of Fradelizi's abstract (Oberwolfach Report 58/2024, p. 3360), positive
answer: for every `d`, the self-convolution of a probability mass function on `ℤᵈ` that is the
restriction of a log-concave function on `ℝᵈ` is again such a restriction. -/
def selfConvolutionPreservesLogConcavity : Prop :=
  ∀ (d : ℕ) (p : (Fin d → ℤ) → ℝ), IsProbabilityMassFunction p → IsLogConcaveRestriction p →
    IsLogConcaveRestriction (selfConvolution p)

/--
Resolved false: Fradelizi, Gavalakis and Rapaport answer the question in their paper with a
counterexample in dimension `3` (Remark 12): the support of a log-concave probability mass function
on `ℤᵈ` is `ℤᵈ`-convex (the lattice points of its convex hull), the Reeve tetrahedron `S = {(0,0,0),
(1,0,0), (0,1,0), (1,1,2)}` is `ℤ³`-convex, and `S + S` misses `(1,1,1)`, the midpoint of `(1,1,0)`
and `(1,1,2)`, so it is not `ℤ³`-convex; the uniform distribution on `S` is log-concave and its
self-convolution, supported on `S + S`, is not. The same remark records that convolution preserves
log-concavity in dimension `1` and that `S + S` is `ℤ²`-convex for every `ℤ²`-convex `S`, so
dimension `2` is not settled by this argument. Source: M. Fradelizi (with L. Gavalakis and M.
Rapaport), On the monotonicity of discrete entropy for log-concave random vectors in Z^d, in Convex
Geometry and its Applications, Oberwolfach Reports 21 (2024), no. 58, p. 3360, DOI
10.4171/OWR/2024/58; resolution: M. Fradelizi, L. Gavalakis and M. Rapaport, On the monotonicity of
discrete entropy for log-concave random vectors on Z^d, Discrete Comput. Geom. (2026), DOI
10.1007/s00454-025-00813-7, arXiv:2401.15462, Remark 12, with Definitions 10-11 (A ⊂ Z^d is
Z^d-convex iff its indicator is log-concave extensible; the support of a log-concave function on Z^d
is Z^d-convex): the Reeve tetrahedron S = {(0,0,0),(1,0,0),(0,1,0),(1,1,2)} is Z^3-convex, but S + S
does not contain (1,1,1) and is thus not Z^3-convex; arXiv v4 comments: 'A counterexample was added
to Remark 12 answering a question from the previous version',
https://doi.org/10.1007/s00454-025-00813-7.
-/
public theorem_wanted selfConvolutionPreservesLogConcavity_refuted :
    ¬ selfConvolutionPreservesLogConcavity

end MathlibExt.Probability.DiscreteLogConcaveSelfConvolutionOWR14298808Problem013Wanted
