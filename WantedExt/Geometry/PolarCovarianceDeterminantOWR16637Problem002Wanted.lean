/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Covariance determinants of polar convex bodies (Oberwolfach Reports 54/2018)

Oberwolfach workshop Convex Geometry and its Applications (2018), B. Klartag: is there a universal
`C > 0` such that every convex body `K ⊆ ℝⁿ` with barycenter at the origin satisfies `det(Cov(K)
Cov(K°)) ≤ (C/n)^{2n}`?
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.InnerProductSpace.PolarSet
public import MathlibExt.Geometry.Convex.Covering
public import MathlibExt.Probability.Geometry.IsotropicConstant

@[expose] public section

namespace MathlibExt.Geometry.PolarCovarianceDeterminantOWR16637Problem002Wanted

/-!
Source: B. Klartag, in Convex Geometry and its Applications, Oberwolfach Reports 15 (2018), no. 54,
p. 3224, inequality (1), DOI 10.4171/OWR/2018/54. UnsolvedMath record UM-30004024 (`OWR-16637-002`),
dataset ulamai/UnsolvedMath v1.8.0.

`Cov(S)` is the covariance matrix (MathlibExt's `covarianceMatrix`) of the uniform probability
measure `ProbabilityTheory.cond volume S` on `S` (the source's formula); `K° = polarSet K = {y : ⟨x,
y⟩ ≤ 1 for x ∈ K}`; a convex body is a compact convex set with nonempty interior
(`ConvexCovering.IsConvexBody`); barycenter at the origin means `∫_K x dx = 0`. The source states
inequality (1) for convex bodies whose barycenter or whose polar's barycenter is at the origin; the
statement takes the first case, as the record does.
-/

open MeasureTheory
open ConvexCovering (IsConvexBody)
open MetaMathlibExt (polarSet)
open MathlibExt.Probability.IsotropicConstant (covarianceMatrix)

/-- Klartag's inequality (1) (Oberwolfach Report 54/2018, p. 3224): there is a universal `C > 0`
such that every convex body `K ⊆ ℝⁿ` with barycenter at the origin satisfies
`det(Cov(K) Cov(K°)) ≤ (C / n)^{2n}`, where `Cov(S)` is the covariance matrix
(`covarianceMatrix`) of the uniform probability measure `ProbabilityTheory.cond volume S` on `S`
and `K° = polarSet K = {y : ⟨x, y⟩ ≤ 1 for all x ∈ K}`. -/
def polarCovarianceDeterminantBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
    ∫ x in K, x = 0 →
      (covarianceMatrix (ProbabilityTheory.cond volume K) *
          covarianceMatrix (ProbabilityTheory.cond volume (polarSet K))).det ≤ (C / n) ^ (2 * n)

/--
Resolved true: the source states that, by the Santaló and Bourgain-Milman inequalities (`c ≤ n (|K|
|K°|)^{1/n} ≤ C` when the barycenter of `K` or of `K°` is at the origin), Bourgain's slicing problem
is equivalent to inequality (1), and Klartag and Lehec resolved the slicing problem affirmatively
(Theorem 1.1; stated in this repository as
`MathlibExt.Geometry.HyperplaneSlicingUniversalWanted.conjecture_holds`). Source: B. Klartag, in
Convex Geometry and its Applications, Oberwolfach Reports 15 (2018), no. 54, p. 3224, inequality
(1), DOI 10.4171/OWR/2018/54; resolution: B. Klartag and J. Lehec, Affirmative resolution of
Bourgain's slicing problem using Guan's bound, Geom. Funct. Anal. 35 (2025), no. 4, 1147-1168,
arXiv:2412.15044, Theorem 1.1: every convex body K ⊆ ℝⁿ of volume one has a hyperplane H with
Vol_{n-1}(K ∩ H) > c for a universal c > 0, which is Bourgain's slicing problem as the source states
it; the source (p. 3224) states that, by the Santaló and Bourgain-Milman inequalities, the slicing
problem is equivalent to inequality (1), https://arxiv.org/abs/2412.15044.
-/
public theorem_wanted polarCovarianceDeterminantBound_holds : polarCovarianceDeterminantBound

end MathlibExt.Geometry.PolarCovarianceDeterminantOWR16637Problem002Wanted
