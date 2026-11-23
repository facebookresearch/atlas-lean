/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Meckes's question on expected volumes of random simplices (Oberwolfach Report 10/2017)

M. Reitzner, High-dimensional random polytopes, Mini-Workshop: Perspectives in High-Dimensional
Probability and Convexity, Oberwolfach Report 10/2017, p. 519: does there exist `c(d)` with
`lim_{d→∞} c(d)^{1/d} < ∞` such that for all convex bodies `K ⊂ L` one has `E V_d(P^K_{d+1}) ≤ c(d)
E V_d(P^L_{d+1})`? (Meckes)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import MathlibExt.Geometry.Convex.Covering

@[expose] public section

namespace MathlibExt.Geometry.RandomSimplexVolumeMonotonicityOWR15215Problem006Wanted

/-!
Source: M. Reitzner, High-dimensional random polytopes, in Mini-Workshop: Perspectives in
High-Dimensional Probability and Convexity, Oberwolfach Reports 14 (2017), no. 10, p. 519, DOI
10.4171/OWR/2017/10. UnsolvedMath record UM-30003397 (`OWR-15215-006`), dataset ulamai/UnsolvedMath
v1.8.0.

`P^K_{d+1}` is the convex hull of `d + 1` independent points uniform in `K`, so `E V_d(P^K_{d+1})`
is the integral of the volume of the hull over `K^{d+1}` divided by `vol(K)^{d+1}`. A convex body is
a compact convex set with nonempty interior (MathlibExt `ConvexCovering.IsConvexBody`). The
condition `lim_{d→∞} c(d)^{1/d} < ∞` is transcribed as printed in the report: the constants are
positive (they bound a ratio of positive expectations) and `c(d)^{1/d}` converges to a real number.
The UnsolvedMath record writes `limsup`; for this existence question the readings `lim`, `limsup`
and `c(d) ≤ C^d` are interchangeable (enlarge `c` to `C^d`), and the report's own form is used, so
the report's equivalence with the slicing problem applies to the statement verbatim. The report's
second request, a lower bound for the optimal `c(d)` (open problem on p. 519), is open-ended and is
not formalized.
-/

open MeasureTheory

/-- `E V_d(P^K_{d+1})`: the expected volume of the convex hull of `d + 1` independent points
uniformly distributed in `K ⊆ ℝ^d`, i.e. the integral of the volume of the hull over `K^{d+1}`
divided by `vol(K)^{d+1}`. -/
noncomputable def expectedSimplexVolume {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  (∫ x in Set.univ.pi fun _ : Fin (d + 1) => K, (volume (convexHull ℝ (Set.range x))).toReal) /
    (volume K).toReal ^ (d + 1)

/-- Meckes's question as printed in Oberwolfach Report 10/2017, p. 519: there are positive constants
`c(d)` with `lim_{d → ∞} c(d)^{1/d} < ∞` (the limit exists and is a real number) such that
`E V_d(P^K_{d+1}) ≤ c(d) E V_d(P^L_{d+1})` for all convex bodies `K ⊆ L ⊂ ℝ^d`. -/
def meckesRandomSimplexQuestion : Prop :=
  ∃ c : ℕ → ℝ, (∀ d, 0 < c d) ∧
    (∃ A : ℝ, Filter.Tendsto (fun d : ℕ => c d ^ ((1 : ℝ) / d)) Filter.atTop (nhds A)) ∧
    ∀ (d : ℕ) (K L : Set (EuclideanSpace ℝ (Fin d))), ConvexCovering.IsConvexBody K →
      ConvexCovering.IsConvexBody L → K ⊆ L →
        expectedSimplexVolume K ≤ c d * expectedSimplexVolume L

/--
Resolved true: the report states after Meckes's original question (this statement, with `lim
c(d)^{1/d} < ∞`) "Now, this is equivalent to a positive solution to the slicing problem" (p. 519),
and Klartag and Lehec resolved Bourgain's slicing problem affirmatively: every convex body of volume
one in `ℝⁿ` has a hyperplane section of volume at least a universal constant `c > 0`. Source: M.
Reitzner, High-dimensional random polytopes, in Mini-Workshop: Perspectives in High-Dimensional
Probability and Convexity, Oberwolfach Reports 14 (2017), no. 10, p. 519, DOI 10.4171/OWR/2017/10;
resolution: B. Klartag and J. Lehec, Affirmative resolution of Bourgain's slicing problem using
Guan's bound, Geom. Funct. Anal. (2025), DOI 10.1007/s00039-025-00718-w, arXiv:2412.15044;
Oberwolfach Report 10/2017, p. 519, Klartag-Lehec abstract: for any convex body K in R^n of volume
one there is a hyperplane H with Vol_{n-1}(K ∩ H) > c, c > 0 universal; report p. 519: Meckes's
question 'is equivalent to a positive solution to the slicing problem',
https://arxiv.org/abs/2412.15044.
-/
public theorem_wanted meckesRandomSimplexQuestion_holds : meckesRandomSimplexQuestion

end MathlibExt.Geometry.RandomSimplexVolumeMonotonicityOWR15215Problem006Wanted
