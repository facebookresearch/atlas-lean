/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Constructions.Pi
public import MathlibExt.Probability.KernelMeanEmbedding

/-!
# Concentration of the biased empirical MMD

The kernel two-sample test of Gretton, Borgwardt, Rasch, Schölkopf and Smola compares two
samples through the biased empirical maximum mean discrepancy `MMD_b` (the distance between
the empirical kernel mean embeddings, `KernelMeanEmbedding.mmdBiased_eq`). For a kernel with
values in `[0, K]`, `MMD_b` concentrates around the population `MMD` at rate
`O(√(1/m) + √(1/n))`, uniformly over the distributions: this is what makes the test
distribution-free and consistent against every fixed alternative. The proof combines McDiarmid's
bounded-difference inequality with a symmetrization (Rademacher-average) bound for the unit
ball of the RKHS; neither the RKHS Rademacher bound nor this assembly is in Mathlib or the
repository yet.

Reference: A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, "A kernel
two-sample test", *J. Mach. Learn. Res.* **13** (2012), 723–773, Theorem 7 (proved in
Appendix A.2).
-/

@[expose] public section

open MeasureTheory MathlibExt.Probability.KernelMeanEmbedding

namespace MathlibExt.Probability.KernelTwoSampleTestWanted

/-- **Large-deviation bound for the biased empirical MMD** (Gretton, Borgwardt, Rasch,
Schölkopf and Smola, *A kernel two-sample test*, JMLR 13 (2012), Theorem 7). Let `H` be a real
RKHS on a measurable space `X` whose feature map is strongly measurable and whose kernel
satisfies `0 ≤ k(x, y) ≤ K`. Let `m, n ≥ 1`, let `X = (x₁, …, x_m)` be i.i.d. with law `P` and
`Y = (y₁, …, y_n)` i.i.d. with law `Q`, independent of `X`. Then for every `ε > 0`,
`Pr{|MMD_b[X, Y] - MMD[P, Q]| > 2 (√(K/m) + √(K/n)) + ε} ≤ 2 exp(-ε² m n / (2K(m + n)))`. -/
theorem_wanted measureReal_abs_mmdBiased_sub_mmd_gt_le {X : Type*} [MeasurableSpace X]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [RKHS ℝ H X ℝ] (hφ : StronglyMeasurable (featureMap H)) {K : ℝ}
    (hk : ∀ x y, 0 ≤ kernelValue H x y ∧ kernelValue H x y ≤ K)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {m n : ℕ} [NeZero m] [NeZero n] {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin n => ν)).real
        {z | 2 * (√(K / m) + √(K / n)) + ε < |mmdBiased H z.1 z.2 - mmd H μ ν|} ≤
      2 * Real.exp (-(ε ^ 2 * m * n / (2 * K * (m + n))))

end MathlibExt.Probability.KernelTwoSampleTestWanted
