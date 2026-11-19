/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.PopulationGenetics.Admixture.JacobianRankIdentifiability

/-! Tests for Jacobian-rank identifiability: the immersion criterion, generic
restatements of the three-population results, and the star-tree example. -/

open Filter Set Matrix MeasureTheory
  MathlibExt.Biology.PopulationGenetics.FStatistics
open scoped Topology

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.JacobianRankIdentifiability

open MathlibExt.Biology.PopulationGenetics.Admixture
  MathlibExt.Analysis.Calculus.LocalInverseBridge

example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → F} {f' : E →L[ℝ] F} {a : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f a) (hf' : HasFDerivAt f f' a) (hn : n ≠ 0)
    (hinj : Function.Injective f') :
    ∃ s ∈ 𝓝 a, InjOn f s :=
  exists_mem_nhds_injOn_of_contDiffAt_injective hf hf' hn hinj

example {p : Fin 5 → ℝ} (hp : p 2 + p 3 ≠ 0) :
    (MetaMathlibExt.jacobianMatrix threePopF2 p).rank = 3 :=
  threePopF2_jacobian_rank hp

example {p : Fin 5 → ℝ} (hp : p 2 + p 3 ≠ 0) :
    ¬ Function.Injective (fderiv ℝ threePopF2 p) :=
  threePopF2_not_injective_fderiv hp

example {α s s' a b c t : ℝ} :
    threePopF2 ![α, s', a + t, b - t, c] = threePopF2 ![α, s, a, b, c] :=
  threePopF2_eq_shift

example : Function.Injective starTreeF2 := starTreeF2_injective

example (p : Fin 3 → ℝ) : Function.Injective (fderiv ℝ starTreeF2 p) :=
  starTreeF2_injective_fderiv p

end MathlibExtTest.Biology.PopulationGenetics.Admixture.JacobianRankIdentifiability
