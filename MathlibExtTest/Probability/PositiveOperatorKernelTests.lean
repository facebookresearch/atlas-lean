/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.TransitionKernel

/-!
# Tests for positive-operator Markov kernels

The probes cover identity and non-identity operators, the order of noncommuting composition,
and the actual Wright–Fisher transition law on the allele-frequency interval.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

namespace MathlibExt.Probability.PositiveOperatorKernelTest

open MathlibExt.Probability.PositiveOperatorKernel
open MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
open MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting

/-- Averaging against the Dirac mass at `a`: every input function is sent to its constant value at
`a`. This is a non-identity positive unital operator whose transition forgets the starting point. -/
noncomputable def fixedPointAveragingOperator (a : I) : C(I, ℝ) →P[ℝ] C(I, ℝ) := by
  let A : C(I, ℝ) →L[ℝ] C(I, ℝ) :=
    (ContinuousLinearMap.const ℝ I).comp (ContinuousMap.evalCLM ℝ a)
  exact PositiveContinuousLinearMap.mk
    (PositiveLinearMap.mk A.toLinearMap fun f g hfg => by
      apply ContinuousMap.le_def.mpr
      intro x
      change f a ≤ g a
      exact ContinuousMap.le_def.mp hfg a)
    A.continuous

/-- Fixed-point averaging is the constant function with the input's value at that point. -/
@[simp]
theorem fixedPointAveragingOperator_apply (a : I) (f : C(I, ℝ)) :
    fixedPointAveragingOperator a f = ContinuousMap.const I (f a) :=
  rfl

/-- Fixed-point averaging preserves the constant function one. -/
@[simp]
theorem fixedPointAveragingOperator_apply_one (a : I) : fixedPointAveragingOperator a 1 = 1 := by
  ext x
  simp

/-- The proof-owning generalized core accepts the underlying plain positive linear map. -/
example (a : I) :
    ∃ K : Kernel I I, IsMarkovKernel K ∧
      ∀ (f : C(I, ℝ)) (x : I), ∫ y, f y ∂K x = fixedPointAveragingOperator a f x :=
  exists_markovKernelOfPositiveLinearMap
    (fixedPointAveragingOperator a).toPositiveLinearMap
    (fixedPointAveragingOperator_apply_one a)

/-- Identity operators produce Dirac transition measures. -/
example (x : I) :
    markovKernelOfPositiveOperator (PositiveContinuousLinearMap.id ℝ C(I, ℝ)) (by rfl) x =
      Measure.dirac x :=
  markovKernelOfPositiveOperator_id_apply x

/-- Fixed-point averaging produces the constant Dirac kernel at that point. -/
example (a : I) :
    markovKernelOfPositiveOperator (fixedPointAveragingOperator a)
        (fixedPointAveragingOperator_apply_one a) =
      Kernel.const I (Measure.dirac a) := by
  apply kernel_ext_of_forall_integral_continuous_eq
  intro f x
  rw [integral_markovKernelOfPositiveOperator, Kernel.const_apply]
  simp

/-- Kernel composition follows the public generic theorem in the noncommuting fixed-point case. -/
example (a b : I) :
    markovKernelOfPositiveOperator (fixedPointAveragingOperator b)
        (fixedPointAveragingOperator_apply_one b) ∘ₖ
      markovKernelOfPositiveOperator (fixedPointAveragingOperator a)
        (fixedPointAveragingOperator_apply_one a) =
      Kernel.const I (Measure.dirac b) := by
  rw [← markovKernelOfPositiveOperator_comp]
  apply kernel_ext_of_forall_integral_continuous_eq
  intro f x
  rw [integral_markovKernelOfPositiveOperator, Kernel.const_apply]
  change fixedPointAveragingOperator a (fixedPointAveragingOperator b f) x = _
  simp

/-- Averaging at `0` after `1` differs from averaging at `1` after `0`. -/
example : (fixedPointAveragingOperator 0).comp (fixedPointAveragingOperator 1) ≠
    (fixedPointAveragingOperator 1).comp (fixedPointAveragingOperator 0) := by
  intro h
  have h' := congrArg (fun T => T (ContinuousMap.mk (fun y : I => (y : ℝ)) (by fun_prop)) 0) h
  simp at h'

/-- One-half as a point of the Wright–Fisher allele-frequency interval. -/
noncomputable def halfFrequency : I := ⟨1 / 2, by constructor <;> norm_num⟩

/-- Every Wright–Fisher transition from one-half has probability mass one. -/
example (t : ℝ) : wfTransitionKernel t halfFrequency Set.univ = 1 :=
  measure_univ

/-- At time zero, the actual Wright–Fisher transition from one-half is Dirac. -/
example : wfTransitionKernel 0 halfFrequency = Measure.dirac halfFrequency :=
  wfTransitionKernel_zero_apply halfFrequency

/-- The documented nonpositive-time convention gives the identity kernel. -/
example : wfTransitionKernel (-1) = (Kernel.id : Kernel I I) :=
  wfTransitionKernel_of_nonpos (by norm_num)

/-- The Chapman–Kolmogorov law specializes to concrete positive times on the interval. -/
example : wfTransitionKernel (1 + 2) = wfTransitionKernel 2 ∘ₖ wfTransitionKernel 1 := by
  exact wfTransitionKernel_add (by norm_num) (by norm_num)

/-- The actual Wright–Fisher transition from `1/2` has the block-counting moment formula. -/
example {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∫ y, ((Polynomial.X ^ n : Polynomial ℝ).toContinuousMapOn I) y ∂
        wfTransitionKernel t halfFrequency =
      ∑ k : Fin (n + 1),
        NormedSpace.exp (t • blockCountingGenerator n) (Fin.last n) k *
          (halfFrequency : ℝ) ^ (k : ℕ) :=
  integral_wfTransitionKernel_X_pow ht n halfFrequency

end MathlibExt.Probability.PositiveOperatorKernelTest
