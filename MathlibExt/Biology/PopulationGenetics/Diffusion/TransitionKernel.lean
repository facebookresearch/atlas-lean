/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Diffusion.Semigroup
public import MathlibExt.Probability.PositiveOperatorKernel

/-!
# Transition kernel of the neutral Wright–Fisher diffusion

The positive-operator representation theorem turns `wfSemigroup t` into a genuine Markov kernel
on the allele-frequency interval `[0, 1]`. The kernel represents the semigroup on every continuous
test function. At time zero it is the identity kernel, and the semigroup law becomes canonical
kernel composition.

## References

* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Chapter 1.
* S. N. Ethier and R. C. Griffiths, *The transition function of a Fleming–Viot process*,
  Ann. Probab. 21 (1993), 1571–1590.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory unitInterval

namespace MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup

open MathlibExt.Probability.PositiveOperatorKernel
open MathlibExt.Biology.PopulationGenetics.Coalescent.KingmanBlockCounting

/-- The Wright–Fisher semigroup bundled as a positive continuous linear operator. -/
noncomputable def wfSemigroupPositive (t : ℝ) : C(I, ℝ) →P[ℝ] C(I, ℝ) :=
  PositiveContinuousLinearMap.mk
    (PositiveLinearMap.mk (wfSemigroup t).toLinearMap fun f g hfg => by
      have hgf : 0 ≤ g - f := ContinuousMap.le_def.mpr fun x =>
        sub_nonneg.mpr (ContinuousMap.le_def.mp hfg x)
      apply ContinuousMap.le_def.mpr
      intro x
      have hx := ContinuousMap.le_def.mp (wfSemigroup_nonneg t hgf) x
      rw [map_sub] at hx
      exact sub_nonneg.mp hx)
    (wfSemigroup t).continuous

/-- Bundling the operator as positive leaves its action on continuous functions unchanged. -/
@[simp]
theorem wfSemigroupPositive_apply (t : ℝ) (f : C(I, ℝ)) :
    wfSemigroupPositive t f = wfSemigroup t f :=
  rfl

/-- The positive Wright–Fisher operator fixes the constant function `1`. -/
@[simp]
theorem wfSemigroupPositive_apply_one (t : ℝ) : wfSemigroupPositive t 1 = 1 := by
  simpa only [wfSemigroupPositive_apply] using wfSemigroup_apply_one t

/-- The positive-operator form of the Wright–Fisher semigroup law. -/
theorem wfSemigroupPositive_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    wfSemigroupPositive (s + t) =
      (wfSemigroupPositive s).comp (wfSemigroupPositive t) := by
  ext f x
  simp [wfSemigroup_add hs ht]

/-- The transition kernel of the neutral Wright–Fisher diffusion at time `t`. For nonnegative `t`
it is the probabilistic transition corresponding to `wfSemigroup t`; for negative `t`, both the
operator and kernel are the identity junk value inherited from `wfSemigroup`. -/
noncomputable def wfTransitionKernel (t : ℝ) : Kernel I I :=
  markovKernelOfPositiveOperator (wfSemigroupPositive t) (wfSemigroupPositive_apply_one t)

/-- Every transition measure of the Wright–Fisher kernel is a probability measure. -/
noncomputable instance isMarkovKernel_wfTransitionKernel (t : ℝ) :
    IsMarkovKernel (wfTransitionKernel t) := by
  rw [wfTransitionKernel]
  infer_instance

/-- Integration against the transition kernel agrees with the Wright–Fisher semigroup on every
continuous test function and every initial allele frequency. -/
@[simp]
theorem integral_wfTransitionKernel (t : ℝ) (f : C(I, ℝ)) (x : I) :
    ∫ y, f y ∂wfTransitionKernel t x = wfSemigroup t f x := by
  rw [wfTransitionKernel, integral_markovKernelOfPositiveOperator, wfSemigroupPositive_apply]

/-- For nonpositive times, the Wright–Fisher transition is the identity kernel. -/
theorem wfTransitionKernel_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    wfTransitionKernel t = (Kernel.id : Kernel I I) := by
  apply kernel_ext_of_forall_integral_continuous_eq
  intro f x
  rw [integral_wfTransitionKernel, wfSemigroup_of_nonpos ht, Kernel.id_apply]
  simp

/-- At time zero the Wright–Fisher transition is the identity kernel. -/
@[simp]
theorem wfTransitionKernel_zero : wfTransitionKernel 0 = (Kernel.id : Kernel I I) :=
  wfTransitionKernel_of_nonpos le_rfl

/-- Pointwise identity law for the transition kernel at time zero. -/
@[simp]
theorem wfTransitionKernel_zero_apply (x : I) : wfTransitionKernel 0 x = Measure.dirac x := by
  rw [wfTransitionKernel_zero, Kernel.id_apply]

/-- Chapman–Kolmogorov law for the Wright–Fisher transition kernels. With Mathlib's convention,
`K_t ∘ₖ K_s` first evolves for time `s` and then for time `t`. -/
theorem wfTransitionKernel_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    wfTransitionKernel (s + t) = wfTransitionKernel t ∘ₖ wfTransitionKernel s := by
  unfold wfTransitionKernel
  simp_rw [wfSemigroupPositive_add hs ht]
  exact markovKernelOfPositiveOperator_comp _ _ _ _

/-- Kernel form of Wright–Fisher moment duality: transition-kernel moments are the transition
probabilities of Kingman's block-counting process. -/
theorem integral_wfTransitionKernel_X_pow {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (x : I) :
    ∫ y, ((Polynomial.X ^ n : Polynomial ℝ).toContinuousMapOn I) y ∂wfTransitionKernel t x =
      ∑ k : Fin (n + 1),
        NormedSpace.exp (t • blockCountingGenerator n) (Fin.last n) k * (x : ℝ) ^ (k : ℕ) := by
  rw [integral_wfTransitionKernel, wfSemigroup_X_pow ht]

end MathlibExt.Biology.PopulationGenetics.Diffusion.WrightFisherSemigroup
