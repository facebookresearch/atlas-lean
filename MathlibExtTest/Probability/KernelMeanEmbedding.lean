/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KernelMeanEmbedding
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

@[expose] public section

/-!
# Tests for kernel mean embeddings and the maximum mean discrepancy
-/

set_option autoImplicit false

open MeasureTheory RKHS
open scoped InnerProductSpace
open MathlibExt.Probability.KernelMeanEmbedding

namespace MathlibExtTest.Probability.KernelMeanEmbedding

/-- The biased empirical MMD of one point against one point is `k(x,x) - 2k(x,y) + k(y,y)`. -/
example {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [RKHS ℝ H X ℝ] (a b : X) :
    mmdBiased H (fun _ : Fin 1 => a) (fun _ : Fin 1 => b) ^ 2 =
      kernelValue H a a - 2 * kernelValue H a b + kernelValue H b b := by
  rw [mmdBiased_sq_eq]
  simp

/-- The MMD of a measure against itself vanishes. -/
example {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [RKHS ℝ H X ℝ] (μ : Measure X) (hμ : Integrable (featureMap H) μ) :
    mmd H μ μ = 0 := by
  rw [mmd_eq_norm_sub hμ hμ, sub_self, norm_zero]

/-- A two-point compact metric space. -/
abbrev S := ({0, 1} : Set ℝ)

/-- The indicator functions of the two points of `S`. -/
noncomputable def e (a : ℝ) : S → ℝ := fun s => if (s : ℝ) = a then 1 else 0

/-- The kernel `k(s, t) = δₛₜ` on `S`, as a sum of two rank-one kernels. -/
noncomputable abbrev K₂ : Matrix S S (ℝ →L[ℝ] ℝ) :=
  RKHS.outerKernel ℝ (e 0) + RKHS.outerKernel ℝ (e 1)

instance : Fact K₂.PosSemidef :=
  ⟨(RKHS.posSemidef_outerKernel (𝕜 := ℝ) (e 0)).add (RKHS.posSemidef_outerKernel (𝕜 := ℝ) (e 1))⟩

/-- Its RKHS: all functions on the two points. -/
abbrev H₂ := RKHS.OfKernel K₂

theorem kernelValue_H₂ (s t : S) : kernelValue H₂ s t = e 0 s * e 0 t + e 1 s * e 1 t := by
  have h := kernel_eq_smul (H := H₂) s t
  rw [RKHS.OfKernel.kernel_ofKernel] at h
  have h1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h
  simp [K₂] at h1
  rw [← h1]
  ring

/-- Non-vacuity of Theorem 5 with content: on the two-point space `S`, the kernel `δₛₜ` is
continuous and its RKHS is all of `C(S)`, so `MMD(P, Q) = 0` forces `P = Q`. -/
example (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    mmd H₂ μ ν = 0 ↔ μ = ν := by
  refine mmd_eq_zero_iff_of_universal continuous_of_discreteTopology (fun f ε hε => ?_) μ ν
  let p₀ : S := ⟨0, by simp⟩
  let p₁ : S := ⟨1, by simp⟩
  refine ⟨f p₀ • featureMap H₂ p₀ + f p₁ • featureMap H₂ p₁, fun x => ?_⟩
  have : (f p₀ • featureMap H₂ p₀ + f p₁ • featureMap H₂ p₁ : H₂) x = f x := by
    rw [RKHS.coe_add, RKHS.coe_smul, RKHS.coe_smul, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      featureMap_apply, featureMap_apply, kernelValue_H₂, kernelValue_H₂]
    obtain ⟨v, hv⟩ := x
    rcases hv with rfl | hv
    · simp [e, p₀, p₁]
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      simp [e, p₀, p₁]
  rw [this, sub_self, abs_zero]
  exact hε.le

/-- The hypotheses of the translation-invariant characterization (Sriperumbudur et al.,
Theorem 9) are satisfiable with `d = 1`: the constant kernel `k ≡ 1` on `ℝ¹` is
`∫ exp(-i (x - y)ᵀω) dΛ(ω)` for `Λ` the Dirac mass at `0`. -/
example : ∀ x y : EuclideanSpace ℝ (Fin 1),
    (kernelValue (RKHS.OfKernel (RKHS.outerKernel ℝ (fun _ : EuclideanSpace ℝ (Fin 1) => (1 : ℝ))))
      x y : ℂ) =
      ∫ ω, Complex.exp (-((⟪x - y, ω⟫_ℝ : ℝ) : ℂ) * Complex.I)
        ∂(Measure.dirac (0 : EuclideanSpace ℝ (Fin 1))) := by
  intro x y
  have h := kernel_eq_smul
    (H := RKHS.OfKernel (RKHS.outerKernel ℝ (fun _ : EuclideanSpace ℝ (Fin 1) => (1 : ℝ)))) x y
  rw [RKHS.OfKernel.kernel_ofKernel] at h
  have h1 := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h
  simp [RKHS.outerKernel_apply] at h1
  rw [integral_dirac]
  simp [← h1]

end MathlibExtTest.Probability.KernelMeanEmbedding
