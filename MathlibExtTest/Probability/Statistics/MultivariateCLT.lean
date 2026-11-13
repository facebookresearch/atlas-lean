/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultivariateCLT
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Tests for the multivariate central limit theorem

* `E = ℝ`: the interface theorem specializes to the scalar CLT's `(√n)⁻¹ * (∑ - n * P[X 0])`
  shape.
* Degenerate: a constant sequence has every projection variance `0`, and the limit `Y = 0`
  satisfies the projection hypotheses.
* `E = EuclideanSpace ℝ (Fin 2)`: the interface theorem with a given limit, and the constructed
  limit for an i.i.d. sequence of standard Gaussian vectors realized on `ℕ → E`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset RealInnerProductSpace
open scoped Real

namespace MultivariateCLTTest

/-! ### `E = ℝ` recovers the scalar statement shape -/

example {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ} (hY : AEMeasurable Y P')
    (hYlaw : ∀ t : ℝ,
      HasLaw (fun ω ↦ ⟪Y ω, t⟫) (gaussianReal 0 (Var[fun ω ↦ ⟪X 0 ω, t⟫; P]).toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ range n, X k ω - n * P[X 0]))
      atTop Y (fun _ ↦ P) P' := by
  simpa [smul_eq_mul, nsmul_eq_mul] using
    tendstoInDistribution_inv_sqrt_smul_sum_sub hY hYlaw hX hindep hident

/-! ### Degenerate case: a constant sequence converges to `0` -/

/-- A constant sequence on a product probability space, with every projection variance `0`. -/
example (c : EuclideanSpace ℝ (Fin 2)) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → ℝ) ↦
        (√n)⁻¹ • (∑ _k ∈ range n, (fun _ : ℕ → ℝ ↦ c) ω -
          n • ∫ _, c ∂(Measure.infinitePi fun _ : ℕ ↦ gaussianReal 0 1)))
      atTop (fun _ : Unit ↦ (0 : EuclideanSpace ℝ (Fin 2)))
      (fun _ ↦ Measure.infinitePi fun _ : ℕ ↦ gaussianReal 0 1) (Measure.dirac ()) := by
  refine tendstoInDistribution_inv_sqrt_smul_sum_sub (X := fun _ _ ↦ c) aemeasurable_const
    (fun t ↦ ⟨aemeasurable_const, ?_⟩) (memLp_const c)
    (iIndepFun_infinitePi (X := fun _ (_ : ℝ) ↦ c) fun _ ↦ measurable_const)
    fun _ ↦ IdentDistrib.refl aemeasurable_const
  rw [variance_eq_integral aemeasurable_const]
  simp

/-! ### `E = EuclideanSpace ℝ (Fin 2)` -/

/-- The interface theorem in the plane with a given limit `Y`. -/
example {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X : ℕ → Ω → EuclideanSpace ℝ (Fin 2)} {Y : Ω' → EuclideanSpace ℝ (Fin 2)}
    (hY : AEMeasurable Y P')
    (hYlaw : ∀ t, HasLaw (fun ω ↦ ⟪Y ω, t⟫)
      (gaussianReal 0 (Var[fun ω ↦ ⟪X 0 ω, t⟫; P]).toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ • (∑ k ∈ range n, X k ω - n • ∫ ω, X 0 ω ∂P))
      atTop Y (fun _ ↦ P) P' :=
  tendstoInDistribution_inv_sqrt_smul_sum_sub hY hYlaw hX hindep hident

/-- The constructed limit for i.i.d. standard Gaussian vectors in the plane, realized as the
coordinates of `ℕ → EuclideanSpace ℝ (Fin 2)` under the infinite product measure. -/
example : ∃ A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2),
    HasGaussianLaw A (stdGaussian _) ∧
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → EuclideanSpace ℝ (Fin 2)) ↦ (√n)⁻¹ • (∑ k ∈ range n, ω k -
        n • ∫ ω, ω 0 ∂(Measure.infinitePi fun _ ↦ stdGaussian (EuclideanSpace ℝ (Fin 2)))))
      atTop A (fun _ ↦ Measure.infinitePi fun _ ↦ stdGaussian (EuclideanSpace ℝ (Fin 2)))
      (stdGaussian _) := by
  have hlaw : ∀ i, (Measure.infinitePi fun _ : ℕ ↦ stdGaussian (EuclideanSpace ℝ (Fin 2))).map
      (fun ω ↦ ω i) = stdGaussian _ := fun i ↦ Measure.infinitePi_map_eval _ i
  have hX0 : MemLp (fun ω : ℕ → EuclideanSpace ℝ (Fin 2) ↦ ω 0) 2
      (Measure.infinitePi fun _ ↦ stdGaussian (EuclideanSpace ℝ (Fin 2))) := by
    have h : MemLp id 2 ((Measure.infinitePi fun _ : ℕ ↦
        stdGaussian (EuclideanSpace ℝ (Fin 2))).map (fun ω ↦ ω 0)) := by
      rw [hlaw]
      exact IsGaussian.memLp_two_id
    exact (memLp_map_measure_iff aestronglyMeasurable_id (measurable_pi_apply 0).aemeasurable).1 h
  obtain ⟨A, hA, -, hconv⟩ := exists_tendstoInDistribution_inv_sqrt_smul_sum_sub
    (X := fun k (ω : ℕ → EuclideanSpace ℝ (Fin 2)) ↦ ω k) hX0
    (iIndepFun_infinitePi (P := fun _ ↦ stdGaussian (EuclideanSpace ℝ (Fin 2)))
      (X := fun _ (x : EuclideanSpace ℝ (Fin 2)) ↦ x) fun _ ↦ measurable_id)
    fun i ↦ ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      by rw [hlaw, hlaw]⟩
  exact ⟨A, hA, hconv⟩

end MultivariateCLTTest
