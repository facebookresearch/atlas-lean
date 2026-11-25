/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/WienerAtom.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `wiener_atom_detection` (manifest
`manifests/problems/wiener_atom_detection.toml`, revision 1, submitted by Kim Morrison).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The definition of `fourierCoeffMeasure` and the statement of `wiener_atom_detection` were placed
in the ATLAS namespace and their docstrings updated in the former wanted module. The source
was distributed without a `NOTICE` file. The declarations are moved here with their full names
and statements preserved. The proof is new.
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.Field.GeomSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Wiener's atom-detection formula

The Cesàro means of the squared Fourier coefficient norms of a probability measure on the
circle converge to the sum of its squared point masses. The averaged characters of the
difference of two points converge to the indicator of the diagonal.
-/

@[expose] public section

namespace MathlibExt.Analysis.WienerAtomWanted.Analysis

open MeasureTheory Filter Topology Real Complex
open scoped ComplexConjugate

set_option linter.dupNamespace false in
/-- **Fourier coefficients of a measure on the circle.** For a measure $\mu$ on the circle
$\mathbb{T} = \mathbb{R}/2\pi\mathbb{Z}$ and an integer $k$, the $k$-th Fourier coefficient of
$\mu$ is $\hat\mu_k = \int_{\mathbb{T}} e^{ikx} \, d\mu(x)$. -/
noncomputable def fourierCoeffMeasure (μ : Measure (AddCircle (2 * Real.pi)))
    (k : ℤ) : ℂ :=
  ∫ x, fourier k x ∂μ

local notation "Torus" => AddCircle (2 * Real.pi)

private noncomputable def kernel (N : ℕ) (p : Torus × Torus) : ℂ :=
  (1 / (N : ℂ)) * ∑ k ∈ Finset.Ico 1 (N + 1), fourier (k : ℤ) (p.1 - p.2)

private theorem norm_kernel_le (N : ℕ) (p : Torus × Torus) : ‖kernel N p‖ ≤ 1 := by
  have hsum : ‖∑ k ∈ Finset.Ico 1 (N + 1), fourier (k : ℤ) (p.1 - p.2)‖ ≤ N := by
    refine (norm_sum_le _ _).trans ?_
    simp [fourier_apply, Circle.norm_coe]
  rw [kernel, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans (by
    rcases eq_or_ne N 0 with rfl | h
    · simp
    · simp [h])

private theorem tendsto_kernel (p : Torus × Torus) :
    Tendsto (fun N ↦ kernel N p) atTop (𝓝 ((Set.diagonal Torus).indicator (fun _ ↦ 1) p)) := by
  classical
  by_cases h : p.1 = p.2
  · rw [Set.indicator_of_mem (Set.mem_diagonal_iff.mpr h)]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop 0] with N hN
    simp [kernel, h, hN]
  · rw [Set.indicator_of_notMem (fun hp ↦ h (Set.mem_diagonal_iff.mp hp))]
    let z : ℂ := AddCircle.toCircle (p.1 - p.2)
    have hz : z ≠ 1 := by
      intro hz
      apply h
      apply sub_eq_zero.mp
      apply AddCircle.injective_toCircle (by positivity)
      apply Subtype.ext
      simpa [z] using hz
    have hpow (k : ℕ) : fourier (k : ℤ) (p.1 - p.2) = z ^ k := by
      simp [z, fourier_apply, AddCircle.toCircle_nsmul]
    simp only [kernel, hpow, geom_sum_Ico hz (Nat.le_add_left 1 _), pow_one]
    apply tendsto_one_div_atTop_nhds_zero_nat.zero_mul_isBoundedUnder_le
    refine ⟨2 / ‖z - 1‖, eventually_map.mpr <| Eventually.of_forall fun N ↦ ?_⟩
    have hnorm : ‖z‖ = 1 := Circle.norm_coe _
    change ‖(z ^ (N + 1) - z) / (z - 1)‖ ≤ _
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    simpa [norm_pow, hnorm, one_add_one_eq_two] using norm_sub_le (z ^ (N + 1)) z

private theorem integral_fourier_sub (μ : Measure Torus) [IsProbabilityMeasure μ] (k : ℤ) :
    ∫ p : Torus × Torus, fourier k (p.1 - p.2) ∂μ.prod μ =
      (‖fourierCoeffMeasure μ k‖ ^ 2 : ℝ) := by
  have h (p : Torus × Torus) :
      fourier k (p.1 - p.2) = fourier k p.1 * conj (fourier k p.2) := by
    simp only [fourier_apply, sub_eq_add_neg, smul_add, smul_neg, AddCircle.toCircle_add,
      Circle.coe_mul, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]
  simp_rw [h]
  rw [integral_prod_mul (fourier k) (fun y ↦ conj (fourier k y)), integral_conj,
    Complex.mul_conj, Complex.sq_norm, fourierCoeffMeasure]

private theorem integral_kernel (μ : Measure Torus) [IsProbabilityMeasure μ] (N : ℕ) :
    ∫ p, kernel N p ∂μ.prod μ =
      ((1 / (N : ℝ)) * ∑ k ∈ Finset.Icc (1 : ℤ) N, ‖fourierCoeffMeasure μ k‖ ^ 2 : ℝ) := by
  simp only [kernel, integral_const_mul, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_natCast, Complex.ofReal_sum]
  congr 1
  rw [integral_finsetSum]
  · simp_rw [integral_fourier_sub]
    apply Finset.sum_nbij' (fun k : ℕ ↦ (k : ℤ)) Int.toNat
    all_goals simp only [Finset.mem_Icc, Finset.mem_Ico]
    all_goals (intros; first | trivial | omega)
  · intro k _
    have : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    have hc : Continuous (fun p : Torus × Torus ↦ fourier (k : ℤ) (p.1 - p.2)) :=
      (fourier (k : ℤ)).continuous.comp (continuous_fst.sub continuous_snd)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem measure_diagonal (μ : Measure Torus) [IsProbabilityMeasure μ] :
    (μ.prod μ).real (Set.diagonal Torus) = ∑' x : Torus, (μ {x}).toReal ^ 2 := by
  let s := Function.support (fun x : Torus ↦ μ {x})
  have hs : s.Countable := by
    simpa [s, Function.support, pos_iff_ne_zero] using
      (Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ)
        (fun x : Torus ↦ measurableSet_singleton x) (fun _ _ h ↦ Set.disjoint_singleton.mpr h))
  have hslice (x : Torus) : Prod.mk x ⁻¹' Set.diagonal Torus = {x} := by
    ext y
    simp [Set.diagonal, eq_comm]
  rw [measureReal_def, Measure.prod_apply measurableSet_diagonal]
  simp_rw [hslice]
  rw [← setLIntegral_eq_of_support_subset (s := s) (Set.Subset.rfl),
    lintegral_countable _ hs]
  simp only [← sq, ENNReal.tsum_toReal_eq (fun _ ↦ ENNReal.pow_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_pow]
  apply tsum_subtype_eq_of_support_subset (f := fun x : Torus ↦ (μ {x}).toReal ^ 2)
  intro x hx
  contrapose hx
  simp_all [s, Function.mem_support]

set_option linter.dupNamespace false in
/-- **Wiener's atom-detection formula.** Let $\mu$ be a probability measure on the circle
$\mathbb{T} = \mathbb{R}/2\pi\mathbb{Z}$, with Fourier coefficients
$\hat\mu_k = \int_{\mathbb{T}} e^{ikx} \, d\mu(x)$. Then
$\frac{1}{N} \sum_{k=1}^{N} \lvert \hat\mu_k \rvert^2 \to \sum_{x \in \mathbb{T}} \mu(\{x\})^2$
as $N \to \infty$.

Source: N. Wiener, The Fourier Integral and Certain of its Applications (1933). Listed as §66 in O.
Knill, Some Fundamental Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `wiener_atom_detection`. -/
theorem wiener_atom_detection
    (μ : Measure (AddCircle (2 * Real.pi))) [IsProbabilityMeasure μ] :
    Tendsto
      (fun N : ℕ =>
        (1 / (N : ℝ)) *
          ∑ k ∈ Finset.Icc (1 : ℤ) N, ‖fourierCoeffMeasure μ k‖ ^ 2)
      atTop
      (𝓝 (∑' x : AddCircle (2 * Real.pi), ((μ {x}).toReal) ^ 2)) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ.prod μ) (fun _ ↦ (1 : ℝ))
    (F := kernel) (fun N ↦ by
      apply Continuous.aestronglyMeasurable
      unfold kernel
      fun_prop) (integrable_const _) (fun N ↦ .of_forall (norm_kernel_le N))
    (.of_forall tendsto_kernel)
  rw [integral_indicator measurableSet_diagonal, setIntegral_const, measure_diagonal] at h
  simp_rw [integral_kernel] at h
  simpa only [Function.comp_def, ofReal_re, Complex.real_smul, mul_one] using
    (Complex.continuous_re.tendsto _).comp h

end MathlibExt.Analysis.WienerAtomWanted.Analysis
