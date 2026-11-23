/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.BilateralShiftOperator
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.NormedSpace

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The spectrum of the bilateral shift is the unit circle

For the bilateral shift `S` on `ℓ²(ℤ, 𝕜)` and its adjoint, the backward
shift `B`, the spectrum is the unit circle `Metric.sphere 0 1`. The proof
has three parts:

* `S` is unitary (`mem_unitary_bilateralShiftCLM`), so its spectrum is
  contained in the unit circle (`spectrum.subset_circle_of_unitary`).
* Every point `μ` of the unit circle is in the spectrum: the truncated
  vectors `approxEigenVec μ N`, equal to `(star μ) ^ n` on `[-N, N]` and
  `0` outside, satisfy `‖v_N‖² = 2N + 1` while the residual
  `‖(μ • 1 - S) v_N‖² = 2`, since the only surviving coordinates of the
  residual are the two boundary terms. If `μ • 1 - S` were a unit it
  would be bounded below (open mapping / anti-Lipschitz), contradicting
  `‖v_N‖ / ‖(μ • 1 - S) v_N‖ → ∞`.
* The spectrum of `B` follows from the spectrum of `S` since
  `B = star S` and `spectrum.map_star`, using that the unit circle is
  stable under `star`.

This is a companion to the Hilbert-space / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`.
It is not one of the 72 v1 targets. The proof below uses the bilateral
shift construction and Mathlib's unitary-spectrum and Banach-operator APIs.

## Main declarations

* `approxEigenVec` : the truncated approximate eigenvector `(star μ) ^ n`
  on `[-N, N]`, for `‖μ‖ = 1`.
* `norm_sq_approxEigenVec` : `‖approxEigenVec μ N‖² = 2N + 1`.
* `norm_sq_residual_approxEigenVec` :
  `‖(μ • 1 - S) (approxEigenVec μ N)‖² = 2`.
* `mem_spectrum_bilateralShiftCLM_of_norm_eq_one` : every point of the
  unit circle is in the spectrum of `S`.
* `spectrum_bilateralShiftCLM` : `spectrum 𝕜 S = Metric.sphere 0 1`.
* `spectrum_bilateralBackwardCLM` : `spectrum 𝕜 B = Metric.sphere 0 1`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.BilateralShiftSpectrum

open Filter Topology Set Metric
open scoped _root_.lp _root_.InnerProduct _root_.InnerProductSpace ENNReal
open MathlibExt.Analysis.InnerProductSpace.BilateralShiftOperator

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **A unit scalar times its conjugate is one.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. If $\mu \in \mathbb{K}$ satisfies $|\mu| = 1$, then $\mu \bar{\mu} = 1$, where
$\bar{\mu}$ is the complex conjugate of $\mu$. -/
theorem mul_star_eq_one_of_norm_eq_one {μ : 𝕜} (hμ : ‖μ‖ = 1) : μ * star μ = 1 := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (x := μ)
  rw [RCLike.inner_apply, starRingEnd_apply, hμ] at h
  simpa using h

/-- **Conjugates of unimodular scalars are nonzero.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$. If $\mu \in \mathbb{K}$ satisfies $|\mu| = 1$, then its conjugate $\bar{\mu}$ is
nonzero. -/
theorem star_ne_zero_of_norm_eq_one {μ : 𝕜} (hμ : ‖μ‖ = 1) : star μ ≠ 0 := by
  intro h
  have hnorm : ‖star μ‖ = 1 := by rw [norm_star, hμ]
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

/-- **Multiplying a power of the conjugate by a unit scalar.** Let $\mathbb{K}$ be $\mathbb{R}$
or $\mathbb{C}$, and write $\bar{\mu}$ for the complex conjugate of $\mu \in \mathbb{K}$. If
$|\mu| = 1$, then for every integer $n$, $\mu \bar{\mu}^{\,n} = \bar{\mu}^{\,n-1}$. -/
theorem mul_star_zpow {μ : 𝕜} (hμ : ‖μ‖ = 1) (n : ℤ) :
    μ * (star μ) ^ n = (star μ) ^ (n - 1) := by
  have hc0 := star_ne_zero_of_norm_eq_one hμ
  have h1 : (star μ) ^ n = (star μ) ^ (n - 1) * star μ := by
    conv_lhs => rw [← sub_add_cancel n 1]
    exact zpow_add_one₀ hc0 (n - 1)
  rw [h1, mul_comm ((star μ) ^ (n - 1)) (star μ), ← mul_assoc,
    mul_star_eq_one_of_norm_eq_one hμ, one_mul]

/-- **Truncated approximate eigenfunction of the bilateral shift.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $\mu \in \mathbb{K}$ and $N \in \mathbb{N}$, and write
$\bar{\mu}$ for the complex conjugate of $\mu$. This is the function
$f_{\mu,N} : \mathbb{Z} \to \mathbb{K}$ with $f_{\mu,N}(n) = \bar{\mu}^{\,n}$ for
$-N \le n \le N$ and $f_{\mu,N}(n) = 0$ otherwise (negative powers are inverses, with the
convention $0^{n} = 0$ for $n < 0$).

It is used for $\mu$ on the unit circle, where it gives approximate eigenvectors of the
bilateral shift. -/
def approxEigenFun (μ : 𝕜) (N : ℕ) (n : ℤ) : 𝕜 :=
  if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then (star μ) ^ n else 0

theorem approxEigenFun_of_mem {μ : 𝕜} {N : ℕ} {n : ℤ}
    (hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    approxEigenFun μ N n = (star μ) ^ n := by
  simp [approxEigenFun, hn]

theorem approxEigenFun_of_notMem {μ : 𝕜} {N : ℕ} {n : ℤ}
    (hn : n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) :
    approxEigenFun μ N n = 0 := by
  simp [approxEigenFun, hn]

theorem memℓp_approxEigenFun {μ : 𝕜} (N : ℕ) : Memℓp (approxEigenFun μ N) 2 := by
  apply memℓp_gen
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) ?_
  intro n hn
  rw [approxEigenFun_of_notMem hn]
  simp [Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]

/-- **Truncated approximate eigenvector of the bilateral shift.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $\mu \in \mathbb{K}$ and $N \in \mathbb{N}$, and write
$\bar{\mu}$ for the complex conjugate of $\mu$. This is the vector
$v_{\mu,N} \in \ell^2(\mathbb{Z}, \mathbb{K})$ whose $n$-th coordinate is the truncated
approximate eigenfunction $f_{\mu,N}(n)$, that is, $\bar{\mu}^{\,n}$ for $-N \le n \le N$ and
$0$ otherwise; it lies in $\ell^2$ because it has finite support.

It is used for $\mu$ on the unit circle, where it is an approximate eigenvector of the
bilateral shift. -/
noncomputable def approxEigenVec (μ : 𝕜) (N : ℕ) : ℓ²(ℤ, 𝕜) :=
  ⟨approxEigenFun μ N, memℓp_approxEigenFun N⟩

theorem approxEigenVec_apply (μ : 𝕜) (N : ℕ) (n : ℤ) :
    approxEigenVec μ N n = approxEigenFun μ N n := rfl

/-- **Norm of the truncated approximate eigenvector.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $\mu \in \mathbb{K}$ with $|\mu| = 1$, and let $N \in \mathbb{N}$. The
truncated approximate eigenvector $v_{\mu,N} \in \ell^2(\mathbb{Z}, \mathbb{K})$, whose $n$-th
coordinate is $\bar{\mu}^{\,n}$ for $-N \le n \le N$ and $0$ otherwise ($\bar{\mu}$ the complex
conjugate of $\mu$), satisfies $\|v_{\mu,N}\|^2 = 2N + 1$. -/
theorem norm_sq_approxEigenVec {μ : 𝕜} (hμ : ‖μ‖ = 1) (N : ℕ) :
    ‖approxEigenVec μ N‖ ^ 2 = 2 * (N : ℝ) + 1 := by
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  have htsum : ‖approxEigenVec μ N‖ ^ (2 : ℝ) =
      ∑' n, ‖approxEigenFun μ N n‖ ^ (2 : ℝ) := by
    rw [← hexp]
    exact lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) _
  rw [Real.rpow_two] at htsum
  rw [htsum]
  have htsum2 : ∑' n, ‖approxEigenFun μ N n‖ ^ (2 : ℝ) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖approxEigenFun μ N n‖ ^ (2 : ℝ) :=
    tsum_eq_sum (by
      intro n hn
      rw [approxEigenFun_of_notMem hn]
      simp [Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)])
  rw [htsum2]
  have hterm : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ‖approxEigenFun μ N n‖ ^ (2 : ℝ) = 1 := by
    intro n hn
    rw [approxEigenFun_of_mem hn]
    have hnorm : ‖(star μ) ^ n‖ = 1 := by
      rw [norm_zpow, norm_star, hμ, one_zpow]
    rw [hnorm]
    exact Real.one_rpow _
  rw [Finset.sum_congr rfl (fun n hn => hterm n hn), Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.Icc (-(N : ℤ)) (N : ℤ)).card : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [Int.card_Icc]
    have heq : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [heq, Int.toNat_natCast]
    push_cast
    ring
  rw [hcard, mul_one]

/-- **Applying $\mu I - T$ on $\ell^2(\mathbb{Z})$.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $T$ be a bounded linear operator on $\ell^2(\mathbb{Z}, \mathbb{K})$, let
$\mu \in \mathbb{K}$, and let $\mu I$ be the image of $\mu$ under the algebra map from $\mathbb{K}$
to the bounded operators on $\ell^2(\mathbb{Z}, \mathbb{K})$, that is, $\mu$ times the identity.
Then for every $x \in \ell^2(\mathbb{Z}, \mathbb{K})$, $(\mu I - T)x = \mu x - Tx$. -/
theorem algebraMap_sub_apply (T : ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) (μ : 𝕜)
    (x : ℓ²(ℤ, 𝕜)) :
    (algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - T) x = μ • x - T x := by
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [sub_apply, smul_apply, one_apply_eq_self]

/-- **Coordinates of the residual of the truncated approximate eigenvector.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, let $S$ be the bilateral shift on $\ell^2(\mathbb{Z}, \mathbb{K})$,
and let $\mu \in \mathbb{K}$, $N \in \mathbb{N}$ and $n \in \mathbb{Z}$. Let $f_{\mu,N}$ be the
truncated approximate eigenfunction and $v_{\mu,N} \in \ell^2(\mathbb{Z}, \mathbb{K})$ the
corresponding truncated approximate eigenvector. Then the $n$-th coordinate of
$(\mu I - S)v_{\mu,N}$ is $\mu f_{\mu,N}(n) - f_{\mu,N}(n - 1)$, where $\mu I$ is $\mu$ times
the identity operator. -/
theorem residual_apply {μ : 𝕜} (N : ℕ) (n : ℤ) :
    ((algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - bilateralShiftCLM (𝕜 := 𝕜))
        (approxEigenVec μ N)) n =
      μ * approxEigenFun μ N n - approxEigenFun μ N (n - 1) := by
  rw [algebraMap_sub_apply]
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    bilateralShiftCLM_apply, bilateralShiftFun_apply, approxEigenVec_apply]

/-- **Residual of the truncated approximate eigenvector.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$, let $S$ be the bilateral shift on $\ell^2(\mathbb{Z}, \mathbb{K})$, let
$\mu \in \mathbb{K}$ with $|\mu| = 1$, and let $N \in \mathbb{N}$. The truncated approximate
eigenvector $v_{\mu,N}$ satisfies $\|(\mu I - S)v_{\mu,N}\|^2 = 2$, where $\mu I$ is $\mu$ times
the identity operator.

The only nonzero coordinates of $(\mu I - S)v_{\mu,N}$ are those at $n = -N$ and $n = N + 1$,
each of absolute value $1$. -/
theorem norm_sq_residual_approxEigenVec {μ : 𝕜} (hμ : ‖μ‖ = 1) (N : ℕ) :
    ‖(algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - bilateralShiftCLM (𝕜 := 𝕜))
        (approxEigenVec μ N)‖ ^ 2 = 2 := by
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  have htsum : ‖(algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - bilateralShiftCLM (𝕜 := 𝕜))
        (approxEigenVec μ N)‖ ^ (2 : ℝ) =
      ∑' n, ‖((algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - bilateralShiftCLM (𝕜 := 𝕜))
        (approxEigenVec μ N)) n‖ ^ (2 : ℝ) := by
    rw [← hexp]
    exact lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) _
  rw [Real.rpow_two] at htsum
  rw [htsum]
  have hne : (-(N : ℤ)) ≠ (N : ℤ) + 1 := by omega
  have htsum2 : ∑' n, ‖((algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - bilateralShiftCLM (𝕜 := 𝕜))
        (approxEigenVec μ N)) n‖ ^ (2 : ℝ) =
      ∑ n ∈ ({-(N : ℤ), (N : ℤ) + 1} : Finset ℤ),
        ‖((algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - bilateralShiftCLM (𝕜 := 𝕜))
          (approxEigenVec μ N)) n‖ ^ (2 : ℝ) := by
    apply tsum_eq_sum
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    push Not at hn
    obtain ⟨hn1, hn2⟩ := hn
    rw [residual_apply]
    by_cases h1 : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
    · by_cases h2 : (n - 1) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
      · rw [approxEigenFun_of_mem h1, approxEigenFun_of_mem h2,
          mul_star_zpow hμ n, sub_self]
        simp [Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
      · exfalso
        have hm1 := Finset.mem_Icc.mp h1
        rw [Finset.mem_Icc] at h2
        push Not at h2
        omega
    · by_cases h2 : (n - 1) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
      · exfalso
        have hm2 := Finset.mem_Icc.mp h2
        rw [Finset.mem_Icc] at h1
        push Not at h1
        omega
      · rw [approxEigenFun_of_notMem h1, approxEigenFun_of_notMem h2]
        simp [Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
  rw [htsum2, Finset.sum_pair hne]
  have hleft : ‖((algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - bilateralShiftCLM (𝕜 := 𝕜))
        (approxEigenVec μ N)) (-(N : ℤ))‖ ^ (2 : ℝ) = 1 := by
    rw [residual_apply]
    have hmem : -(N : ℤ) ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      rw [Finset.mem_Icc]
      exact ⟨le_refl _, by omega⟩
    have hnot : -(N : ℤ) - 1 ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      rw [Finset.mem_Icc]
      push Not
      intro h
      omega
    rw [approxEigenFun_of_mem hmem, approxEigenFun_of_notMem hnot, sub_zero]
    have hnorm : ‖μ * (star μ) ^ (-(N : ℤ))‖ = 1 := by
      rw [norm_mul, hμ, norm_zpow, norm_star, hμ, one_zpow, mul_one]
    rw [hnorm]
    exact Real.one_rpow _
  have hright : ‖((algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - bilateralShiftCLM (𝕜 := 𝕜))
        (approxEigenVec μ N)) ((N : ℤ) + 1)‖ ^ (2 : ℝ) = 1 := by
    rw [residual_apply]
    have hnot : (N : ℤ) + 1 ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      rw [Finset.mem_Icc]
      push Not
      intro h
      omega
    have hmem : (N : ℤ) + 1 - 1 ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      rw [Finset.mem_Icc]
      constructor <;> omega
    rw [approxEigenFun_of_notMem hnot, approxEigenFun_of_mem hmem, mul_zero, zero_sub]
    have heq : (N : ℤ) + 1 - 1 = (N : ℤ) := by omega
    rw [heq, norm_neg, norm_zpow, norm_star, hμ, one_zpow]
    exact Real.one_rpow _
  rw [hleft, hright]
  norm_num

/-- **Every point of the unit circle lies in the spectrum of the bilateral shift.** Let
$\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ and let $S$ be the bilateral shift on
$\ell^2(\mathbb{Z}, \mathbb{K})$. Every $\mu \in \mathbb{K}$ with $|\mu| = 1$ lies in the
spectrum of $S$ in the algebra of bounded operators on $\ell^2(\mathbb{Z}, \mathbb{K})$, that
is, $\mu I - S$ is not invertible there, where $\mu I$ is $\mu$ times the identity operator.

If $\mu I - S$ were invertible it would be bounded below, but the truncated approximate
eigenvectors $v_{\mu,N}$ satisfy $\|v_{\mu,N}\| = \sqrt{2N + 1}$ and
$\|(\mu I - S)v_{\mu,N}\| = \sqrt{2}$ for every $N \in \mathbb{N}$. -/
theorem mem_spectrum_bilateralShiftCLM_of_norm_eq_one {μ : 𝕜} (hμ : ‖μ‖ = 1) :
    μ ∈ spectrum 𝕜 (bilateralShiftCLM (𝕜 := 𝕜)) := by
  rw [spectrum.mem_iff]
  intro hunit
  have hbij : Function.Bijective
      ⇑(algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - bilateralShiftCLM (𝕜 := 𝕜)) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  have hclosed : IsClosed (Set.range
      ⇑(algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - bilateralShiftCLM (𝕜 := 𝕜))) := by
    rw [Set.range_eq_univ.mpr hbij.2]
    exact isClosed_univ
  obtain ⟨K, hK⟩ := ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range
    _ hbij.1 hclosed
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (K : ℝ) ^ 2)
  have hanti := hK (approxEigenVec μ N) 0
  rw [map_zero, edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (K : ℝ))] at hanti
  have hanti' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hanti
  rw [dist_zero_right, dist_zero_right] at hanti'
  have hsq : ‖approxEigenVec μ N‖ ^ 2 ≤
      ((K : ℝ) * ‖(algebraMap 𝕜 (ℓ²(ℤ, 𝕜) →L[𝕜] ℓ²(ℤ, 𝕜)) μ - bilateralShiftCLM (𝕜 := 𝕜))
        (approxEigenVec μ N)‖) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) hanti'
  rw [norm_sq_approxEigenVec hμ N, mul_pow, norm_sq_residual_approxEigenVec hμ N] at hsq
  have hN' : (2 : ℝ) * (N : ℝ) + 1 ≤ 2 * (K : ℝ) ^ 2 := by linarith [hsq]
  linarith [hN, hN']

/-- **Spectrum of the bilateral shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$. The
spectrum of the bilateral shift, as a bounded operator on $\ell^2(\mathbb{Z}, \mathbb{K})$, is the
set of scalars $\mu \in \mathbb{K}$ with $|\mu| = 1$; for $\mathbb{K} = \mathbb{C}$ this is the
unit circle. -/
theorem spectrum_bilateralShiftCLM :
    spectrum 𝕜 (bilateralShiftCLM (𝕜 := 𝕜)) = Metric.sphere 0 1 := by
  apply Subset.antisymm
  · exact spectrum.subset_circle_of_unitary mem_unitary_bilateralShiftCLM
  · intro μ hμ
    rw [mem_sphere_zero_iff_norm] at hμ
    exact mem_spectrum_bilateralShiftCLM_of_norm_eq_one hμ

/-- **Spectrum of the bilateral backward shift.** Let $\mathbb{K}$ be $\mathbb{R}$ or
$\mathbb{C}$ and let $B$ be the bilateral backward shift on $\ell^2(\mathbb{Z}, \mathbb{K})$.
The spectrum of $B$ in the algebra of bounded operators on $\ell^2(\mathbb{Z}, \mathbb{K})$ is
the unit circle $\{\mu \in \mathbb{K} : |\mu| = 1\}$. -/
theorem spectrum_bilateralBackwardCLM :
    spectrum 𝕜 (bilateralBackwardCLM (𝕜 := 𝕜)) = Metric.sphere 0 1 := by
  have h1 : bilateralBackwardCLM (𝕜 := 𝕜) = star (bilateralShiftCLM (𝕜 := 𝕜)) := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_bilateralShiftCLM]
  rw [h1, spectrum.map_star, spectrum_bilateralShiftCLM]
  ext μ
  simp only [Set.mem_star, mem_sphere_zero_iff_norm, norm_star]

end MathlibExt.Analysis.InnerProductSpace.BilateralShiftSpectrum
