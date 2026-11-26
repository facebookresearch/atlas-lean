/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section

open Filter Topology
open scoped InnerProductSpace

namespace MathlibExt.Analysis.InnerProductSpace.OrthonormalWeakConvergence

/-!
# Weak convergence of orthonormal sequences to zero

An orthonormal sequence in an inner product space converges weakly to `0`,
but not strongly: its inner products with any fixed vector tend to `0`
(Bessel's inequality makes the squared norms of the coefficients summable,
hence the coefficients themselves tend to `0`), so every continuous linear
functional vanishes on the sequence in the limit by the Riesz representation
theorem, while the sequence stays at distance `1` from `0` in norm.

This is not in the pinned Mathlib: Mathlib has Bessel's inequality
(`Orthonormal.tsum_inner_products_le`), its summability form
(`Orthonormal.inner_products_summable`), and the Riesz representation
(`InnerProductSpace.toDual`), but no statement that an orthonormal family
tends weakly to `0`.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean`,
`HilbertSpace.bessel_inequality` (Theorem (Bessel), Section preceding
April 13, 2021) and `HilbertSpace.riesz_representation` (Theorem (Riesz
Representation Theorem), April 22, 2021). The v1 file proves Bessel's
inequality from `Orthonormal.tsum_inner_products_le` and Riesz representation
from `InnerProductSpace.toDual`; the weak-convergence conclusion drawn here
from those two ingredients is not stated in v1 or in the pinned Mathlib.
-/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Fourier coefficients along an orthonormal family tend to `0`.** Let $H$ be an inner product
space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $(v_i)_{i \in \iota}$ be an orthonormal
family in $H$ and let $x \in H$. Then the inner products $\langle v_i, x \rangle$ tend to $0$
along the cofinite filter on $\iota$: for every $\varepsilon > 0$,
$|\langle v_i, x \rangle| < \varepsilon$ for all but finitely many $i$.

Bessel's inequality makes their squared absolute values summable, and the terms of a summable
family tend to $0$. -/
theorem tendsto_inner_cofinite_zero {ι : Type*} {v : ι → H} (hv : Orthonormal 𝕜 v)
    (x : H) :
    Tendsto (fun i => ⟪v i, x⟫_𝕜) cofinite (𝓝 0) := by
  have hsum : Summable fun i => ‖⟪v i, x⟫_𝕜‖ ^ 2 := hv.inner_products_summable x
  have h0 : Tendsto (fun i => ‖⟪v i, x⟫_𝕜‖ ^ 2) cofinite (𝓝 0) :=
    hsum.tendsto_cofinite_zero
  have hnorm : Tendsto (fun i => ‖⟪v i, x⟫_𝕜‖) cofinite (𝓝 0) := by
    have hsqrt := h0.sqrt
    rw [Real.sqrt_zero] at hsqrt
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hsqrt
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- **An orthonormal family tends weakly to `0`.** Let $H$ be a Hilbert space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $(v_i)_{i \in \iota}$ be an orthonormal family in
$H$ and let $f : H \to \mathbb{K}$ be a continuous linear functional. Then $f(v_i)$ tends to $0$
along the cofinite filter on $\iota$: for every $\varepsilon > 0$, $|f(v_i)| < \varepsilon$ for
all but finitely many $i$.

By the Riesz representation theorem, $f$ is the inner product with a fixed vector, so this
follows from the corresponding statement for Fourier coefficients. -/
theorem tendsto_apply_cofinite_zero [CompleteSpace H] {ι : Type*} {v : ι → H}
    (hv : Orthonormal 𝕜 v) (f : H →L[𝕜] 𝕜) :
    Tendsto (fun i => f (v i)) cofinite (𝓝 0) := by
  let y := (InnerProductSpace.toDual 𝕜 H).symm f
  have hfy : ∀ x, f x = ⟪y, x⟫_𝕜 := by
    intro x
    have h : (InnerProductSpace.toDual 𝕜 H) y = f :=
      LinearIsometryEquiv.apply_symm_apply (InnerProductSpace.toDual 𝕜 H) f
    rw [← h]
    exact InnerProductSpace.toDual_apply_apply
  have hnorm : Tendsto (fun i => ‖f (v i)‖) cofinite (𝓝 0) := by
    have hcoeff := tendsto_inner_cofinite_zero hv y
    have hcoeffnorm : Tendsto (fun i => ‖⟪v i, y⟫_𝕜‖) cofinite (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hcoeff
    simpa only [hfy, norm_inner_symm] using hcoeffnorm
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- **Fourier coefficients along an orthonormal sequence tend to `0`.** Let $H$ be an inner
product space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $(v_n)_{n \in \mathbb{N}}$ be
an orthonormal sequence in $H$ and let $x \in H$. Then $\langle v_n, x \rangle \to 0$ as
$n \to \infty$. -/
theorem tendsto_inner_atTop_zero {v : ℕ → H} (hv : Orthonormal 𝕜 v) (x : H) :
    Tendsto (fun n => ⟪v n, x⟫_𝕜) atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_inner_cofinite_zero hv x

/-- **An orthonormal sequence tends weakly to `0`.** Let $H$ be a Hilbert space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ and let $(v_n)_{n \in \mathbb{N}}$ be an orthonormal
sequence in $H$. Then for every continuous linear functional $f : H \to \mathbb{K}$, we have
$f(v_n) \to 0$ as $n \to \infty$. -/
theorem tendsto_apply_atTop_zero [CompleteSpace H] {v : ℕ → H} (hv : Orthonormal 𝕜 v)
    (f : H →L[𝕜] 𝕜) :
    Tendsto (fun n => f (v n)) atTop (𝓝 0) := by
  rw [← Nat.cofinite_eq_atTop]
  exact tendsto_apply_cofinite_zero hv f

/-- **An orthonormal sequence does not converge strongly to `0`.** Let $H$ be an inner product
space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ and let $(v_n)_{n \in \mathbb{N}}$ be an
orthonormal sequence in $H$. Then $v_n$ does not tend to $0$ in norm as $n \to \infty$.

Weak convergence does not upgrade to norm convergence here: every term of an orthonormal sequence
has norm $1$. -/
theorem not_tendsto_atTop_zero {v : ℕ → H} (hv : Orthonormal 𝕜 v) :
    ¬ Tendsto v atTop (𝓝 0) := by
  intro h
  have hn : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    have hnorm := h.norm
    simpa only [norm_zero, hv.norm_eq_one] using hnorm
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hn
  exact one_ne_zero h10

#print axioms tendsto_inner_cofinite_zero
#print axioms tendsto_apply_cofinite_zero
#print axioms tendsto_inner_atTop_zero
#print axioms tendsto_apply_atTop_zero
#print axioms not_tendsto_atTop_zero

end MathlibExt.Analysis.InnerProductSpace.OrthonormalWeakConvergence
