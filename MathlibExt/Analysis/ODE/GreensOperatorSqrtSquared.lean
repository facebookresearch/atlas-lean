/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal
public import MathlibExt.Analysis.ODE.GreensOperator

/-!
# The square of the Green's operator's square root

The v1 book defines the square root `A^{1/2}` of the Green's operator for
the Dirichlet Laplacian on `[0, 1]` by its action on the sine eigenbasis:
if `f = ∑' k, c_k b_k` with `c_k = ⟨b_k, f⟩`, then
`A^{1/2} f = ∑' k, (1 / (kπ)) c_k b_k`. The Green's operator itself has the
corresponding expansion with eigenvalues `λ_k = 1 / (k²π²)`.

This file identifies the canonical square root with a bounded continuous
diagonal map and proves its composition with itself equals the supplied
Green linear operator. The operator must have the canonical self-adjoint
and kernel-a.e. properties, and the basis must represent the actual indexed
sine functions a.e. The proof combines bounded diagonal squaring with the
already proved canonical Green eigendecomposition.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
`SpectralTheory.greensOperatorSqrt` with `greensEigenvalueSqrt` and
`greensEigenvalue` (Definition, May 13, 2021 section). The v1 file states
only the definition of `A^{1/2}`; the squaring identity is not proved there.
-/

@[expose] public section

open MeasureTheory
open MathlibExt.Analysis.InnerProductSpace.HilbertBasisDiagonal

namespace MathlibExt.Analysis.ODE.GreensOperatorSqrtSquared

open MathlibExt.Analysis.ODE.GreensOperator

/-- The Green's square-root coefficients `1 / (kπ)` are bounded by `1 / π`. -/
private theorem greensSqrtCoeff_bound (k : ℕ+) :
    ‖greensEigenvalueSqrt k‖ ≤ 1 / Real.pi := by
  unfold greensEigenvalueSqrt
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast k.pos
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hk1, hpi])

/-- The square of a Green's square-root coefficient is the Green's eigenvalue. -/
private theorem greensSqrtCoeff_sq (k : ℕ+) :
    (greensEigenvalueSqrt k) ^ 2 = greensEigenvalue k := by
  unfold greensEigenvalueSqrt greensEigenvalue
  have hk : (k : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The square root of the Green's operator is a diagonal operator.** Let $(b_k)_{k \ge 1}$ be
a Hilbert basis of $L^2([0, 1])$ indexed by the positive integers with
$b_k(x) = \sqrt{2} \sin(k\pi x)$ for almost every $x \in [0, 1]$, let $\mu_k = \frac{1}{k\pi}$,
and let $C$ be a real number with $|\mu_k| \le C$ for every $k$. Then for every
$f \in L^2([0, 1])$, the square root $A^{1/2} f$ of the Green's operator defined from $(b_k)$
equals $D f$, where $D$ is the bounded diagonal operator with coefficients $(\mu_k)$ in the
basis $(b_k)$ and coefficient bound $C$. -/
theorem greensOperatorSqrt_eq_diagonal
    (b : HilbertBasis ℕ+ ℝ L2UnitInterval)
    (hb : ∀ k : ℕ+, (b k : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (sineBasisFun k : ℝ → ℝ)) {C : ℝ}
    (hC : ∀ k : ℕ+, ‖greensEigenvalueSqrt k‖ ≤ C) (f : L2UnitInterval) :
    greensOperatorSqrt b hb f = diagonalOperator b greensEigenvalueSqrt
      hC f := by
  rw [diagonalOperator_eq_tsum]
  rfl

/-- **The square root of the Green's operator squares to the Green's operator.** Let
$G(x, t) = \min(x, t)\,(1 - \max(x, t))$ be the Green's kernel and let $A$ be a linear map from
$L^2([0, 1])$ to itself that is symmetric, $\langle Af, g \rangle = \langle f, Ag \rangle$ for all
$f, g$, and is given by the Green's kernel, $(Af)(x) = \int_{[0, 1]} G(x, t) f(t)\, dt$ for almost
every $x \in [0, 1]$ and every $f$. Let $(b_k)_{k \ge 1}$ be a Hilbert basis of $L^2([0, 1])$
indexed by the positive integers with $b_k(x) = \sqrt{2} \sin(k\pi x)$ for almost every
$x \in [0, 1]$, and let $A^{1/2}$ be the square root of the Green's operator defined from
$(b_k)$. Then $A^{1/2}(A^{1/2} f) = Af$ for every $f \in L^2([0, 1])$. -/
theorem greensOperatorSqrt_sq
    (A : Module.End ℝ L2UnitInterval)
    (b : HilbertBasis ℕ+ ℝ L2UnitInterval)
    (hA_sa : ∀ f g : L2UnitInterval,
      inner (𝕜 := ℝ) (A f) g = inner (𝕜 := ℝ) f (A g))
    (hb : ∀ k : ℕ+, (b k : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (sineBasisFun k : ℝ → ℝ))
    (hA_greens : ∀ f : L2UnitInterval,
      (A f : L2UnitInterval) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x => ∫ t in Set.Icc (0 : ℝ) 1, greensKernel x t * (f : ℝ → ℝ) t))
    (f : L2UnitInterval) :
    greensOperatorSqrt b hb (greensOperatorSqrt b hb f) = A f := by
  have hexpand := (greens_operator_eigendecomposition A b hA_sa hb hA_greens).2.2 f
  rw [greensOperatorSqrt_eq_diagonal b hb greensSqrtCoeff_bound,
    greensOperatorSqrt_eq_diagonal b hb greensSqrtCoeff_bound]
  rw [diagonalOperator_sq greensSqrtCoeff_bound, diagonalOperator_eq_tsum]
  simpa only [greensSqrtCoeff_sq] using hexpand.symm

end MathlibExt.Analysis.ODE.GreensOperatorSqrtSquared
