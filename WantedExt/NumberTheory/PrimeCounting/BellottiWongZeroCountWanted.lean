/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros
import Batteries.Util.ProofWanted

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/-!
## Bellotti–Wong zero-counting bound

`N(T)`, the number of nontrivial zeta zeros `ρ = β + iγ` with
`0 < γ ≤ T` counted with multiplicity, satisfies the two explicit
upper bounds below (the `+` halves of Theorem 1.1). The count sums
`meromorphicOrderAt` over the finite zero set in the strip box;
only upper bounds are filed since the ladders need `N(T)` from above.

Source: Lorenzo Bellotti and Kyle Wong, *Improved estimates for the
argument and zero-counting function of the Riemann zeta-function*
(with appendix by Andrew Fiori), arXiv:2412.15470v2 (accepted by
Math. Comp.), Theorem 1.1, <https://arxiv.org/html/2412.15470v2>.
-/

/-- **Zero-counting function of the Riemann zeta function.** For a real number $T$, $N(T)$ is
the number of zeros $\rho = \beta + i\gamma$ of the Riemann zeta function with $0 < \beta < 1$
and $0 < \gamma \le T$, each counted with its multiplicity as a zero. -/
noncomputable def zetaZeroCount (T : ℝ) : ℕ :=
  have hfin : (riemannZetaZeros ∩ {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T}).Finite := by
    have hsub : (riemannZetaZeros ∩ {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T})
        ⊆ Metric.closedBall 0 (|T| + 2) ∩ riemannZetaZeros := by
      intro ρ h
      obtain ⟨hmem, hre0, hre1, him0, himT⟩ := h
      refine ⟨?_, hmem⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have hre : |ρ.re| < 1 := abs_lt.mpr ⟨by linarith, hre1⟩
      have him : |ρ.im| ≤ |T| :=
        abs_le.mpr ⟨by linarith [abs_nonneg T], le_trans himT (le_abs_self T)⟩
      have h1 : ρ.re ^ 2 ≤ 1 := by nlinarith [hre0, hre1]
      have h2 : ρ.im ^ 2 ≤ T ^ 2 := sq_le_sq.mpr him
      have hnorm : ‖ρ‖ ^ 2 = ρ.re ^ 2 + ρ.im ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        ring
      have h3 : ‖ρ‖ ^ 2 ≤ (|T| + 2) ^ 2 := by
        rw [hnorm]
        nlinarith [h1, h2, sq_abs T, abs_nonneg T]
      have h4 := sq_le_sq.mp h3
      rwa [abs_of_nonneg (norm_nonneg ρ), abs_of_nonneg (by positivity : (0 : ℝ) ≤ |T| + 2)] at h4
    exact (isCompact_closedBall 0 _).inter_riemannZetaZeros_finite.subset hsub
  Finset.sum hfin.toFinset
    (fun ρ => (WithTop.untopD 0 (meromorphicOrderAt riemannZeta ρ)).toNat)

/-- **First Bellotti–Wong bound on the zero-counting function.** For every real number
$T \ge e$, the number $N(T)$ of zeros $\rho = \beta + i\gamma$ of the Riemann zeta function with
$0 < \beta < 1$ and $0 < \gamma \le T$, counted with multiplicity, satisfies
$$
N(T) \le \frac{T}{2\pi} \log \frac{T}{2\pi e} + 0.10076 \log T + 0.24460 \log \log T + 8.08344.
$$

This bound is sharper than the second Bellotti–Wong bound for $T$ above about $e^{447.981}$. -/
public theorem_wanted bellotti_wong_zero_count_bound (T : ℝ) (hT : Real.exp 1 ≤ T) :
    (zetaZeroCount T : ℝ) ≤ T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))
      + 0.10076 * Real.log T + 0.24460 * Real.log (Real.log T) + 8.08344

/-- **Second Bellotti–Wong bound on the zero-counting function.** For every real number
$T \ge e$, the number $N(T)$ of zeros $\rho = \beta + i\gamma$ of the Riemann zeta function with
$0 < \beta < 1$ and $0 < \gamma \le T$, counted with multiplicity, satisfies
$$
N(T) \le \frac{T}{2\pi} \log \frac{T}{2\pi e} + 0.11200 \log T + 0.12567 \log \log T + 3.77417.
$$

This bound is sharper than the first Bellotti–Wong bound for $T$ below about $e^{447.981}$. -/
public theorem_wanted bellotti_wong_zero_count_bound_small (T : ℝ) (hT : Real.exp 1 ≤ T) :
    (zetaZeroCount T : ℝ) ≤ T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))
      + 0.11200 * Real.log T + 0.12567 * Real.log (Real.log T) + 3.77417

end MetaMathlibExt
