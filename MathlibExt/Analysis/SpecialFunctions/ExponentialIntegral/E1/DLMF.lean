/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.ExponentialIntegral.E1.TwoTermRemainder

open Filter Set Topology MeasureTheory

noncomputable section

@[expose] public section

namespace Complex

/-- **Two-term remainder bound for $E_1$ in the outer sector.** Let $z \ne 0$ be a complex number
with $\pi/2 \le |\arg z| < \pi$, where $\arg z \in (-\pi, \pi]$ is the principal argument. Let
$E_1(z)$ be the principal exponential integral, let
$T_n(z) = \frac{e^{-z}}{z} \cdot \frac{(-1)^n n!}{z^n}$ be the $n$-th term of its asymptotic
expansion, and let $R_2(z) = E_1(z) - T_0(z) - T_1(z)$ be the remainder after the first two
terms. Then $|R_2(z)| \le \frac{|T_2(z)|}{\sin |\arg z|}$.

Source: DLMF 6.12.1 and the outer-sector remainder bound of DLMF §6.12(i), with $n = 2$. -/
theorem principal_exponential_integral_e1_two_term_remainder_dlmf
    (z : ℂ) (hz : z ≠ 0) (hargLower : Real.pi / 2 ≤ |z.arg|)
    (hargUpper : |z.arg| < Real.pi) :
    ‖e1AsymptoticRemainder 2 z hz‖ ≤
      (Real.sin |z.arg|)⁻¹ * ‖e1AsymptoticTerm 2 z hz‖ := by
  rw [two_term_integral_remainder z hz hargUpper]
  exact integral_remainder_bound z hz hargLower hargUpper

end Complex

end
