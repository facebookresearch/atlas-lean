/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace MetaMathlibExt

open Filter
open scoped Topology

/-- **Binary Epstein zeta functional equation.** For $\operatorname{Im} z > 0$, the sum of
$Q_z(m,n)^{-s}$ over all nonzero integer pairs, with $Q_z(m,n) = |m+nz|^2/\operatorname{Im} z$,
converges for $\operatorname{Re} s > 1$. Its meromorphic continuation $Z$ has only a simple pole
at $1$ of residue $\pi$, and $Z(0)=-1$.

The completed function $\Lambda$ agrees with $\pi^{-s}\Gamma(s) Z(s)$ where the factors are
regular, and continues across the negative integers. Its only poles are simple, at $0$ and $1$,
with residues $-1$ and $1$ respectively. Away from those poles, $\Lambda(s)=\Lambda(1-s)$.
The Lean functions need not take any particular value at their actual poles.

Source: C. L. Siegel, *Lectures on advanced analytic number theory*, TIFR Lectures on
Mathematics 23, Chapter 1, Theorem 3 (p. 47) and the binary specialization (p. 48). -/
theorem_wanted epsteinZeta_binary_functionalEquation (z : ℂ) (hz : 0 < z.im) :
    ∃ Z Λ : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re →
        HasSum (fun p : {p : ℤ × ℤ // p ≠ (0, 0)} ↦
          Complex.cpow ((Complex.normSq ((p.val.1 : ℂ) + (p.val.2 : ℂ) * z) / z.im : ℝ) : ℂ)
            (-s)) (Z s)) ∧
      (∀ s : ℂ, s ≠ 1 → AnalyticAt ℂ Z s) ∧
      Tendsto (fun s ↦ (s - 1) * Z s) (𝓝[≠] 1) (𝓝 (Real.pi : ℂ)) ∧
      Z 0 = -1 ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → AnalyticAt ℂ Λ s) ∧
      Tendsto (fun s ↦ s * Λ s) (𝓝[≠] 0) (𝓝 (-1)) ∧
      Tendsto (fun s ↦ (s - 1) * Λ s) (𝓝[≠] 1) (𝓝 1) ∧
      (∀ s : ℂ, s ≠ 1 → (∀ n : ℕ, s ≠ -(n : ℂ)) →
        Λ s = Complex.cpow (Real.pi : ℂ) (-s) * Complex.Gamma s * Z s) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ s = Λ (1 - s))

end MetaMathlibExt
