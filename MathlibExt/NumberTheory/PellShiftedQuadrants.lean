/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PellRotatedSquare
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Eventual quadrants of shifted Pell solutions

The real Pell coordinates both tend to infinity, so their four choices of signs eventually
place the shifted solutions in the corresponding closed quadrants.
-/

namespace MetaMathlibExt

open Filter
open scoped Topology

/-- **Shifted real Pell solutions eventually lie in the closed quadrants.** Let $D$ be an integer
and let $(\alpha, \beta)$ be a fundamental solution of $X^2 - DY^2 = 1$, that is, an integer
solution with $\alpha > 1$ and $\beta > 0$ such that $\alpha \le X$ for every integer solution
$(X, Y)$ with $X > 1$ (one exists only when $D$ is positive and not a square). For real $x$ let
$u(x) = ((\alpha + \beta\sqrt D)^x + (\alpha - \beta\sqrt D)^x)/2$ and
$v(x) = ((\alpha + \beta\sqrt D)^x - (\alpha - \beta\sqrt D)^x)/(2\sqrt D)$, and for integers $a$,
$b$ and signs $i, j \in \{1, -1\}$ let $R_{i,j}(x) = (i\,u(x) + a, j\,v(x) + b)$. Then there is a
real $x_0$ such that for every real $x \ge x_0$ the point $R_{1,1}(x)$ lies in the closed first
quadrant $\{X \ge 0, Y \ge 0\}$, $R_{-1,1}(x)$ in the closed second quadrant
$\{X \le 0, Y \ge 0\}$, $R_{-1,-1}(x)$ in the closed third quadrant $\{X \le 0, Y \le 0\}$ and
$R_{1,-1}(x)$ in the closed fourth quadrant $\{X \ge 0, Y \le 0\}$.

The points $R_{i,j}(x)$ are real solutions of the shifted Pell equation
$(X - a)^2 - D(Y - b)^2 = 1$. The printed statement of the source swaps the third and fourth
quadrants; this statement follows the reading of the source's proof.

Source: Kun Yi Ong and Eddie Shahril Bin Ismail, *Integer Solutions of Pell Equation in a Closed
Rotated Square Region*, INTEGERS 25 (2025), Article A112, Proposition 3.1
(`integers-2025-A112-prop-3-1`). -/
public theorem pell_shifted_real_solutions_eventually_in_quadrants {D : ℤ}
    {w : Pell.Solution₁ D} (hw : Pell.IsFundamental w) (a b : ℤ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      (0 ≤ pellU D w.x w.y x + a ∧ 0 ≤ pellV D w.x w.y x + b) ∧
      (-pellU D w.x w.y x + a ≤ 0 ∧ 0 ≤ pellV D w.x w.y x + b) ∧
      (-pellU D w.x w.y x + a ≤ 0 ∧ -pellV D w.x w.y x + b ≤ 0) ∧
      (0 ≤ pellU D w.x w.y x + a ∧ -pellV D w.x w.y x + b ≤ 0) := by
  have hD : 0 < (D : ℝ) := by exact_mod_cast hw.d_pos
  let ε : ℝ := w.x + w.y * Real.sqrt D
  have hε : 1 < ε := by
    have hx : 1 < (w.x : ℝ) := by exact_mod_cast hw.1
    have hy : 0 ≤ (w.y : ℝ) := by exact_mod_cast hw.2.1.le
    exact lt_add_of_lt_of_nonneg hx (mul_nonneg hy (Real.sqrt_nonneg _))
  have hconj : (w.x : ℝ) - w.y * Real.sqrt D = ε⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ (zero_lt_one.trans hε).ne').mp
    change (_ - _) * (_ + _) = 1
    rw [mul_comm, ← sq_sub_sq, mul_pow, Real.sq_sqrt hD.le, mul_comm _ (D : ℝ)]
    exact_mod_cast w.prop
  have hgrow := tendsto_rpow_atTop_of_base_gt_one ε hε
  have hdecay : Tendsto (fun x : ℝ => ((w.x : ℝ) - w.y * Real.sqrt D) ^ x) atTop (𝓝 0) := by
    simp only [hconj, Real.inv_rpow (zero_lt_one.trans hε).le]
    exact hgrow.inv_tendsto_atTop
  have hu : Tendsto (pellU D w.x w.y) atTop atTop :=
    (hgrow.atTop_add hdecay).atTop_div_const (by norm_num)
  have hv : Tendsto (pellV D w.x w.y) atTop atTop := by
    unfold pellV
    simpa only [sub_eq_add_neg] using
      (hgrow.atTop_add hdecay.neg).atTop_div_const (show 0 < 2 * Real.sqrt D by positivity)
  filter_upwards [hu.eventually_ge_atTop |(a : ℝ)|, hv.eventually_ge_atTop |(b : ℝ)|]
    with x hux hvx
  grind only [abs_le]

end MetaMathlibExt
