/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.ConvexSubGaussianComparison
public import MathlibExt.Probability.ConvexSubGaussianComparisonFiniteness
public import MathlibExt.Probability.ConvexSubGaussianComparisonDavisPowerSystemExistsUnique

/-!
# Sharp one-dimensional convex sub-Gaussian comparison: literature requests

All four results below are unproved data, not proofs. The implemented probability
model and characteristic APIs are upstream. The numerical approximations in Davis–Power
Remark 2 are not asserted here, and the solved one-dimensional problem is not an open target.
The finiteness of the comparison constant is proved in
`MathlibExt.Probability.ConvexSubGaussianComparisonFiniteness`, and the existence and
uniqueness of the Davis–Power system solution (`davisPowerSystem_existsUnique`) is proved in
`MathlibExt.Probability.ConvexSubGaussianComparisonDavisPowerSystemExistsUnique`, where the
Davis–Power equation data it uses is defined.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.ConvexSubGaussianComparison

-- The Davis–Power constant `c_0` (Davis–Power 2026, equation (6)), kept with its owning
-- literature requests; the equation data it is defined from is in
-- `MathlibExt.Probability.ConvexSubGaussianComparisonDavisPowerSystemExistsUnique`.
namespace MathlibExt.Probability.ConvexSubGaussianComparisonWantedDavis

open Set

/-- **Values of $c_0$ solving the Davis–Power system.** Let $\varphi(t) = e^{-t^2/2}/\sqrt{2\pi}$
be the standard Gaussian density, $B = \frac12 \int_0^\infty \min(1, 2e^{-t^2/2})\,dt$ and
$h(x) = 2x e^{-x^2/2} + 2\int_x^\infty e^{-t^2/2}\,dt$. This is the set of reals $c_0$ for which
there are reals $a$, $p_0$, $z$ with $a > \sqrt{2 \log 2}$, $h(a) = B$, $p_0 = 2e^{-a^2/2}$,
$0 < p_0 < 1$, $\int_z^\infty \varphi(t)\,dt = p_0$ and $c_0 = B / \varphi(z)$. -/
noncomputable def davisPowerC0Values : Set ℝ :=
  {c | ∃ q : DavisPowerSolution, q.IsValid ∧ q.c0 = c}

/-- **The Davis–Power constant $c_0$.** Let $\varphi(t) = e^{-t^2/2}/\sqrt{2\pi}$ be the standard
Gaussian density, $B = \frac12 \int_0^\infty \min(1, 2e^{-t^2/2})\,dt$ and
$h(x) = 2x e^{-x^2/2} + 2\int_x^\infty e^{-t^2/2}\,dt$. The constant $c_0$ is the infimum of the
set of reals $c$ for which there are reals $a$, $p_0$, $z$ with $a > \sqrt{2 \log 2}$, $h(a) = B$,
$p_0 = 2e^{-a^2/2}$, $0 < p_0 < 1$, $\int_z^\infty \varphi(t)\,dt = p_0$ and $c = B / \varphi(z)$.
The infimum of a set of reals that is empty or unbounded below is taken to be $0$.

If the system has exactly one solution $(a, p_0, z, c)$, then $c_0 = c$. The constant is defined
from the equation system, not from numerical data. -/
noncomputable def davisPowerC0 : ℝ :=
  sInf davisPowerC0Values

theorem davisPowerC0Values_eq_singleton {q : DavisPowerSolution}
    (hq : q.IsValid) (hunique : ∀ r : DavisPowerSolution, r.IsValid → r = q) :
    davisPowerC0Values = {q.c0} := by
  ext c
  constructor
  · rintro ⟨r, hr, hrc⟩
    simpa [hunique r hr] using hrc.symm
  · intro hc
    exact ⟨q, hq, (mem_singleton_iff.mp hc).symm⟩

theorem davisPowerC0_eq_of_unique_solution {q : DavisPowerSolution}
    (hq : q.IsValid) (hunique : ∀ r : DavisPowerSolution, r.IsValid → r = q) :
    davisPowerC0 = q.c0 := by
  rw [davisPowerC0, davisPowerC0Values_eq_singleton hq hunique, csInf_singleton]

end MathlibExt.Probability.ConvexSubGaussianComparisonWantedDavis

open MathlibExt.Probability.ConvexSubGaussianComparisonWantedDavis

namespace MathlibExt.Probability.ConvexSubGaussianComparisonWanted

/-- **Davis–Power upper bound: $c_0^2$ is an admissible variance factor.** Let $c_0$ be the
Davis–Power constant and $G$ a standard Gaussian. Then $c_0^2 > 0$, and every real random
variable $X$ on a probability space that is measurable and integrable, has mean $0$ and satisfies
$\mathbb{P}(|X| > t) \le 2e^{-t^2/2}$ for all $t \ge 0$ is dominated by $|c_0|\,G$ in the convex
order. Here a real random variable $X$ is dominated by $Y$ in the convex order when
$\mathbb{E} f(X) \le \mathbb{E} f(Y)$ for every convex $f : \mathbb{R} \to \mathbb{R}$ such that
$f(X)$ and $f(Y)$ are integrable.

Source: Davis–Power (2026), Theorem 1, the exact `c0^2` comparator upper bound. -/
public theorem_wanted davisPowerSharpUpper :
    IsAdmissibleConstant (ENNReal.ofReal (davisPowerC0 ^ 2))

/-- **Davis–Power lower bound for admissible variance factors.** Every admissible variance factor
$C \in [0, \infty]$ satisfies $c_0^2 \le C$, where $c_0$ is the Davis–Power constant. Here $C$ is
admissible when $0 < C < \infty$ and every real random variable $X$ on a probability space that
is measurable and integrable, has mean $0$ and satisfies $\mathbb{P}(|X| > t) \le 2e^{-t^2/2}$ for
all $t \ge 0$ is dominated by $\sqrt{C}\,G$ in the convex order, with $G$ a standard Gaussian;
a real random variable $X$ on a probability space is dominated by $Y$ in the convex order when
$\mathbb{E} f(X) \le \mathbb{E} f(Y)$ for every convex $f : \mathbb{R} \to \mathbb{R}$ such that
$f(X)$ and $f(Y)$ are integrable.

Source: Davis–Power (2026), Theorem 1, sharpness for every admissible variance factor. -/
public theorem_wanted davisPowerSharpLower (C : ENNReal) (hC : IsAdmissibleConstant C) :
    ENNReal.ofReal (davisPowerC0 ^ 2) ≤ C

/-- **Davis–Power value of the convex sub-Gaussian comparison constant.** The convex
sub-Gaussian comparison constant, the infimum in $[0, \infty]$ of all admissible variance factors,
equals $c_0^2$, where $c_0$ is the Davis–Power constant.

Source: Davis–Power (2026), the exact solved one-dimensional catalogue constant. -/
public theorem_wanted comparisonConstant_eq_davisPowerC0_sq :
    comparisonConstant = ENNReal.ofReal (davisPowerC0 ^ 2)

/-- **Davis–Power extremal variable.** Let $c_0$ be the Davis–Power constant and $G$ a standard
Gaussian, and say that a real random variable $X$ is dominated by $Y$ in the convex order when
$\mathbb{E} f(X) \le \mathbb{E} f(Y)$ for every convex $f : \mathbb{R} \to \mathbb{R}$ such that
$f(X)$ and $f(Y)$ are integrable. There is a real random variable $X$ on a probability space that
is measurable and integrable, has mean $0$ and satisfies $\mathbb{P}(|X| > t) \le 2e^{-t^2/2}$ for
all $t \ge 0$, whose tail saturates the capped envelope,
$\mathbb{P}(|X| > t) = \min(1, 2e^{-t^2/2})$ for every $t \ge 0$, and such that for every real $c$
with $0 < c < c_0$, $X$ is not dominated by $cG$ in the convex order.

Source: Davis–Power (2026), the tail-saturating extremizer and smaller-factor sharpness. -/
public theorem_wanted davisPowerExtremalAttainment :
    ∃ (Ω : Type) (m : MeasurableSpace Ω)
      (μ : @Measure Ω m) (hμ : @IsProbabilityMeasure Ω m μ) (X : Ω → ℝ),
      @IsOneSubGaussianTail Ω m μ hμ X ∧ SaturatesGaussianTail μ X ∧
        ∀ c : ℝ, 0 < c → c < davisPowerC0 →
          ¬ConvexDominated μ X (gaussianReal 0 1) (fun g : ℝ => c * g)

end MathlibExt.Probability.ConvexSubGaussianComparisonWanted
