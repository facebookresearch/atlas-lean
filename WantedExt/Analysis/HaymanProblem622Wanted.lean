/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hayman Problem 6.22: Sharp Convexity Radius for Starlike Order One Half
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace MathlibExt.Analysis.HaymanProblem622Wanted

/-! Source record `AMR-022-6022__2306022`. -/

/-!
# Clause inventory for AMR-022-6022, Hayman Problem 6.22

Question: largest radius where normalized starlike order one half implies convex,
with Carathéodory reformulation on circles.

- C1: unit disc as Metric.ball (0 : ℂ) 1, open.
- C2: f holomorphic on the unit disc via DifferentiableOn ℂ f.
- C3: normalization f 0 = 0 and deriv f 0 = 1 for z plus tail with n ≥ 2.
- C4: univalence via Set.InjOn f on the unit disc.
- C5: starlike order one half: (1/2 : ℝ) ≤ Re (z * f' / f) with z ≠ 0 and f z ≠ 0.
- C6: convexity on Metric.ball 0 r: 0 < Re (1 + z * f'' / f') with z ≠ 0 and f' ≠ 0.
- C7: radius r satisfies 0 < r and r ≤ 1, uniform over the class, one shared witness.
- C8: P holomorphic on the unit disc via DifferentiableOn, P 0 = 1, 0 < Re P on disc.
- C9: circle positivity strictly below r: for every s with 0 ≤ s and s < r,
  on Metric.sphere 0 s, 0 < Re ((P+1)/2 + z * P'/(P+1)).
  Strict min > 0 is asserted only below r, not attained at r; the union of
  smaller circles is the open disc, so this matches open-disc strength.
- C10: quantifiers: one shared r, all f in C2-C5, all P in C8, z in ball or sphere,
  s ranging over radii below r.
- C11: sharpness: r works for C6 and C9-below, and no larger r' ≤ 1 works for both
  below r' (negated conjunction, i.e. some class member fails at or above r).
  The value of r is not asserted.
-/

/-- **Conjecture: a sharp radius of convexity for starlike functions of order 1/2.** Let
$\mathbb{D}$ be the open unit disc in $\mathbb{C}$. Call $f : \mathbb{C} \to \mathbb{C}$ a
normalized starlike function of order $1/2$ if $f$ is holomorphic and injective on $\mathbb{D}$,
$f(0) = 0$, $f'(0) = 1$, and $\operatorname{Re}(z f'(z)/f(z)) \ge 1/2$ for every $z \in \mathbb{D}$
with $z \ne 0$ and $f(z) \ne 0$. Call $P : \mathbb{C} \to \mathbb{C}$ a Carathéodory function if
$P$ is holomorphic on $\mathbb{D}$, $P(0) = 1$, and $\operatorname{Re} P(z) > 0$ for every
$z \in \mathbb{D}$. Call a real number $\rho$ a good radius if
$\operatorname{Re}(1 + z f''(z)/f'(z)) > 0$ for every normalized starlike function $f$ of order
$1/2$ and every $z$ with $0 < |z| < \rho$ and $f'(z) \ne 0$, and
$\operatorname{Re}\big((P(z) + 1)/2 + z P'(z)/(P(z) + 1)\big) > 0$ for every Carathéodory
function $P$ and every $z$ with $|z| < \rho$. The conjecture is the proposition that there is a
good radius $r$ with $0 < r \le 1$ such that no real number $r'$ with $r < r' \le 1$ is a good
radius.

This is Problem 6.22 of Hayman, Research Problems in Function Theory (2018), source record
AMR-022-6022.

Source: https://arxiv.org/abs/1809.07200 -/
def conjecture : Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
    ((∀ f : ℂ → ℂ,
        DifferentiableOn ℂ f (Metric.ball (0 : ℂ) (1 : ℝ)) →
        f 0 = 0 →
        deriv f 0 = 1 →
        Set.InjOn f (Metric.ball (0 : ℂ) (1 : ℝ)) →
        (∀ z ∈ Metric.ball (0 : ℂ) (1 : ℝ), z ≠ 0 → f z ≠ 0 →
          (1 / 2 : ℝ) ≤ (z * deriv f z / f z).re) →
        ∀ z ∈ Metric.ball (0 : ℂ) r, z ≠ 0 → deriv f z ≠ 0 →
          0 < (1 + z * deriv (deriv f) z / deriv f z).re) ∧
      (∀ P : ℂ → ℂ,
        DifferentiableOn ℂ P (Metric.ball (0 : ℂ) (1 : ℝ)) →
        P 0 = 1 →
        (∀ z ∈ Metric.ball (0 : ℂ) (1 : ℝ), 0 < (P z).re) →
        ∀ s : ℝ, 0 ≤ s → s < r → ∀ z ∈ Metric.sphere (0 : ℂ) s,
          0 < ((P z + 1) / (2 : ℂ) + z * deriv P z / (P z + 1)).re)) ∧
    ∀ r' : ℝ, r < r' → r' ≤ 1 →
      ¬ ((∀ f : ℂ → ℂ,
        DifferentiableOn ℂ f (Metric.ball (0 : ℂ) (1 : ℝ)) →
        f 0 = 0 →
        deriv f 0 = 1 →
        Set.InjOn f (Metric.ball (0 : ℂ) (1 : ℝ)) →
        (∀ z ∈ Metric.ball (0 : ℂ) (1 : ℝ), z ≠ 0 → f z ≠ 0 →
          (1 / 2 : ℝ) ≤ (z * deriv f z / f z).re) →
        ∀ z ∈ Metric.ball (0 : ℂ) r', z ≠ 0 → deriv f z ≠ 0 →
          0 < (1 + z * deriv (deriv f) z / deriv f z).re) ∧
      (∀ P : ℂ → ℂ,
        DifferentiableOn ℂ P (Metric.ball (0 : ℂ) (1 : ℝ)) →
        P 0 = 1 →
        (∀ z ∈ Metric.ball (0 : ℂ) (1 : ℝ), 0 < (P z).re) →
        ∀ s : ℝ, 0 ≤ s → s < r' → ∀ z ∈ Metric.sphere (0 : ℂ) s,
          0 < ((P z + 1) / (2 : ℂ) + z * deriv P z / (P z + 1)).re))

/--
**A sharp radius of convexity for starlike functions of order 1/2 exists.** Let $\mathbb{D}$ be
the open unit disc in $\mathbb{C}$. Call $f : \mathbb{C} \to \mathbb{C}$ a normalized starlike
function of order $1/2$ if $f$ is holomorphic and injective on $\mathbb{D}$, $f(0) = 0$,
$f'(0) = 1$, and $\operatorname{Re}(z f'(z)/f(z)) \ge 1/2$ for every $z \in \mathbb{D}$ with
$z \ne 0$ and $f(z) \ne 0$. Call $P : \mathbb{C} \to \mathbb{C}$ a Carathéodory function if $P$
is holomorphic on $\mathbb{D}$, $P(0) = 1$, and $\operatorname{Re} P(z) > 0$ for every
$z \in \mathbb{D}$. Call a real number $\rho$ a good radius if
$\operatorname{Re}(1 + z f''(z)/f'(z)) > 0$ for every normalized starlike function $f$ of order
$1/2$ and every $z$ with $0 < |z| < \rho$ and $f'(z) \ne 0$, and
$\operatorname{Re}\big((P(z) + 1)/2 + z P'(z)/(P(z) + 1)\big) > 0$ for every Carathéodory
function $P$ and every $z$ with $|z| < \rho$. Then there is a good radius $r$ with
$0 < r \le 1$ such that no real $r'$ with $r < r' \le 1$ is a good radius.

MacGregor (Proc. AMS 14 (1963) 71-76, Theorem 1) proved that the sharp radius of convexity of
normalized starlike functions of order $1/2$ is $\sqrt{2\sqrt{3}-3} \approx 0.681$; this value is
such a radius $r$. The statement above does not assert the value of $r$.

Source: B. Bhowmik and
S. Biswas, Radius of convexity of certain classes of functions defined by convolution, preprint
(2026), arXiv:2606.20872, https://arxiv.org/abs/2606.20872. Moved from
`OpenConjectures/Analysis/HaymanProblem622`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.HaymanProblem622Wanted
