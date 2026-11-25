/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

namespace MathlibExt.Analysis.DirichletSpacePolynomialDensityWanted

/-!
Clause list for [AMR-022-8011] Problem 8.11:
(a) functions analytic in |z| < 1; (b) finite Dirichlet integral;
(c) g is in D; (d) Pg (as defined in Problem 8.10) is dense in D;
(e) f is in D; (f) |f(z)| >= |g(z)| for all |z| < 1;
question: is Pf necessarily dense in D.
Density is in the Dirichlet norm
`‖u‖² = |u 0|² + ∫_{|z|<1} |u'(z)|²`, stated explicitly below rather
than via a topology on the subtype of all functions `ℂ → ℂ` (whose
inherited product topology would be the wrong one, and would make
values outside the disc matter). Membership `h ∈ Pg` likewise only
constrains values on the disc.
Context-only evidence (analogues in H^2 and A^2, Shields g = 1 case,
status/rights/difficulty metadata) is not formalized.
-/

/-- **The Dirichlet space.** The Dirichlet space $\mathcal{D}$ consists of the functions
$f : \mathbb{C} \to \mathbb{C}$ that are analytic on the open unit disc $\{z : |z| < 1\}$ and have
finite Dirichlet integral: $|f'|^2$ is integrable on the disc with respect to Lebesgue (area)
measure. The values of $f$ outside the disc are unconstrained.

Source: `AMR-022-8011` (Hayman, Research Problems in Function Theory (2018), Problem 8.11,
https://arxiv.org/abs/1809.07200). -/
abbrev DirichletSpace := { f : ℂ → ℂ // AnalyticOn ℂ f (Metric.ball (0 : ℂ) 1) ∧ MeasureTheory.IntegrableOn (fun z => ‖deriv f z‖ ^ 2) (Metric.ball (0 : ℂ) 1) MeasureTheory.volume }

/-- **Polynomial multiples of a function in the Dirichlet space.** For $g$ in the Dirichlet
space $\mathcal{D}$, the set $Pg$ consists of the functions $h \in \mathcal{D}$ for which there is
a polynomial $p$ with complex coefficients such that $h(z) = p(z) g(z)$ for all $|z| < 1$; only
values on the open unit disc are compared.

Source: `AMR-022-8011` (Hayman, Research Problems in Function Theory (2018), Problem 8.11, with
$Pg$ as defined in Problem 8.10), https://arxiv.org/abs/1809.07200. -/
def polyTimes (g : DirichletSpace) : Set DirichletSpace :=
  { h | ∃ p : Polynomial ℂ, ∀ z : ℂ, ‖z‖ < 1 → h.val z = p.eval z * g.val z }

/-- **Density in the Dirichlet norm.** A set $S$ of elements of the Dirichlet space $\mathcal{D}$
is dense in the Dirichlet norm when for every $u \in \mathcal{D}$ and every real $\varepsilon > 0$
there is $h \in S$ with
$$|h(0) - u(0)|^2 + \int_{|z| < 1} |h'(z) - u'(z)|^2 \, dA(z) < \varepsilon,$$
where $A$ is Lebesgue (area) measure on $\mathbb{C}$. -/
def IsDirichletDense (S : Set DirichletSpace) : Prop :=
  ∀ u : DirichletSpace, ∀ ε : ℝ, 0 < ε →
    ∃ h ∈ S, ‖h.val 0 - u.val 0‖ ^ 2 +
      (∫ z in Metric.ball (0 : ℂ) 1, ‖deriv h.val z - deriv u.val z‖ ^ 2
        ∂MeasureTheory.volume) < ε

/-- **Hayman's Problem 8.11: polynomial density under domination.** The statement that for all
$f$ and $g$ in the Dirichlet space $\mathcal{D}$: if the polynomial multiples $Pg$ are dense in
$\mathcal{D}$ in the Dirichlet norm and $|g(z)| \le |f(z)|$ for all $|z| < 1$, then the
polynomial multiples $Pf$ are also dense in $\mathcal{D}$ in the Dirichlet norm.

Source: the open question of `AMR-022-8011` (Hayman, Research Problems in Function Theory
(2018), Problem 8.11, https://arxiv.org/abs/1809.07200). -/
def conjecture : Prop :=
  ∀ (g f : DirichletSpace), IsDirichletDense (polyTimes g) → (∀ z : ℂ, ‖z‖ < 1 → ‖g.val z‖ ≤ ‖f.val z‖) → IsDirichletDense (polyTimes f)
/--
**Polynomial density passes to dominating functions in the Dirichlet space.** For all $f$ and $g$
in the Dirichlet space $\mathcal{D}$: if the polynomial multiples $Pg$ are dense in $\mathcal{D}$
in the Dirichlet norm and $|g(z)| \le |f(z)|$ for all $|z| < 1$, then the polynomial multiples
$Pf$ are dense in $\mathcal{D}$ in the Dirichlet norm. This answers Hayman's Problem 8.11
positively.

Resolved true: Richter and Sundberg (Michigan Math. J. 38 (1991) 355-379), and independently
Aleman, proved that in Dirichlet-type spaces $\mathcal{D}(\mu)$, including the classical Dirichlet
space, $|g| \le |f|$ with $g$ cyclic implies $f$ cyclic, where $g$ is cyclic when $Pg$ is dense
(restated in arXiv:2406.06182, Thm 5.12).

Source: Emmanuel
Fricain and Romain Lebreton, Cyclicity of the shift operator through Bezout identities,
arXiv:2406.06182 (2024), https://arxiv.org/abs/2406.06182. Moved from
`OpenConjectures/Analysis/DirichletSpacePolynomialDensity`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.DirichletSpacePolynomialDensityWanted
