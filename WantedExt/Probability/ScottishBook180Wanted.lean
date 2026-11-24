/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

namespace MathlibExt.Probability.ScottishBook180Wanted

/-- **Stationary random functions (Slutsky–Khinchin).** Let $\mu$ be a measure on a measurable
space $\Omega$, and let $v$ assign to each real $t$ a function $v_t : \Omega \to \mathbb{R}$.
Then $v$ is stationary if there are a real number $c$ and a function $R : \mathbb{R} \to \mathbb{R}$
such that for all real $t$ and $h$, $\int v_t \, d\mu = 0$, $\int v_t^2 \, d\mu = c$ and
$\int v_t \, v_{t+h} \, d\mu = R(h)$.

The integrals are Bochner integrals, which are $0$ for non-integrable functions, so integrability
of $v_t$, $v_t^2$ and $v_t v_{t+h}$ is not required. -/
def IsStationary (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (v : ℝ → Ω → ℝ) : Prop :=
  ∃ (c : ℝ) (R : ℝ → ℝ),
    (∀ t : ℝ, ∫ ω, v t ω ∂μ = 0) ∧
    (∀ t : ℝ, ∫ ω, (v t ω) ^ 2 ∂μ = c) ∧
    ∀ t h : ℝ, ∫ ω, v t ω * v (t + h) ω ∂μ = R h

/-- **Scottish Book Problem 180 (Kampé de Fériet's claim).** The claim that for every probability
space $(\Omega, \mu)$ that carries a measurable random variable $U : \Omega \to \mathbb{R}$
uniformly distributed on $[0, 1]$, and every stationary random function $v$ on $\Omega$ (in the
sense of Slutsky and Khinchin) such that each $v_t : \Omega \to \mathbb{R}$ is measurable, there
exist a measurable random variable $A : \Omega \to \mathbb{R}$ uniformly distributed on $[0, 1]$
and a map $\varphi : \mathbb{R} \to \Omega$ such that $A(\varphi(\alpha)) = \alpha$ for every
$\alpha \in [0, 1]$, and such that for all real $t_1 \ne t_2$ the functions
$\alpha \mapsto v_{t_1}(\varphi(\alpha))$ and $\alpha \mapsto v_{t_2}(\varphi(\alpha))$ are
independent with respect to Lebesgue measure on $[0, 1]$.

Here a variable is uniformly distributed on $[0, 1]$ when its law is Lebesgue measure restricted
to $[0, 1]$. The equation $A(\varphi(\alpha)) = \alpha$ is condition (1) of the problem and the
independence, in the sense of Steinhaus, is condition (2). The existence of $U$ is an added
hypothesis; it rules out refutations that only exploit a space carrying no uniform variable. -/
def ScottishBookProblem180Claim : Prop :=
  ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω),
    MeasureTheory.IsProbabilityMeasure μ →
    (∃ U : Ω → ℝ, Measurable U ∧
      MeasureTheory.Measure.map U μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) →
    ∀ v : ℝ → Ω → ℝ, (∀ t, Measurable (v t)) → IsStationary Ω μ v →
    ∃ (A : Ω → ℝ) (φ : ℝ → Ω), Measurable A ∧
      MeasureTheory.Measure.map A μ =
        MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1) ∧
      (∀ α : ℝ, α ∈ Set.Icc (0 : ℝ) 1 → A (φ α) = α) ∧
      ∀ t₁ t₂ : ℝ, t₁ ≠ t₂ →
        ProbabilityTheory.IndepFun (fun α => v t₁ (φ α))
          (fun α => v t₂ (φ α))
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))

/--
**Scottish Book Problem 180 fails.** The claim of Scottish Book Problem 180 is false: there are a
probability space $(\Omega, \mu)$ carrying a measurable random variable uniformly distributed on
$[0, 1]$ and a stationary random function $v$ on $\Omega$ with every $v_t$ measurable, such that
no measurable random variable $A : \Omega \to \mathbb{R}$ uniformly distributed on $[0, 1]$ and no
map $\varphi : \mathbb{R} \to \Omega$ satisfy both $A(\varphi(\alpha)) = \alpha$ for every
$\alpha \in [0, 1]$ and, for all real $t_1 \ne t_2$, the independence of
$\alpha \mapsto v_{t_1}(\varphi(\alpha))$ and $\alpha \mapsto v_{t_2}(\varphi(\alpha))$ with
respect to Lebesgue measure on $[0, 1]$.

A counterexample is $\Omega = \mathbb{R}$ with $\mu$ Lebesgue measure restricted to $[0, 1]$, the
identity as uniform variable, and $v_t(\omega) = \omega - 1/2$ for every $t$, which is stationary
with $c = R(h) = 1/12$. If $A$ and $\varphi$ existed, $\varphi$ would be injective on $[0, 1]$,
while both functions in the independence condition equal $f(\alpha) = \varphi(\alpha) - 1/2$. A
function independent of itself is almost everywhere constant, and an injective function on
$[0, 1]$ is not. No non-degeneracy hypothesis is added, since the source asks for none.

Source: J. Kampe de Feriet, Problem 180 of the Scottish Book,
typescript PDF pp. 82-83, printed pp. 79-80; see the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem_wanted scottishBook180_refuted : ¬ ScottishBookProblem180Claim

end MathlibExt.Probability.ScottishBook180Wanted
