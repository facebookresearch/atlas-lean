/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Basic

@[expose] public section

namespace MathlibExt.Analysis.HermanProblem290Wanted

/-!
# Research Problems in Function Theory — Problem 2.90

Source: Hayman, Research Problems in Function Theory (2018), Problem 2.90
(M. R. Herman). Source URL: https://arxiv.org/abs/1809.07200.

Clause list from the source (every item appears in the formal text below):
1. quantifier domain of the unknown: α ranges over ℝ.
2. α is irrational: α ∈ ℝ ∖ ℚ.
3. α does not satisfy a diophantine condition.
4. quantified objects f are diffeomorphisms of the circle (bijective with
  two-sided inverse lifts, modeled via degree-one lifts F : ℝ → ℝ with
  F (x + 1) = F x + 1).
5. each f is ℝ-analytic (lift and inverse lift are analytic on all of ℝ).
6. each f is orientation-preserving (lift is strictly monotone increasing).
7. each f has rotation number α (Poincaré mean-motion limit equals α).
8. the conjugacy h is ℝ-analytic (witness is an analytic circle diffeomorphism).
9. the conjugacy target is a (rigid) rotation (lift y ↦ y + α).
10. main quantifiers: existence of one α such that every such f is
  ℝ-analytically conjugated to the rotation.
Context only (not a formal target): if α satisfies a diophantine condition,
the global analytic conjugacy theorem holds (Herman, Yoccoz).
-/

/-- **Diophantine numbers.** A real number $\alpha$ is Diophantine when there are real numbers
$\gamma > 0$ and $\tau \ge 0$ such that $|\alpha - p/q| \ge \gamma / q^{2 + \tau}$ for every
integer $p$ and every integer $q \ge 1$.

Source: Hayman (2018), Problem 2.90; https://arxiv.org/abs/1809.07200. -/
def IsDiophantine (α : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∃ τ : ℝ, 0 ≤ τ ∧ ∀ p : ℤ, ∀ q : ℕ, 1 ≤ q →
    γ / (q : ℝ) ^ (2 + τ) ≤ |α - (p : ℝ) / (q : ℝ)|

/-- **Real-analytic circle diffeomorphisms.** A real-analytic orientation-preserving
diffeomorphism of the circle is given by a lift $F : \mathbb{R} \to \mathbb{R}$ together with an
inverse lift $G : \mathbb{R} \to \mathbb{R}$, both real-analytic on all of $\mathbb{R}$, such that
for every real $x$ we have $F(x + 1) = F(x) + 1$, $G(x + 1) = G(x) + 1$, $G(F(x)) = x$ and
$F(G(x)) = x$, and $F$ is strictly increasing.

Source: Hayman (2018), Problem 2.90; https://arxiv.org/abs/1809.07200. -/
structure AnalyticCircleDiffeo where
  toLift : ℝ → ℝ
  invLift : ℝ → ℝ
  analytic_to : AnalyticOn ℝ toLift Set.univ
  analytic_inv : AnalyticOn ℝ invLift Set.univ
  lift_periodic : ∀ x : ℝ, toLift (x + 1) = toLift x + 1
  inv_periodic : ∀ x : ℝ, invLift (x + 1) = invLift x + 1
  left_inv : ∀ x : ℝ, invLift (toLift x) = x
  right_inv : ∀ x : ℝ, toLift (invLift x) = x
  strictly_mono : StrictMono toLift

/-- **Rotation number of a lift.** Let $F : \mathbb{R} \to \mathbb{R}$ be a function, and for a
natural number $n$ write $F^n$ for the $n$-th iterate of $F$. Then $F$ has rotation number
$\alpha \in \mathbb{R}$ when, for every real $x$, $(F^n(x) - x)/n$ tends to $\alpha$ as $n$ tends
to infinity.

Source: Hayman (2018), Problem 2.90; https://arxiv.org/abs/1809.07200. -/
def HasRotationNumber (F : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ x : ℝ, Filter.Tendsto (fun n : ℕ => (F^[n] x - x) / (n : ℝ)) Filter.atTop (nhds α)

/-- **Analytic conjugacy to a rotation.** A function $F : \mathbb{R} \to \mathbb{R}$ is
analytically conjugate to the rotation by $\alpha \in \mathbb{R}$ when there is a real-analytic
circle diffeomorphism with lift $H$ such that $H(F(x)) = H(x) + \alpha$ for every real $x$.

Source: Hayman (2018), Problem 2.90; https://arxiv.org/abs/1809.07200. -/
def IsAnalyticallyConjugateToRotation (F : ℝ → ℝ) (α : ℝ) : Prop :=
  ∃ H : AnalyticCircleDiffeo, ∀ x : ℝ, H.toLift (F x) = H.toLift x + α

/-- **Herman's analytic linearization problem.** The statement that there is an irrational real
number $\alpha$ that is not Diophantine such that, for every real-analytic circle diffeomorphism
whose lift $F$ has rotation number $\alpha$, $F$ is analytically conjugate to the rotation by
$\alpha$.

M. R. Herman asked whether such an $\alpha$ exists; this is Problem 2.90 in Hayman's list.

Source: Hayman (2018), Problem 2.90; https://arxiv.org/abs/1809.07200. -/
def conjecture : Prop :=
  ∃ α : ℝ, Irrational α ∧ ¬ IsDiophantine α ∧
    ∀ F : AnalyticCircleDiffeo, HasRotationNumber F.toLift α →
      IsAnalyticallyConjugateToRotation F.toLift α

/--
**Herman's analytic linearization problem has a positive answer.** There is an irrational real
number $\alpha$ that is not Diophantine such that, for every real-analytic circle diffeomorphism
whose lift $F$ has rotation number $\alpha$, $F$ is analytically conjugate to the rotation by
$\alpha$.

Yoccoz characterized the Herman class $\mathcal{H}$ of rotation numbers $\alpha$ for which every
real-analytic circle diffeomorphism with rotation number $\alpha$ is analytically linearizable,
and proved that $\mathcal{H}$ strictly contains the set of Diophantine numbers; any $\alpha$ in
$\mathcal{H}$ that is not Diophantine has the required property.

Source: H. Eliasson, B. Fayad and R.
Krikorian, Jean-Christophe Yoccoz and the theory of circle diffeomorphisms (2018),
arXiv:1810.07107 (account of J.-C. Yoccoz, Analytic linearization of circle diffeomorphisms,
Lecture Notes in Math. 1784, Springer (2002), 125-173), https://arxiv.org/abs/1810.07107. Moved
from `OpenConjectures/Analysis/HermanProblem290`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.HermanProblem290Wanted
