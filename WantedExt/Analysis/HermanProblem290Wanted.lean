/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Basic.Real.Basic
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

/-- Diophantine condition on a real number, in the standard inhomogeneous
approximation sense: some margin γ > 0 and exponent τ ≥ 0 bound
|α - p / q| from below by γ / q ^ (2 + τ) for all integers p and all
positive integers q.
Cites: Hayman (2018), Problem 2.90; https://arxiv.org/abs/1809.07200. -/
def IsDiophantine (α : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ ∃ τ : ℝ, 0 ≤ τ ∧ ∀ p : ℤ, ∀ q : ℕ, 1 ≤ q →
    γ / (q : ℝ) ^ (2 + τ) ≤ |α - (p : ℝ) / (q : ℝ)|

/-- Real-analytic orientation-preserving diffeomorphism of the circle,
modeled by its degree-one lift F : ℝ → ℝ to the universal cover.
Characteristic properties: analyticity of the lift and of the inverse lift,
degree-one periodicity F (x + 1) = F x + 1 (circle map), two-sided inverse
(diffeomorphism), and strict monotonicity (orientation-preserving).
Cites: Hayman (2018), Problem 2.90; https://arxiv.org/abs/1809.07200. -/
structure AnalyticCircleDiffeo where
  /-- The degree-one lift `ℝ → ℝ` of the circle diffeomorphism. -/
  toLift : ℝ → ℝ
  /-- The lift of the inverse diffeomorphism, a two-sided inverse of `toLift`. -/
  invLift : ℝ → ℝ
  analytic_to : AnalyticOn ℝ toLift Set.univ
  analytic_inv : AnalyticOn ℝ invLift Set.univ
  lift_periodic : ∀ x : ℝ, toLift (x + 1) = toLift x + 1
  inv_periodic : ∀ x : ℝ, invLift (x + 1) = invLift x + 1
  left_inv : ∀ x : ℝ, invLift (toLift x) = x
  right_inv : ∀ x : ℝ, toLift (invLift x) = x
  strictly_mono : StrictMono toLift

/-- Poincaré rotation number of a circle-map lift F : ℝ → ℝ: the mean motion
(F^[n] x - x) / n tends to α for every base point x.
Cites: Hayman (2018), Problem 2.90; https://arxiv.org/abs/1809.07200. -/
def HasRotationNumber (F : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ x : ℝ, Filter.Tendsto (fun n : ℕ => (F^[n] x - x) / (n : ℝ)) Filter.atTop (nhds α)

/-- Real-analytic conjugacy of a circle-map lift F to the rigid rotation by α:
there exists an analytic orientation-preserving circle diffeomorphism H whose
lift intertwines F with the translation y ↦ y + α, i.e. H ∘ F = R_α ∘ H.
Cites: Hayman (2018), Problem 2.90; https://arxiv.org/abs/1809.07200. -/
def IsAnalyticallyConjugateToRotation (F : ℝ → ℝ) (α : ℝ) : Prop :=
  ∃ H : AnalyticCircleDiffeo, ∀ x : ℝ, H.toLift (F x) = H.toLift x + α

/-- Hayman Problem 2.90 (M. R. Herman): does there exist an irrational number
α satisfying no diophantine condition such that every ℝ-analytic
orientation-preserving diffeomorphism of the circle with rotation number α
is ℝ-analytically conjugated to a rotation?
Cites: Hayman (2018), Problem 2.90; https://arxiv.org/abs/1809.07200. -/
def conjecture : Prop :=
  ∃ α : ℝ, Irrational α ∧ ¬ IsDiophantine α ∧
    ∀ F : AnalyticCircleDiffeo, HasRotationNumber F.toLift α →
      IsAnalyticallyConjugateToRotation F.toLift α

/--
Resolved true: Yoccoz (Analytic linearization of circle diffeomorphisms, LNM 1784, 2002)
characterized the Herman class H of rotation numbers for which every analytic circle
diffeomorphism is analytically linearizable and proved CD strictly contained in H; any alpha in
H minus CD is the required non-Diophantine number. Source: H. Eliasson, B. Fayad and R.
Krikorian, Jean-Christophe Yoccoz and the theory of circle diffeomorphisms (2018),
arXiv:1810.07107 (account of J.-C. Yoccoz, Analytic linearization of circle diffeomorphisms,
Lecture Notes in Math. 1784, Springer (2002), 125-173), https://arxiv.org/abs/1810.07107. Moved
from `OpenConjectures/Analysis/HermanProblem290`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.HermanProblem290Wanted
