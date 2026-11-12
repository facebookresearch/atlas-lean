/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.ExpectedUtility.VonNeumannMorgenstern
public import Mathlib.Analysis.Convex.Function

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Fair full insurance is optimal for a risk-averse agent

States form a finite type `X` with probabilities `p : Convexity.StdSimplex ℝ X`, and
`expectedUtility` is the one of `MathlibExt.Economics.ExpectedUtility.VonNeumannMorgenstern`. An
agent with wealth `w` suffers the loss `ℓ x` in state `x`. In a complete insurance market every
indemnity schedule `I : X → ℝ` can be bought at the actuarially fair premium `E_p[I]`, giving final
wealth `insuredWealth p w ℓ I x = w - ℓ x + I x - E_p[I]`. Every contract leaves mean wealth
`w - E_p[ℓ]`, and full insurance (`I = ℓ`) pays it for sure, so finite Jensen
(`ConcaveOn.le_map_sum`) shows that a risk-averse agent (concave Bernoulli utility) weakly prefers
full insurance to every fairly priced contract. Monotonicity of the utility is not needed.

## Main results

* `insuredWealth_self`: full insurance at the fair premium removes all risk.
* `expectedUtility_insuredWealth_le_full`: fair full insurance is optimal.

## References

* J. Mossin, "Aspects of rational insurance purchasing", Journal of Political Economy 76 (1968),
  553--568.
* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), Section 6.C (insurance example).
-/

namespace MathlibExt.Economics.Risk

open Convexity MathlibExt.Economics.ExpectedUtility

/-- Final wealth in state `x` of an agent with initial wealth `w` who suffers the loss `ℓ x` and
holds the insurance contract paying the indemnity `I x`, bought at the actuarially fair premium
`E_p[I]`: `w - ℓ x + I x - E_p[I]`. Every indemnity schedule `I : X → ℝ` is available (complete
insurance market); full insurance is `I = ℓ`. -/
def insuredWealth {X : Type*} [Fintype X] (p : StdSimplex ℝ X) (w : ℝ) (ℓ I : X → ℝ) (x : X) :
    ℝ :=
  w - ℓ x + I x - expectedUtility I p

/-- Under full insurance at the fair premium, final wealth is the sure amount `w - E_p[ℓ]`. -/
theorem insuredWealth_self {X : Type*} [Fintype X] (p : StdSimplex ℝ X) (w : ℝ) (ℓ : X → ℝ)
    (x : X) : insuredWealth p w ℓ ℓ x = w - expectedUtility ℓ p := by
  unfold insuredWealth
  ring

/-- **Fair full insurance is optimal.** For a risk-averse agent (Bernoulli utility `u` concave on
a convex set `S` of wealth levels), any fairly priced indemnity schedule `I` whose final wealth
stays in `S` gives expected utility at most that of full insurance. -/
theorem expectedUtility_insuredWealth_le_full {X : Type*} [Fintype X] {S : Set ℝ} {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ S u) (p : StdSimplex ℝ X) (w : ℝ) (ℓ I : X → ℝ)
    (hS : ∀ x, insuredWealth p w ℓ I x ∈ S) :
    expectedUtility (u ∘ insuredWealth p w ℓ I) p ≤
      expectedUtility (u ∘ insuredWealth p w ℓ ℓ) p := by
  have hsum : ∑ x, p.weights x = 1 := StdSimplex.total_of_fintype p
  have h₀ : ∀ i ∈ Finset.univ, 0 ≤ p.weights i := fun i _ => p.nonneg i
  have h₁ : ∑ i ∈ Finset.univ, p.weights i = 1 := hsum
  have hmem : ∀ i ∈ Finset.univ, insuredWealth p w ℓ I i ∈ S := fun i _ => hS i
  have hJ := hu.le_map_sum (t := Finset.univ) (w := p.weights)
    (p := insuredWealth p w ℓ I) h₀ h₁ hmem
  simp only [smul_eq_mul] at hJ
  have hLHS : (∑ i ∈ Finset.univ, p.weights i * u (insuredWealth p w ℓ I i)) =
      expectedUtility (u ∘ insuredWealth p w ℓ I) p := by
    simp [expectedUtility]
  have hmean : (∑ i ∈ Finset.univ, p.weights i * insuredWealth p w ℓ I i) =
      w - expectedUtility ℓ p := by
    have hexpand : ∀ x : X, p.weights x * insuredWealth p w ℓ I x =
        p.weights x * w - p.weights x * ℓ x + p.weights x * I x -
          p.weights x * expectedUtility I p := by
      intro x
      unfold insuredWealth
      ring
    simp_rw [hexpand]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hw : ∑ x ∈ Finset.univ, p.weights x * w = w := by
      rw [← Finset.sum_mul, h₁, one_mul]
    have hE : ∑ x ∈ Finset.univ, p.weights x * expectedUtility I p =
        expectedUtility I p := by
      rw [← Finset.sum_mul, h₁, one_mul]
    have hℓ : ∑ x ∈ Finset.univ, p.weights x * ℓ x = expectedUtility ℓ p := by
      simp [expectedUtility]
    have hI : ∑ x ∈ Finset.univ, p.weights x * I x = expectedUtility I p := by
      simp [expectedUtility]
    rw [hw, hℓ, hI, hE]
    ring
  have hRHS : expectedUtility (u ∘ insuredWealth p w ℓ ℓ) p =
      u (w - expectedUtility ℓ p) := by
    have hterm : ∀ x : X, p.weights x * (u ∘ insuredWealth p w ℓ ℓ) x =
        p.weights x * u (w - expectedUtility ℓ p) := by
      intro x
      simp only [Function.comp_apply]
      rw [insuredWealth_self]
    simp only [expectedUtility, hterm]
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [hLHS, hmean] at hJ
  rwa [hRHS]

end MathlibExt.Economics.Risk
