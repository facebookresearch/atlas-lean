/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Engineering.ZoneHeatInventory
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Thermal quadratic dissipation identity

## i. Overview

For a lumped thermal zone network with constant capacities `C i`,
reciprocal conductances `G i j = G j i`, boundary conductances
`g0 i` to a constant outside reference `Tout`, and zone equations
`C i * T' i = Σ j, G i j * (T j - T i) + g0 i * (Tout - T i) + P i`,
the quadratic functional `V = (1/2) * Σ i, C i * (T i - Tout) ^ 2`
(a quadratic functional of the temperature deviations; no sign
assumption on the capacities is made, so no Lyapunov positivity
is claimed) satisfies

`V' = -( (1/2) * Σ ij, G i j * (T j - T i) ^ 2
        + Σ i, g0 i * (T i - Tout) ^ 2 ) + Σ i, (T i - Tout) * P i`:

weighted edge-difference dissipation, boundary squares, and the
input power pairing. With no input power and nonnegative
conductances, `V` is nonincreasing along solutions.

## ii. Key results

- `ZoneHeatInventory.quadratic_dissipation_hasDerivAt`: the
  dissipation identity at one time, from the zone equations at that
  time.
- `ZoneHeatInventory.quadratic_dissipation_deriv`: the dissipation
  identity.
- `ZoneHeatInventory.quadratic_dissipation_nonpos`: nonpositive
  derivative without input power.
- `ZoneHeatInventory.quadratic_dissipation_antitone`: without
  input power, `V` is nonincreasing along solutions.

## iii. Table of contents

- A. The dissipation identity

## iv. References

- J. A. Clarke, *Energy Simulation in Building Design*,
  2nd edition, Butterworth-Heinemann, 2001, Chapter 3
  (lumped-capacitance zonal thermal networks and their
  RC-network equations). The dissipation identity is the
  quadratic energy balance of those network equations.
-/

@[expose] public section

namespace ZoneHeatInventory

/-! ## A. The dissipation identity -/

/-- Derivative of the quadratic thermal functional at one time `t`:
dissipation identity from the zone equations at `t` only. -/
theorem quadratic_dissipation_hasDerivAt {ι : Type*} [Fintype ι]
    (C : ι → ℝ) (G : ι → ι → ℝ) (g0 : ι → ℝ) (Tout : ℝ)
    (T Tv P : ι → ℝ → ℝ) (t : ℝ)
    (hG : ∀ i j, G i j = G j i)
    (hT : ∀ i, HasDerivAt (T i) (Tv i t) t)
    (hzone : ∀ i, C i * Tv i t
      = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout - T i t)
        + P i t) :
    HasDerivAt (fun s => (1 / 2) * ∑ i, C i * (T i s - Tout) ^ 2)
      (-((1 / 2) * ∑ i, ∑ j, G i j * (T j t - T i t) ^ 2
        + ∑ i, g0 i * (T i t - Tout) ^ 2)
        + ∑ i, (T i t - Tout) * P i t) t := by
  have hsub : ∀ i, HasDerivAt (fun s => T i s - Tout) (Tv i t) t :=
    fun i => (hT i).sub_const Tout
  have hsq : ∀ i, HasDerivAt (fun s => (T i s - Tout) ^ 2)
      (Tv i t * (T i t - Tout) + (T i t - Tout) * Tv i t) t := by
    intro i
    have h := (hsub i).mul (hsub i)
    have hfun : (fun s => T i s - Tout) * (fun s => T i s - Tout)
        = fun s => (T i s - Tout) ^ 2 := by
      funext s
      simp [pow_two, Pi.mul_apply]
    rw [hfun] at h
    exact h
  have hCi : ∀ i, HasDerivAt (fun s => C i * (T i s - Tout) ^ 2)
      (C i * (Tv i t * (T i t - Tout) + (T i t - Tout) * Tv i t)) t :=
    fun i => (hsq i).const_mul (C i)
  have hsum : HasDerivAt (fun s => ∑ i, C i * (T i s - Tout) ^ 2)
      (∑ i, C i * (Tv i t * (T i t - Tout) + (T i t - Tout) * Tv i t)) t :=
    HasDerivAt.fun_sum (fun i _ => hCi i)
  have hV : HasDerivAt (fun s => (1 / 2) * ∑ i, C i * (T i s - Tout) ^ 2)
      ((1 / 2) * ∑ i, C i * (Tv i t * (T i t - Tout) + (T i t - Tout) * Tv i t)) t :=
    hsum.const_mul (1 / 2)
  have hexch : (∑ i, (T i t - Tout) * (∑ j, G i j * (T j t - T i t)))
      = -((1 / 2) * ∑ i, ∑ j, G i j * (T j t - T i t) ^ 2) := by
    have hA : (∑ i, (T i t - Tout) * (∑ j, G i j * (T j t - T i t)))
        = ∑ i, ∑ j, (T i t - Tout) * (G i j * (T j t - T i t)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.mul_sum _ _ _
    rw [hA]
    have hpair : ∀ i j, (T i t - Tout) * (G i j * (T j t - T i t))
        + (T j t - Tout) * (G j i * (T i t - T j t))
        = -(G i j * (T j t - T i t) ^ 2) := by
      intro i j
      rw [hG j i]
      ring
    have hswap : (∑ i, ∑ j, (T i t - Tout) * (G i j * (T j t - T i t)))
        = ∑ i, ∑ j, (T j t - Tout) * (G j i * (T i t - T j t)) :=
      Finset.sum_comm
    have h2A : (∑ i, ∑ j, (T i t - Tout) * (G i j * (T j t - T i t)))
        + (∑ i, ∑ j, (T i t - Tout) * (G i j * (T j t - T i t)))
        = -(∑ i, ∑ j, G i j * (T j t - T i t) ^ 2) := by
      calc (∑ i, ∑ j, (T i t - Tout) * (G i j * (T j t - T i t)))
            + (∑ i, ∑ j, (T i t - Tout) * (G i j * (T j t - T i t)))
          = (∑ i, ∑ j, (T i t - Tout) * (G i j * (T j t - T i t)))
            + (∑ i, ∑ j, (T j t - Tout) * (G j i * (T i t - T j t))) := by
              rw [hswap]
        _ = ∑ i, ∑ j, ((T i t - Tout) * (G i j * (T j t - T i t))
            + (T j t - Tout) * (G j i * (T i t - T j t))) := by
            simp only [← Finset.sum_add_distrib]
        _ = ∑ i, ∑ j, (-(G i j * (T j t - T i t) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact hpair i j
        _ = -(∑ i, ∑ j, G i j * (T j t - T i t) ^ 2) := by
            simp only [Finset.sum_neg_distrib]
    calc (∑ i, ∑ j, (T i t - Tout) * (G i j * (T j t - T i t)))
        = (1 / 2) * ((∑ i, ∑ j, (T i t - Tout) * (G i j * (T j t - T i t)))
          + (∑ i, ∑ j, (T i t - Tout) * (G i j * (T j t - T i t)))) := by
          ring
      _ = (1 / 2) * (-(∑ i, ∑ j, G i j * (T j t - T i t) ^ 2)) := by
          rw [h2A]
      _ = -((1 / 2) * ∑ i, ∑ j, G i j * (T j t - T i t) ^ 2) := by
          ring
  have hbnd : (∑ i, (T i t - Tout) * (g0 i * (Tout - T i t)))
      = -(∑ i, g0 i * (T i t - Tout) ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum2 : (∑ i, C i * (Tv i t * (T i t - Tout) + (T i t - Tout) * Tv i t))
      = 2 * (∑ i, (T i t - Tout) * ((∑ j, G i j * (T j t - T i t))
        + g0 i * (Tout - T i t) + P i t)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc C i * (Tv i t * (T i t - Tout) + (T i t - Tout) * Tv i t)
        = 2 * ((T i t - Tout) * (C i * Tv i t)) := by ring
      _ = 2 * ((T i t - Tout) * ((∑ j, G i j * (T j t - T i t))
          + g0 i * (Tout - T i t) + P i t)) := by rw [hzone i]
  have hval : (1 / 2) * ∑ i, C i * (Tv i t * (T i t - Tout) + (T i t - Tout) * Tv i t)
      = -((1 / 2) * ∑ i, ∑ j, G i j * (T j t - T i t) ^ 2
        + ∑ i, g0 i * (T i t - Tout) ^ 2)
        + ∑ i, (T i t - Tout) * P i t := by
    calc (1 / 2) * ∑ i, C i * (Tv i t * (T i t - Tout) + (T i t - Tout) * Tv i t)
        = (1 / 2) * (2 * (∑ i, (T i t - Tout) * ((∑ j, G i j * (T j t - T i t))
          + g0 i * (Tout - T i t) + P i t))) := by rw [hsum2]
      _ = ∑ i, (T i t - Tout) * ((∑ j, G i j * (T j t - T i t))
          + g0 i * (Tout - T i t) + P i t) := by ring
      _ = (∑ i, (T i t - Tout) * (∑ j, G i j * (T j t - T i t)))
          + (∑ i, (T i t - Tout) * (g0 i * (Tout - T i t)))
          + (∑ i, (T i t - Tout) * P i t) := by
          simp only [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = -((1 / 2) * ∑ i, ∑ j, G i j * (T j t - T i t) ^ 2
          + ∑ i, g0 i * (T i t - Tout) ^ 2)
          + ∑ i, (T i t - Tout) * P i t := by
          rw [hexch, hbnd]
          ring
  rw [hval] at hV
  exact hV

/-- Derivative of the quadratic thermal functional: dissipation
identity. -/
theorem quadratic_dissipation_deriv {ι : Type*} [Fintype ι]
    (C : ι → ℝ) (G : ι → ι → ℝ) (g0 : ι → ℝ) (Tout : ℝ)
    (T Tv P : ι → ℝ → ℝ)
    (hG : ∀ i j, G i j = G j i)
    (hT : ∀ i t, HasDerivAt (T i) (Tv i t) t)
    (hzone : ∀ i t, C i * Tv i t
      = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout - T i t)
        + P i t)
    (t : ℝ) :
    HasDerivAt (fun s => (1 / 2) * ∑ i, C i * (T i s - Tout) ^ 2)
      (-((1 / 2) * ∑ i, ∑ j, G i j * (T j t - T i t) ^ 2
        + ∑ i, g0 i * (T i t - Tout) ^ 2)
        + ∑ i, (T i t - Tout) * P i t) t :=
  quadratic_dissipation_hasDerivAt C G g0 Tout T Tv P t hG (fun i => hT i t)
    (fun i => hzone i t)

/-- With no input power and nonnegative conductances, the
quadratic functional is nonincreasing along solutions: its
derivative is nonpositive. -/
theorem quadratic_dissipation_nonpos {ι : Type*} [Fintype ι]
    (C : ι → ℝ) (G : ι → ι → ℝ) (g0 : ι → ℝ) (Tout : ℝ)
    (T Tv : ι → ℝ → ℝ)
    (hG : ∀ i j, G i j = G j i)
    (hGnn : ∀ i j, 0 ≤ G i j) (hg0 : ∀ i, 0 ≤ g0 i)
    (hT : ∀ i t, HasDerivAt (T i) (Tv i t) t)
    (hzone : ∀ i t, C i * Tv i t
      = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout - T i t))
    (t : ℝ) :
    HasDerivAt (fun s => (1 / 2) * ∑ i, C i * (T i s - Tout) ^ 2)
      (-((1 / 2) * ∑ i, ∑ j, G i j * (T j t - T i t) ^ 2
        + ∑ i, g0 i * (T i t - Tout) ^ 2)) t
      ∧ -((1 / 2) * ∑ i, ∑ j, G i j * (T j t - T i t) ^ 2
        + ∑ i, g0 i * (T i t - Tout) ^ 2) ≤ 0 := by
  have hP0 : ∀ i t, C i * Tv i t
      = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout - T i t) + 0 := by
    intro i t
    rw [add_zero]
    exact hzone i t
  have hderiv :=
    quadratic_dissipation_deriv C G g0 Tout T Tv (fun _ _ => 0) hG hT hP0 t
  simp only [mul_zero, Finset.sum_const_zero, add_zero] at hderiv
  have hnn1 : 0 ≤ (1 / 2) * ∑ i, ∑ j, G i j * (T j t - T i t) ^ 2 := by
    refine mul_nonneg (by linarith) ?_
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (hGnn i j) (sq_nonneg _)
  have hnn2 : 0 ≤ ∑ i, g0 i * (T i t - Tout) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hg0 i) (sq_nonneg _)
  have hle : -((1 / 2) * ∑ i, ∑ j, G i j * (T j t - T i t) ^ 2
      + ∑ i, g0 i * (T i t - Tout) ^ 2) ≤ 0 := by
    have h := add_nonneg hnn1 hnn2
    linarith
  exact ⟨hderiv, hle⟩


/-- Without input power and with nonnegative conductances, the
quadratic functional is nonincreasing along solutions: its
derivative is everywhere the nonpositive dissipation. -/
theorem quadratic_dissipation_antitone {ι : Type*} [Fintype ι]
    (C : ι → ℝ) (G : ι → ι → ℝ) (g0 : ι → ℝ) (Tout : ℝ)
    (T Tv : ι → ℝ → ℝ)
    (hG : ∀ i j, G i j = G j i)
    (hGnn : ∀ i j, 0 ≤ G i j) (hg0 : ∀ i, 0 ≤ g0 i)
    (hT : ∀ i t, HasDerivAt (T i) (Tv i t) t)
    (hzone : ∀ i t, C i * Tv i t
      = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout - T i t)) :
    Antitone (fun s => (1 / 2) * ∑ i, C i * (T i s - Tout) ^ 2) := by
  apply antitone_of_deriv_nonpos
  · intro x
    exact (quadratic_dissipation_nonpos C G g0 Tout T Tv hG hGnn hg0
      hT hzone x).1.differentiableAt
  · intro x
    rw [(quadratic_dissipation_nonpos C G g0 Tout T Tv hG hGnn hg0
      hT hzone x).1.deriv]
    exact (quadratic_dissipation_nonpos C G g0 Tout T Tv hG hGnn hg0
      hT hzone x).2

end ZoneHeatInventory
