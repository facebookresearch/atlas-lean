/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Periodic staggered-grid energy stability of the leapfrog update

## i. Overview

On a periodic grid of `N` cells with spacing `h`, this module studies
the staggered leapfrog update from
`MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil`. For a pair
`(u, v)` of grid functions it defines the squared weighted grid norm
`weightedNormSq`, the squared pair norm `pairNormSq` and its square
root `pairNorm`, the scaled forward difference
`scaledForwardDifference` given by `A = c * dt * Dplus`, and the
quadratic energy
`Q(u, v) = normSq(u) + normSq(v) - inner(u, A * v)`, where `inner` is
the weighted inner product of the stencil module. It also defines
`leapfrogIterate`, the iterates of the update from an initial pair.

The one-step invariance proof expands the weighted norms of the two
components of the update and cancels the cross terms, using the
identity for the weighted inner product against the forward
difference obtained from the transposed difference matrix. The
coercivity proof bounds that cross term by weighted Cauchy-Schwarz
together with a bound on the weighted norm of the forward difference,
which gives the trap between `(1 - rho)` and `(1 + rho)` times the
squared pair norm under the Courant bound `c * dt / h <= rho`; the
lower bound is coercive when `rho < 1`.
The bound for every iterate follows by combining exact preservation
of the energy at each step with the trap at the initial and current
pairs. At Courant number at least one on an even grid, the alternating
grid mode makes the energy nonpositive on a nonzero pair, so no
positive coercivity constant exists there.

## ii. Key results

- `yeeEnergy_zero`: the energy of the zero pair is zero.
- `pairNormSq_nonneg`: the squared pair norm is nonnegative at a
  positive grid spacing.
- `leapfrogStep_yeeEnergy`: one leapfrog step preserves the energy
  exactly.
- `yeeEnergy_pairNormSq_bounds`: under the Courant bound
  `c * dt / h ≤ rho`, the energy is trapped between `(1 - rho)` and
  `(1 + rho)` times the squared pair norm (coercive when `rho < 1`).
- `staggeredLeapfrog_energyStable`: one-step energy preservation
  together with the two-sided trap.
- `leapfrogIterate_yeeEnergy`: every iterate has the same energy as
  the initial pair.
- `leapfrogIterate_pairNorm_le`: every iterate has pair norm at most
  `sqrt((1 + rho) / (1 - rho))` times the initial pair norm.
- `no_positive_coercivity_of_courant_ge_one`: at Courant number at
  least one on an even grid, no positive constant traps the energy
  below by the squared pair norm.

## iii. Table of contents

- A. Grid norms, scaled difference and energy
- B. Auxiliary identities
- C. Energy invariance and coercivity
- D. All iterates
- E. Courant boundary

## iv. References

- K. S. Yee, Numerical solution of initial boundary value problems
  involving Maxwell's equations in isotropic media, *IEEE
  Transactions on Antennas and Propagation* 14 (1966), no. 3,
  302-307.
- A. Taflove and S. C. Hagness, *Computational Electrodynamics: The
  Finite-Difference Time-Domain Method*, 3rd ed., Artech House, 2005,
  Chapter 3.
-/

@[expose] public section

open Matrix

namespace MathlibExt.Analysis.Numerical.PeriodicYeeEnergy

open MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil

/-! ## A. Grid norms, scaled difference and energy -/

/-- Weighted sum of squares `h * ∑ⱼ wⱼ²`, defined for every `h`; for `0 ≤ h` it is the square
of the weighted grid norm, and for `h < 0` it can be negative. -/
def weightedNormSq {N : ℕ} (h : ℝ) (w : Fin N → ℝ) : ℝ :=
  weightedInner h w w

/-- Squared pair norm: the sum of the two squared grid norms. -/
def pairNormSq {N : ℕ} (h : ℝ) (u v : Fin N → ℝ) : ℝ :=
  weightedNormSq h u + weightedNormSq h v

/-- Pair norm: the square root of the squared pair norm. For `h ≥ 0` this is `√h` times the
Euclidean norm of the concatenated vector `(u, v)`, not a product maximum norm. -/
noncomputable def pairNorm {N : ℕ} (h : ℝ) (u v : Fin N → ℝ) : ℝ :=
  Real.sqrt (pairNormSq h u v)

/-- The scaled forward difference `A = c * dt * Dplus`. -/
noncomputable def scaledForwardDifference {N : ℕ} (h c dt : ℝ)
    (v : Fin N → ℝ) : Fin N → ℝ :=
  (c * dt) • dPlus h v

/-- The quadratic energy
`Q(u, v) = normSq(u) + normSq(v) - inner(u, A * v)`. -/
noncomputable def yeeEnergy {N : ℕ} (h c dt : ℝ) (u v : Fin N → ℝ) : ℝ :=
  weightedNormSq h u + weightedNormSq h v -
    weightedInner h u (scaledForwardDifference h c dt v)

/-- Iterates of the leapfrog update from an initial pair:
the zeroth iterate is the initial pair and each successor applies
one update step. -/
noncomputable def leapfrogIterate {N : ℕ} (h c dt : ℝ) (u0 v0 : Fin N → ℝ) :
    ℕ → (Fin N → ℝ) × (Fin N → ℝ)
  | 0 => (u0, v0)
  | n + 1 =>
      leapfrogStep h c dt (leapfrogIterate h c dt u0 v0 n).1
        (leapfrogIterate h c dt u0 v0 n).2

/-! ## B. Auxiliary identities -/

private theorem periodicSucc_eq_finRotate {N : ℕ} (j : Fin N) :
    periodicSucc j = finRotate N j := by
  apply Fin.ext
  simp only [periodicSucc, finRotate_apply, Fin.val_add]
  simp [Nat.add_mod]

private theorem sum_periodicSucc {N : ℕ} (f : Fin N → ℝ) :
    ∑ j, f (periodicSucc j) = ∑ j, f j := by
  simp_rw [periodicSucc_eq_finRotate]
  simpa using
    (Equiv.Perm.sum_comp (finRotate N) Finset.univ f (by simp))

private theorem weightedInner_comm {N : ℕ} (h : ℝ) (u v : Fin N → ℝ) :
    weightedInner h u v = weightedInner h v u := by
  unfold weightedInner
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem weightedInner_add_left {N : ℕ} (h : ℝ)
    (u w v : Fin N → ℝ) :
    weightedInner h (u + w) v =
      weightedInner h u v + weightedInner h w v := by
  unfold weightedInner
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply]
  ring

private theorem weightedInner_add_right {N : ℕ} (h : ℝ)
    (u v w : Fin N → ℝ) :
    weightedInner h u (v + w) =
      weightedInner h u v + weightedInner h u w := by
  rw [weightedInner_comm h u (v + w), weightedInner_add_left,
    weightedInner_comm h u v, weightedInner_comm h u w]

private theorem weightedInner_sub_left {N : ℕ} (h : ℝ)
    (u w v : Fin N → ℝ) :
    weightedInner h (u - w) v =
      weightedInner h u v - weightedInner h w v := by
  unfold weightedInner
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.sub_apply]
  ring

private theorem weightedInner_sub_right {N : ℕ} (h : ℝ)
    (u v w : Fin N → ℝ) :
    weightedInner h u (v - w) =
      weightedInner h u v - weightedInner h u w := by
  rw [weightedInner_comm h u (v - w), weightedInner_sub_left,
    weightedInner_comm h u v, weightedInner_comm h u w]

private theorem weightedInner_smul_left {N : ℕ} (h a : ℝ)
    (u v : Fin N → ℝ) :
    weightedInner h (a • u) v = a * weightedInner h u v := by
  unfold weightedInner
  have hsum : (∑ j, (a • u) j * v j) = a * ∑ j, u j * v j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsum]
  ring

private theorem weightedInner_smul_right {N : ℕ} (h a : ℝ)
    (u v : Fin N → ℝ) :
    weightedInner h u (a • v) = a * weightedInner h u v := by
  rw [weightedInner_comm h u (a • v), weightedInner_smul_left,
    weightedInner_comm h u v]

private theorem weightedNormSq_add {N : ℕ} (h : ℝ)
    (u v : Fin N → ℝ) :
    weightedNormSq h (u + v) =
      weightedNormSq h u + 2 * weightedInner h u v +
        weightedNormSq h v := by
  unfold weightedNormSq
  rw [weightedInner_add_left, weightedInner_add_right,
    weightedInner_add_right, weightedInner_comm h v u]
  ring

private theorem weightedNormSq_sub {N : ℕ} (h : ℝ)
    (u v : Fin N → ℝ) :
    weightedNormSq h (u - v) =
      weightedNormSq h u - 2 * weightedInner h u v +
        weightedNormSq h v := by
  unfold weightedNormSq
  rw [weightedInner_sub_left, weightedInner_sub_right,
    weightedInner_sub_right, weightedInner_comm h v u]
  ring

private theorem dPlus_add {N : ℕ} (h : ℝ) (u v : Fin N → ℝ) :
    dPlus h (u + v) = dPlus h u + dPlus h v := by
  funext j
  unfold dPlus
  simp only [Pi.add_apply]
  ring

private theorem dPlus_sub {N : ℕ} (h : ℝ) (u v : Fin N → ℝ) :
    dPlus h (u - v) = dPlus h u - dPlus h v := by
  funext j
  unfold dPlus
  simp only [Pi.sub_apply]
  ring

private theorem scaledForwardDifference_add {N : ℕ} (h c dt : ℝ)
    (u v : Fin N → ℝ) :
    scaledForwardDifference h c dt (u + v) =
      scaledForwardDifference h c dt u +
        scaledForwardDifference h c dt v := by
  unfold scaledForwardDifference
  rw [dPlus_add, smul_add]

private theorem scaledForwardDifference_sub {N : ℕ} (h c dt : ℝ)
    (u v : Fin N → ℝ) :
    scaledForwardDifference h c dt (u - v) =
      scaledForwardDifference h c dt u -
        scaledForwardDifference h c dt v := by
  unfold scaledForwardDifference
  rw [dPlus_sub, smul_sub]

private theorem weightedInner_dPlus {N : ℕ} (h : ℝ)
    (u v : Fin N → ℝ) :
    weightedInner h u (dPlus h v) =
      weightedInner h (dPlusAdjoint h u) v := by
  have key : v ⬝ᵥ (dPlusAdjoint h u) = (dPlus h v) ⬝ᵥ u := by
    calc v ⬝ᵥ (dPlusAdjoint h u)
        = v ⬝ᵥ (Matrix.vecMul u (dPlusMatrix h)) := by
          unfold dPlusAdjoint
          rw [Matrix.mulVec_transpose]
      _ = (Matrix.vecMul u (dPlusMatrix h)) ⬝ᵥ v := by
          rw [dotProduct_comm]
      _ = u ⬝ᵥ (dPlusMatrix h *ᵥ v) := by
          rw [Matrix.dotProduct_mulVec]
      _ = u ⬝ᵥ (dPlus h v) := by
          rw [PeriodicLeapfrogStencil.dPlusMatrix_mulVec]
      _ = (dPlus h v) ⬝ᵥ u := by rw [dotProduct_comm]
  unfold weightedInner
  congr 1
  calc (∑ j, u j * dPlus h v j)
      = ∑ j, dPlus h v j * u j := by
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = ∑ j, v j * dPlusAdjoint h u j := by
        have k := key
        simp only [dotProduct] at k
        exact k.symm
    _ = ∑ j, dPlusAdjoint h u j * v j := by
        apply Finset.sum_congr rfl
        intro j _
        ring

private theorem weightedInner_scaledForwardDifference {N : ℕ}
    (h c dt : ℝ) (u v : Fin N → ℝ) :
    weightedInner h u (scaledForwardDifference h c dt v) =
      weightedInner h ((c * dt) • dPlusAdjoint h u) v := by
  unfold scaledForwardDifference
  rw [weightedInner_smul_right, weightedInner_dPlus,
    weightedInner_smul_left]

private theorem weightedNormSq_nonneg {N : ℕ} (h : ℝ) (hh : 0 < h)
    (w : Fin N → ℝ) :
    0 ≤ weightedNormSq h w := by
  unfold weightedNormSq weightedInner
  apply mul_nonneg hh.le
  apply Finset.sum_nonneg
  intro j _
  exact mul_self_nonneg _

private theorem weightedInner_sq_le {N : ℕ} (h : ℝ)
    (u w : Fin N → ℝ) :
    (weightedInner h u w) ^ 2 ≤
      weightedNormSq h u * weightedNormSq h w := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u w
  unfold weightedNormSq weightedInner
  calc (h * ∑ j, u j * w j) ^ 2
      = h ^ 2 * (∑ j, u j * w j) ^ 2 := by ring
    _ ≤ h ^ 2 * ((∑ j, u j ^ 2) * ∑ j, w j ^ 2) := by
        apply mul_le_mul_of_nonneg_left hcs
        positivity
    _ = (h * ∑ j, u j * u j) * (h * ∑ j, w j * w j) := by
        have e1 : (∑ j, u j ^ 2) = ∑ j, u j * u j := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        have e2 : (∑ j, w j ^ 2) = ∑ j, w j * w j := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [e1, e2]
        ring

private theorem weightedNormSq_dPlus_le {N : ℕ} (h : ℝ) (hh : 0 < h)
    (v : Fin N → ℝ) :
    weightedNormSq h (dPlus h v) ≤
      (4 / h ^ 2) * weightedNormSq h v := by
  have hsum : ∑ j, (v (periodicSucc j) - v j) ^ 2 ≤
      4 * ∑ j, v j ^ 2 := by
    have hterm : ∀ j : Fin N, (v (periodicSucc j) - v j) ^ 2 ≤
        2 * v (periodicSucc j) ^ 2 + 2 * v j ^ 2 := by
      intro j
      nlinarith [sq_nonneg (v (periodicSucc j) + v j)]
    calc ∑ j, (v (periodicSucc j) - v j) ^ 2
        ≤ ∑ j, (2 * v (periodicSucc j) ^ 2 + 2 * v j ^ 2) := by
          apply Finset.sum_le_sum
          intro j _
          exact hterm j
      _ = 4 * ∑ j, v j ^ 2 := by
          have hsucc : (∑ i, v (periodicSucc i) ^ 2) =
              ∑ i, v i ^ 2 := by
            simpa using sum_periodicSucc (fun x => v x ^ 2)
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, hsucc]
          ring
  have hhne : h ≠ 0 := ne_of_gt hh
  have hleft : weightedNormSq h (dPlus h v) =
      (∑ j, (v (periodicSucc j) - v j) ^ 2) / h := by
    unfold weightedNormSq weightedInner dPlus
    have hterm : (∑ j, (v (periodicSucc j) - v j) / h *
          ((v (periodicSucc j) - v j) / h)) =
        (∑ j, (v (periodicSucc j) - v j) ^ 2) / h ^ 2 := by
      calc (∑ j, (v (periodicSucc j) - v j) / h *
              ((v (periodicSucc j) - v j) / h))
          = ∑ j, (v (periodicSucc j) - v j) ^ 2 / h ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            ring
        _ = (∑ j, (v (periodicSucc j) - v j) ^ 2) / h ^ 2 := by
            simp only [div_eq_mul_inv, ← Finset.sum_mul]
    rw [hterm]
    field_simp
  have hright : (4 / h ^ 2) * weightedNormSq h v =
      (4 * ∑ j, v j ^ 2) / h := by
    have e : (∑ j, v j * v j) = ∑ j, v j ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    unfold weightedNormSq weightedInner
    rw [e]
    field_simp
  rw [hleft, hright]
  exact (div_le_div_iff_of_pos_right hh).mpr hsum

private theorem abs_weightedInner_scaled_le {N : ℕ} (h c dt : ℝ)
    (hh : 0 < h) (ha : 0 ≤ c * dt) (u v : Fin N → ℝ) :
    |weightedInner h u (scaledForwardDifference h c dt v)| ≤
      (c * dt / h) * pairNormSq h u v := by
  have hX : 0 ≤ weightedNormSq h u := weightedNormSq_nonneg h hh u
  have hW : weightedNormSq h (dPlus h v) ≤
      (4 / h ^ 2) * weightedNormSq h v :=
    weightedNormSq_dPlus_le h hh v
  have hcs := weightedInner_sq_le h u (dPlus h v)
  have hP : 0 ≤ pairNormSq h u v := by
    unfold pairNormSq
    exact add_nonneg hX (weightedNormSq_nonneg h hh v)
  have hcross_sq : (weightedInner h u (dPlus h v)) ^ 2 ≤
      (pairNormSq h u v / h) ^ 2 := by
    have h1 : (weightedInner h u (dPlus h v)) ^ 2 ≤
        weightedNormSq h u * ((4 / h ^ 2) * weightedNormSq h v) :=
      le_trans hcs (mul_le_mul_of_nonneg_left hW hX)
    have h2 : weightedNormSq h u *
          ((4 / h ^ 2) * weightedNormSq h v) ≤
        (pairNormSq h u v / h) ^ 2 := by
      have hY : 0 ≤ weightedNormSq h v :=
        weightedNormSq_nonneg h hh v
      have hxy : 4 * weightedNormSq h u * weightedNormSq h v ≤
          pairNormSq h u v ^ 2 := by
        unfold pairNormSq
        nlinarith [sq_nonneg
          (weightedNormSq h u - weightedNormSq h v)]
      have hh2 : (0 : ℝ) < h ^ 2 := by positivity
      have hhne : h ≠ 0 := ne_of_gt hh
      calc weightedNormSq h u *
              ((4 / h ^ 2) * weightedNormSq h v)
          = (4 * weightedNormSq h u * weightedNormSq h v) /
              h ^ 2 := by field_simp
        _ ≤ pairNormSq h u v ^ 2 / h ^ 2 :=
            (div_le_div_iff_of_pos_right hh2).mpr hxy
        _ = (pairNormSq h u v / h) ^ 2 := by
            rw [div_pow]
    exact le_trans h1 h2
  have hcross_abs : |weightedInner h u (dPlus h v)| ≤
      pairNormSq h u v / h :=
    abs_le_of_sq_le_sq hcross_sq (by positivity)
  have hscaled : weightedInner h u
        (scaledForwardDifference h c dt v) =
      (c * dt) * weightedInner h u (dPlus h v) := by
    unfold scaledForwardDifference
    exact weightedInner_smul_right h (c * dt) u (dPlus h v)
  rw [hscaled, abs_mul, abs_of_nonneg ha]
  calc (c * dt) * |weightedInner h u (dPlus h v)|
      ≤ (c * dt) * (pairNormSq h u v / h) := by
        apply mul_le_mul_of_nonneg_left hcross_abs ha
    _ = (c * dt / h) * pairNormSq h u v := by ring

/-! ## C. Energy invariance and coercivity -/

/-- The energy of the zero pair is zero. -/
theorem yeeEnergy_zero {N : ℕ} (h c dt : ℝ) :
    yeeEnergy (N := N) h c dt 0 0 = 0 := by
  unfold yeeEnergy weightedNormSq weightedInner
    scaledForwardDifference dPlus
  simp

/-- The squared pair norm is nonnegative at a positive weight. -/
theorem pairNormSq_nonneg {N : ℕ} (h : ℝ) (hh : 0 < h) (u v : Fin N → ℝ) :
    0 ≤ pairNormSq h u v := by
  unfold pairNormSq
  exact add_nonneg (weightedNormSq_nonneg h hh u)
    (weightedNormSq_nonneg h hh v)

/-- **One-step energy invariance.** The leapfrog update preserves
the quadratic energy exactly. -/
theorem leapfrogStep_yeeEnergy {N : ℕ} (h c dt : ℝ) (u v : Fin N → ℝ) :
    yeeEnergy h c dt (leapfrogStep h c dt u v).1
        (leapfrogStep h c dt u v).2 =
      yeeEnergy h c dt u v := by
  have h2 : (leapfrogStep h c dt u v).2 =
      v - (c * dt) • dPlusAdjoint h u := by
    simp [leapfrogStep]
  have h1 : (leapfrogStep h c dt u v).1 =
      u + scaledForwardDifference h c dt
        (v - (c * dt) • dPlusAdjoint h u) := by
    simp [leapfrogStep, scaledForwardDifference]
  have hBu : weightedInner h v ((c * dt) • dPlusAdjoint h u) =
      weightedInner h u (scaledForwardDifference h c dt v) := by
    rw [weightedInner_comm h v ((c * dt) • dPlusAdjoint h u),
      ← weightedInner_scaledForwardDifference h c dt u v]
  have hscaledB : weightedInner h u
        (scaledForwardDifference h c dt
          ((c * dt) • dPlusAdjoint h u)) =
      weightedNormSq h ((c * dt) • dPlusAdjoint h u) := by
    rw [weightedInner_scaledForwardDifference]
    rfl
  have ht : weightedInner h u
        (scaledForwardDifference h c dt
          (v - (c * dt) • dPlusAdjoint h u)) =
      weightedInner h u (scaledForwardDifference h c dt v) -
        weightedNormSq h ((c * dt) • dPlusAdjoint h u) := by
    rw [scaledForwardDifference_sub, weightedInner_sub_right,
      hscaledB]
  have hvNorm : weightedNormSq h
        (v - (c * dt) • dPlusAdjoint h u) =
      weightedNormSq h v -
        2 * weightedInner h v ((c * dt) • dPlusAdjoint h u) +
          weightedNormSq h ((c * dt) • dPlusAdjoint h u) :=
    weightedNormSq_sub h v _
  have huNorm : weightedNormSq h
        (u + scaledForwardDifference h c dt
          (v - (c * dt) • dPlusAdjoint h u)) =
      weightedNormSq h u +
        2 * weightedInner h u
          (scaledForwardDifference h c dt
            (v - (c * dt) • dPlusAdjoint h u)) +
          weightedNormSq h
            (scaledForwardDifference h c dt
              (v - (c * dt) • dPlusAdjoint h u)) :=
    weightedNormSq_add h u _
  have hcross : weightedInner h
        (u + scaledForwardDifference h c dt
          (v - (c * dt) • dPlusAdjoint h u))
        (scaledForwardDifference h c dt
          (v - (c * dt) • dPlusAdjoint h u)) =
      weightedInner h u
          (scaledForwardDifference h c dt
            (v - (c * dt) • dPlusAdjoint h u)) +
        weightedNormSq h
          (scaledForwardDifference h c dt
            (v - (c * dt) • dPlusAdjoint h u)) := by
    rw [weightedInner_add_left]
    congr 1
  unfold yeeEnergy
  rw [h1, h2, huNorm, hvNorm, hcross, ht, hBu]
  ring

/-- **Two-sided energy bound under a Courant bound.** With
`c * dt / h ≤ rho`, the energy is trapped between `(1 - rho)` and
`(1 + rho)` times the squared pair norm; the lower bound is coercive
when `rho < 1`. -/
theorem yeeEnergy_pairNormSq_bounds {N : ℕ} (h c dt rho : ℝ)
    (hh : 0 < h) (hc : 0 < c) (hdt : 0 < dt)
    (hr : c * dt / h ≤ rho) (u v : Fin N → ℝ) :
    (1 - rho) * pairNormSq h u v ≤ yeeEnergy h c dt u v ∧
      yeeEnergy h c dt u v ≤ (1 + rho) * pairNormSq h u v := by
  have ha : 0 ≤ c * dt := mul_nonneg hc.le hdt.le
  have hP : 0 ≤ pairNormSq h u v := pairNormSq_nonneg h hh u v
  have habs := abs_weightedInner_scaled_le h c dt hh ha u v
  have hr_bound : (c * dt / h) * pairNormSq h u v ≤
      rho * pairNormSq h u v :=
    mul_le_mul_of_nonneg_right hr hP
  have hcross : |weightedInner h u
        (scaledForwardDifference h c dt v)| ≤
      rho * pairNormSq h u v :=
    le_trans habs hr_bound
  have hcross' := abs_le.mp hcross
  unfold yeeEnergy pairNormSq at *
  constructor <;> linarith

/-- **Staggered-grid energy stability.** The leapfrog update
preserves the quadratic energy, and under the Courant bound
`c * dt / h ≤ rho` the energy is trapped between `(1 - rho)` and
`(1 + rho)` times the squared pair norm. -/
theorem staggeredLeapfrog_energyStable {N : ℕ}
    (h c dt rho : ℝ) (hh : 0 < h) (hc : 0 < c) (hdt : 0 < dt)
    (hr : c * dt / h ≤ rho) (u v : Fin N → ℝ) :
    yeeEnergy h c dt (leapfrogStep h c dt u v).1
          (leapfrogStep h c dt u v).2 =
        yeeEnergy h c dt u v ∧
      (1 - rho) * pairNormSq h u v ≤ yeeEnergy h c dt u v ∧
        yeeEnergy h c dt u v ≤ (1 + rho) * pairNormSq h u v := by
  exact ⟨leapfrogStep_yeeEnergy h c dt u v,
    yeeEnergy_pairNormSq_bounds h c dt rho hh hc hdt hr u v⟩

/-! ## D. All iterates -/

/-- Every iterate has the same energy as the initial pair. -/
theorem leapfrogIterate_yeeEnergy {N : ℕ} (h c dt : ℝ)
    (u0 v0 : Fin N → ℝ) (n : ℕ) :
    yeeEnergy h c dt (leapfrogIterate h c dt u0 v0 n).1
        (leapfrogIterate h c dt u0 v0 n).2 =
      yeeEnergy h c dt u0 v0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : leapfrogIterate h c dt u0 v0 (n + 1) =
          leapfrogStep h c dt
            (leapfrogIterate h c dt u0 v0 n).1
            (leapfrogIterate h c dt u0 v0 n).2 := rfl
      rw [hstep]
      exact (leapfrogStep_yeeEnergy h c dt _ _).trans ih

/-- **Uniform pair-norm bound.** Every iterate has pair norm at
most `sqrt((1 + rho) / (1 - rho))` times the initial pair norm. -/
theorem leapfrogIterate_pairNorm_le {N : ℕ}
    (h c dt rho : ℝ) (hh : 0 < h) (hc : 0 < c) (hdt : 0 < dt)
    (hr : c * dt / h ≤ rho) (hrho : rho < 1) (u0 v0 : Fin N → ℝ)
    (n : ℕ) :
    pairNorm h (leapfrogIterate h c dt u0 v0 n).1
        (leapfrogIterate h c dt u0 v0 n).2 ≤
      Real.sqrt ((1 + rho) / (1 - rho)) * pairNorm h u0 v0 := by
  have h1rho : 0 < 1 - rho := by linarith
  have hb0 := yeeEnergy_pairNormSq_bounds h c dt rho hh hc hdt hr u0 v0
  have hbn := yeeEnergy_pairNormSq_bounds h c dt rho hh hc hdt hr
    (leapfrogIterate h c dt u0 v0 n).1
      (leapfrogIterate h c dt u0 v0 n).2
  have henergy := leapfrogIterate_yeeEnergy h c dt u0 v0 n
  have hPn : pairNormSq h (leapfrogIterate h c dt u0 v0 n).1
        (leapfrogIterate h c dt u0 v0 n).2 ≤
      ((1 + rho) / (1 - rho)) * pairNormSq h u0 v0 := by
    have hle : (1 - rho) * pairNormSq h
          (leapfrogIterate h c dt u0 v0 n).1
          (leapfrogIterate h c dt u0 v0 n).2 ≤
        (1 + rho) * pairNormSq h u0 v0 := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ h1rho]
    linarith
  have hfactor : 0 ≤ (1 + rho) / (1 - rho) := by
    have hr0 : 0 ≤ c * dt / h := by
      apply div_nonneg (mul_nonneg hc.le hdt.le) hh.le
    apply div_nonneg <;> linarith
  unfold pairNorm
  calc Real.sqrt (pairNormSq h
          (leapfrogIterate h c dt u0 v0 n).1
          (leapfrogIterate h c dt u0 v0 n).2)
      ≤ Real.sqrt (((1 + rho) / (1 - rho)) *
          pairNormSq h u0 v0) :=
        Real.sqrt_le_sqrt hPn
    _ = Real.sqrt ((1 + rho) / (1 - rho)) *
          Real.sqrt (pairNormSq h u0 v0) :=
        Real.sqrt_mul hfactor _

/-! ## E. Courant boundary -/

/-- At Courant number at least one on an even grid, no positive
coercivity constant exists: for every positive `eps` some pair has
energy below `eps` times its squared pair norm. The strict margin
is therefore necessary for this argument, and at `r = 1` the lower
factor `1 - rho` degenerates to zero. -/
theorem no_positive_coercivity_of_courant_ge_one {N : ℕ} (hN : 2 ≤ N)
    (hNeven : Even N) (h c dt : ℝ) (hh : 0 < h) (hr : 1 ≤ c * dt / h) :
    ¬ ∃ eps : ℝ, 0 < eps ∧
      ∀ u v : Fin N → ℝ, eps * pairNormSq h u v ≤ yeeEnergy h c dt u v := by
  rintro ⟨eps, heps, hforall⟩
  set w : Fin N → ℝ := fun j => (-1 : ℝ) ^ j.val with hw_def
  have hsucc_w : ∀ j : Fin N, w (periodicSucc j) = - w j := by
    intro j
    by_cases hlt : j.val + 1 < N
    · have hv : (periodicSucc j).val = j.val + 1 :=
        Nat.mod_eq_of_lt hlt
      change (-1 : ℝ) ^ (periodicSucc j).val = - (-1 : ℝ) ^ j.val
      rw [hv, pow_succ]
      ring
    · have heq : j.val + 1 = N := by
        have hj := j.isLt
        omega
      have hv : (periodicSucc j).val = 0 := by
        change (j.val + 1) % N = 0
        rw [heq]
        exact Nat.mod_self N
      have hodd : Odd j.val := by
        obtain ⟨k, hk⟩ := hNeven
        exact ⟨k - 1, by omega⟩
      change (-1 : ℝ) ^ (periodicSucc j).val = - (-1 : ℝ) ^ j.val
      rw [hv, hodd.neg_one_pow]
      simp
  have hsq : ∀ j : Fin N, w j * w j = 1 := by
    intro j
    have hprod : w j * w j = (-1 : ℝ) ^ (j.val + j.val) := by
      change (-1 : ℝ) ^ j.val * (-1 : ℝ) ^ j.val = _
      rw [← pow_add]
    rw [hprod, Even.neg_one_pow ⟨j.val, rfl⟩]
  have hw_norm : weightedNormSq h w = h * (N : ℝ) := by
    unfold weightedNormSq weightedInner
    rw [Finset.sum_congr rfl (fun j _ => hsq j)]
    simp
  have hneg_norm : weightedNormSq h (-w) = h * (N : ℝ) := by
    have hsq' : ∀ j : Fin N, (-w) j * (-w) j = 1 := by
      intro j
      simp only [Pi.neg_apply]
      rw [neg_mul_neg]
      exact hsq j
    unfold weightedNormSq weightedInner
    rw [Finset.sum_congr rfl (fun j _ => hsq' j)]
    simp
  have hscaled : scaledForwardDifference h c dt (-w) =
      (2 * c * dt / h) • w := by
    funext j
    unfold scaledForwardDifference dPlus
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    rw [hsucc_w j]
    ring
  have hinner : weightedInner h w
        (scaledForwardDifference h c dt (-w)) =
      (2 * c * dt / h) * (h * (N : ℝ)) := by
    rw [hscaled, weightedInner_smul_right]
    have hwi : weightedInner h w w = h * (N : ℝ) := hw_norm
    rw [hwi]
  have henergy : yeeEnergy h c dt w (-w) =
      (2 - 2 * c * dt / h) * (h * (N : ℝ)) := by
    unfold yeeEnergy
    rw [hw_norm, hneg_norm, hinner]
    ring
  have hpair : pairNormSq h w (-w) = 2 * (h * (N : ℝ)) := by
    unfold pairNormSq
    rw [hw_norm, hneg_norm]
    ring
  have hspec := hforall w (-w)
  rw [hpair, henergy] at hspec
  have hNcast : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (by omega : 0 < N)
  have hpos : 0 < eps * (2 * (h * (N : ℝ))) :=
    mul_pos heps (by positivity)
  have hnonpos : (2 - 2 * c * dt / h) * (h * (N : ℝ)) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · rw [show (2 : ℝ) - 2 * c * dt / h = 2 - 2 * (c * dt / h) by ring]
      linarith
    · positivity
  linarith

end MathlibExt.Analysis.Numerical.PeriodicYeeEnergy
