/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Analysis.Numerical.PeriodicYeeEnergy
public import MathlibExt.Analysis.Numerical.PeriodicYeeResidual

/-!
# Global error bound for the periodic Yee leapfrog scheme

## i. Overview

On a periodic grid of `N` cells with spacing `h` and length
`L = N * h`, let `(u, v)` be a smooth periodic solution of the
first-order wave system `u_t = c * v_x`, `v_t = c * u_x` whose third
time derivatives are bounded by `Mt` and third space derivatives by
`Mx`. Sample it on the staggered grid, `U_j^n = u(n * dt, j * h)` and
`V_j^n = v(n * dt - dt / 2, j * h - h / 2)`, and run the periodic
leapfrog update from arbitrary initial grid data `(u0, v0)`. Under the
Courant bound `c * dt / h ≤ rho < 1`, for every step `n` with
`n * dt ≤ T` the pair error obeys

`pairNorm (U^n - u^n, V^n - v^n)
   ≤ sqrt((1 + rho) / (1 - rho)) *
       (pairNorm (U^0 - u0, V^0 - v0)
         + T * sqrt L * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 6)`.

The initial mismatch is kept as an explicit term. Since `V^0` samples
`v` at the half time `-dt / 2`, initializing `v0` from `v(0, .)`
leaves a nonzero half-step mismatch that the bound carries.

The proof combines the energy stability of
`MathlibExt.Analysis.Numerical.PeriodicYeeEnergy` with the consistency
residuals of `MathlibExt.Analysis.Numerical.PeriodicYeeResidual`. The
exact samples advance by one leapfrog step plus a forcing whose `u`
component is the `u` residual plus `c * dt` times the forward
difference of the `v` residual, because the `u` update reads the new
`v`. Since the forward difference has weighted norm at most `2 / h`
times its argument, the forcing has pair norm at most four times the
residual bound. Linearity of the step and a discrete variation of
constants then accumulate the forcing over `n` steps, and
`n * dt ≤ T` turns the accumulated residual bound into the `1 / 6`
term. Exact real arithmetic, one space dimension and periodic
boundaries only; no continuum convergence, boundary or floating-point
claim is made.

## ii. Key results

- `sampled_succ_eq_leapfrogStep_add_errorForcing`: the exact samples
  advance by one leapfrog step plus the error forcing.
- `weightedNorm_dPlus_le`: the periodic forward difference has
  weighted norm at most `2 / h` times the weighted norm of its
  argument.
- `errorForcing_pairNorm_le`: under the Courant bound, the error
  forcing has pair norm at most four times the consistency bound.
- `pairNorm_le_of_forced_leapfrog`: a forced leapfrog sequence stays
  within the stability factor times the initial pair norm plus the
  accumulated forcing.
- `leapfrogPairError_le`: the global error bound with the initial
  mismatch kept explicitly.
- `leapfrogPairError_le_of_exact_init`: exact staggered initialization
  removes the mismatch term.
- `globalErrorBound_refine_half`: halving `dt` and `h` keeps the
  Courant number and divides the truncation term by four.

## iii. Table of contents

- A. Definitions
- B. Algebraic structure of the update
- C. Norm estimates
- D. Discrete evolution with forcing
- E. Global error bound
- F. Refinement

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

namespace MathlibExt.Analysis.Numerical.PeriodicYeeError

open MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil
open MathlibExt.Analysis.Numerical.PeriodicYeeEnergy
open MathlibExt.Analysis.Numerical.PeriodicYeeResidual

/-! ## A. Definitions -/

/-- Pair error at step `n`: the Euclidean pair norm of the difference
between the exact staggered samples of `(u, v)` at step `n` and the
`n`-th leapfrog iterate from the initial grid data `(u0, v0)`. -/
noncomputable def leapfrogPairError {N : ℕ} (u v : ℝ → ℝ → ℝ) (h c dt : ℝ)
    (u0 v0 : Fin N → ℝ) (n : ℕ) : ℝ :=
  pairNorm h (sampledU u dt h n - (leapfrogIterate h c dt u0 v0 n).1)
    (sampledV v dt h n - (leapfrogIterate h c dt u0 v0 n).2)

/-- Initial pair mismatch between the exact staggered samples at step
`0` (the `v` sample taken at the half time `-dt / 2`) and the initial
grid data `(u0, v0)`. -/
noncomputable def initialPairMismatch {N : ℕ} (u v : ℝ → ℝ → ℝ) (h dt : ℝ)
    (u0 v0 : Fin N → ℝ) : ℝ :=
  pairNorm h (sampledU u dt h 0 - u0) (sampledV v dt h 0 - v0)

/-- The global error bound expression
`sqrt((1 + rho) / (1 - rho)) * (E0 + T * sqrt L * (Mt * dt^2 + c * Mx * h^2) / 6)`, defined for
all real arguments (at `rho = 1` total division makes the prefactor `0`); it bounds the pair error
under the hypotheses of `leapfrogPairError_le`. -/
noncomputable def globalErrorBound (rho T L c Mt Mx dt h E0 : ℝ) : ℝ :=
  Real.sqrt ((1 + rho) / (1 - rho)) *
    (E0 + T * Real.sqrt L * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 6)

/-- Per-step forcing of the error recursion: the `u` component is the
`u` residual plus the scaled forward difference of the `v` residual,
the `v` component is the `v` residual. -/
noncomputable def errorForcing {N : ℕ} (u v : ℝ → ℝ → ℝ) (h c dt : ℝ) (n : ℕ) :
    (Fin N → ℝ) × (Fin N → ℝ) :=
  (uUpdateResidual u v h c dt n + (c * dt) • dPlus h (vUpdateResidual u v h c dt n),
    vUpdateResidual u v h c dt n)

/-! ## B. Algebraic structure of the update -/

/-- The two components of a pair, concatenated as one Euclidean vector. -/
private noncomputable def pairVec {N : ℕ} (u v : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin N ⊕ Fin N) :=
  WithLp.toLp 2 (Sum.elim u v)

private theorem pairNorm_eq {N : ℕ} (h : ℝ) (hh : 0 ≤ h) (u v : Fin N → ℝ) :
    pairNorm h u v = Real.sqrt h * ‖pairVec u v‖ := by
  rw [pairNorm, ← Real.sqrt_sq (norm_nonneg (pairVec u v)), ← Real.sqrt_mul hh,
    EuclideanSpace.real_norm_sq_eq]
  congr 1
  simp only [pairNormSq, weightedNormSq, weightedInner, pairVec,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sq]
  ring

private theorem pairVec_add {N : ℕ} (u v u' v' : Fin N → ℝ) :
    pairVec (u + u') (v + v') = pairVec u v + pairVec u' v' := by
  ext x
  cases x <;> simp [pairVec]

private theorem pairVec_smul {N : ℕ} (k : ℝ) (u v : Fin N → ℝ) :
    pairVec (k • u) (k • v) = k • pairVec u v := by
  ext x
  cases x <;> simp [pairVec]

private theorem pairNorm_smul {N : ℕ} (h : ℝ) (hh : 0 ≤ h) (k : ℝ) (u v : Fin N → ℝ) :
    pairNorm h (k • u) (k • v) = |k| * pairNorm h u v := by
  rw [pairNorm_eq h hh, pairNorm_eq h hh, pairVec_smul, norm_smul, Real.norm_eq_abs]
  ring

private theorem weightedNorm_eq_pairNorm {N : ℕ} (h : ℝ) (w : Fin N → ℝ) :
    weightedNorm h w = pairNorm h w 0 := by
  simp [weightedNorm, pairNorm, pairNormSq, weightedNormSq, weightedInner]

private theorem weightedNorm_eq_pairNorm_snd {N : ℕ} (h : ℝ) (w : Fin N → ℝ) :
    weightedNorm h w = pairNorm h 0 w := by
  simp [weightedNorm, pairNorm, pairNormSq, weightedNormSq, weightedInner]

/-- The leapfrog step is additive in the pair. -/
theorem leapfrogStep_add {N : ℕ} (h c dt : ℝ) (u v u' v' : Fin N → ℝ) :
    leapfrogStep h c dt (u + u') (v + v') =
      leapfrogStep h c dt u v + leapfrogStep h c dt u' v' := by
  refine Prod.ext ?_ ?_ <;> funext j <;>
    simp [leapfrogStep, dPlusAdjoint_eq_neg_dMinus, dPlus, dMinus] <;> ring

/-- The leapfrog step commutes with subtraction of pairs. -/
theorem leapfrogStep_sub {N : ℕ} (h c dt : ℝ) (u v u' v' : Fin N → ℝ) :
    leapfrogStep h c dt (u - u') (v - v') =
      leapfrogStep h c dt u v - leapfrogStep h c dt u' v' := by
  refine Prod.ext ?_ ?_ <;> funext j <;>
    simp [leapfrogStep, dPlusAdjoint_eq_neg_dMinus, dPlus, dMinus] <;> ring

/-- Exact staggered samples advance by one leapfrog step plus the
error forcing built from the two update residuals. -/
theorem sampled_succ_eq_leapfrogStep_add_errorForcing {N : ℕ}
    (u v : ℝ → ℝ → ℝ) (h c dt : ℝ) (n : ℕ) :
    ((sampledU u dt h (n + 1) : Fin N → ℝ), (sampledV v dt h (n + 1) : Fin N → ℝ)) =
      leapfrogStep h c dt (sampledU u dt h n) (sampledV v dt h n) +
        errorForcing u v h c dt n := by
  refine Prod.ext ?_ ?_ <;> funext j
  · simp [leapfrogStep, errorForcing, uUpdateResidual, vUpdateResidual,
      dPlusAdjoint_eq_neg_dMinus, dPlus, dMinus]
    ring
  · simp [leapfrogStep, errorForcing, uUpdateResidual, vUpdateResidual,
      dPlusAdjoint_eq_neg_dMinus]

/-! ## C. Norm estimates -/

/-- The pair norm is subadditive at a nonnegative weight. -/
theorem pairNorm_add_le {N : ℕ} (h : ℝ) (hh : 0 ≤ h) (u v u' v' : Fin N → ℝ) :
    pairNorm h (u + u') (v + v') ≤ pairNorm h u v + pairNorm h u' v' := by
  rw [pairNorm_eq h hh, pairNorm_eq h hh, pairNorm_eq h hh, pairVec_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)

/-- The pair norm is at most the sum of the two component norms. -/
theorem pairNorm_le_weightedNorm_add {N : ℕ} (h : ℝ) (hh : 0 ≤ h)
    (u v : Fin N → ℝ) :
    pairNorm h u v ≤ weightedNorm h u + weightedNorm h v := by
  have := pairNorm_add_le h hh u 0 0 v
  rw [add_zero, zero_add] at this
  rw [weightedNorm_eq_pairNorm, weightedNorm_eq_pairNorm_snd]
  exact this

private theorem sum_comp_periodicSucc {N : ℕ} (f : Fin N → ℝ) :
    ∑ j, f (periodicSucc j) = ∑ j, f j := by
  have hinj : Function.Injective (periodicSucc (N := N)) := by
    intro a b hab
    have ha := a.isLt
    have hb := b.isLt
    have h' : (a.val + 1) % N = (b.val + 1) % N := congrArg Fin.val hab
    apply Fin.ext
    rcases Nat.lt_or_ge (a.val + 1) N with h1 | h1 <;>
      rcases Nat.lt_or_ge (b.val + 1) N with h2 | h2
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h'; omega
    · rw [Nat.mod_eq_of_lt h1, show b.val + 1 = N by omega, Nat.mod_self] at h'; omega
    · rw [Nat.mod_eq_of_lt h2, show a.val + 1 = N by omega, Nat.mod_self] at h'; omega
    · omega
  exact (Finite.injective_iff_bijective.mp hinj).sum_comp f

private theorem weightedNorm_add_le {N : ℕ} (h : ℝ) (hh : 0 ≤ h) (a b : Fin N → ℝ) :
    weightedNorm h (a + b) ≤ weightedNorm h a + weightedNorm h b := by
  have := pairNorm_add_le h hh a 0 b 0
  rw [add_zero] at this
  rw [weightedNorm_eq_pairNorm, weightedNorm_eq_pairNorm, weightedNorm_eq_pairNorm]
  exact this

private theorem weightedNorm_smul {N : ℕ} (h : ℝ) (hh : 0 ≤ h) (k : ℝ) (a : Fin N → ℝ) :
    weightedNorm h (k • a) = |k| * weightedNorm h a := by
  rw [weightedNorm_eq_pairNorm, weightedNorm_eq_pairNorm, ← pairNorm_smul h hh, smul_zero]

/-- The periodic forward difference has weighted norm at most `2 / h`
times the weighted norm of its argument. -/
theorem weightedNorm_dPlus_le {N : ℕ} (h : ℝ) (hh : 0 < h) (w : Fin N → ℝ) :
    weightedNorm h (dPlus h w) ≤ (2 / h) * weightedNorm h w := by
  have hre := sum_comp_periodicSucc (fun j => w j * w j)
  have hsum : ∑ j, dPlus h w j * dPlus h w j ≤ (2 / h) ^ 2 * ∑ j, w j * w j := by
    calc ∑ j, dPlus h w j * dPlus h w j
        = (∑ j, (w (periodicSucc j) - w j) ^ 2) / h ^ 2 := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [dPlus]; field_simp
      _ ≤ (∑ j, (2 * (w (periodicSucc j) * w (periodicSucc j)) + 2 * (w j * w j))) / h ^ 2 := by
          gcongr with j
          nlinarith [sq_nonneg (w (periodicSucc j) + w j)]
      _ = (2 / h) ^ 2 * ∑ j, w j * w j := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hre]
          field_simp; ring
  unfold weightedNorm weightedNormSq weightedInner
  rw [show (2 / h) * Real.sqrt (h * ∑ j, w j * w j) =
      Real.sqrt ((2 / h) ^ 2 * (h * ∑ j, w j * w j)) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  calc h * ∑ j, dPlus h w j * dPlus h w j ≤ h * ((2 / h) ^ 2 * ∑ j, w j * w j) :=
        mul_le_mul_of_nonneg_left hsum hh.le
    _ = (2 / h) ^ 2 * (h * ∑ j, w j * w j) := by ring

/-- Under the Courant bound `c * dt / h ≤ rho < 1`, the per-step
error forcing has pair norm at most four times the consistency bound. -/
theorem errorForcing_pairNorm_le {N : ℕ} (hN : 0 < N)
    (h dt c L Mt Mx rho : ℝ) (hh : 0 < h) (hdt : 0 < dt) (hc : 0 < c)
    (hL : L = (N : ℝ) * h) (hMt : 0 ≤ Mt) (hMx : 0 ≤ Mx)
    (hr : c * dt / h ≤ rho) (hrho : rho < 1)
    (u v : ℝ → ℝ → ℝ) (hsol : isSmoothPeriodicSolution L c Mt Mx u v)
    (n : ℕ) :
    pairNorm h (errorForcing (N := N) u v h c dt n).1
        (errorForcing (N := N) u v h c dt n).2 ≤
      4 * consistencyEta L dt c Mt Mx h := by
  obtain ⟨hu, hv⟩ := staggeredSampleResiduals_bounded hN h dt c L Mt Mx hh hdt hc hL hMt hMx
    u v hsol n
  have hη : 0 ≤ consistencyEta L dt c Mt Mx h := le_trans (weightedNorm_nonneg h hh.le _) hu
  have hD := weightedNorm_dPlus_le h hh (vUpdateResidual (N := N) u v h c dt n)
  have hl0 : 0 ≤ c * dt := (mul_pos hc hdt).le
  have hrv0 := weightedNorm_nonneg h hh.le (vUpdateResidual (N := N) u v h c dt n)
  have e0 : weightedNorm h (uUpdateResidual (N := N) u v h c dt n +
        (c * dt) • dPlus h (vUpdateResidual (N := N) u v h c dt n)) ≤
      weightedNorm h (uUpdateResidual (N := N) u v h c dt n) +
        c * dt * weightedNorm h (dPlus h (vUpdateResidual (N := N) u v h c dt n)) := by
    have := weightedNorm_add_le h hh.le (uUpdateResidual (N := N) u v h c dt n)
      ((c * dt) • dPlus h (vUpdateResidual (N := N) u v h c dt n))
    rwa [weightedNorm_smul h hh.le, abs_of_nonneg hl0] at this
  have e4 := pairNorm_le_weightedNorm_add h hh.le
    (uUpdateResidual (N := N) u v h c dt n +
      (c * dt) • dPlus h (vUpdateResidual (N := N) u v h c dt n))
    (vUpdateResidual (N := N) u v h c dt n)
  simp only [errorForcing]
  have e1 : c * dt * ((2 / h) * consistencyEta L dt c Mt Mx h) =
      2 * consistencyEta L dt c Mt Mx h * (c * dt / h) := by
    field_simp
  have e2 : 2 * consistencyEta L dt c Mt Mx h * (c * dt / h) ≤
      2 * consistencyEta L dt c Mt Mx h * 1 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e3 : c * dt * weightedNorm h (dPlus h (vUpdateResidual (N := N) u v h c dt n)) ≤
      c * dt * ((2 / h) * consistencyEta L dt c Mt Mx h) := by
    apply mul_le_mul_of_nonneg_left _ hl0
    exact hD.trans (mul_le_mul_of_nonneg_left hv (by positivity))
  linarith

/-! ## D. Discrete evolution with forcing -/

/-- Discrete variation of constants with the stability bound: a pair
sequence advanced by the leapfrog step plus a forcing of pair norm at
most `phi` stays within `sqrt((1 + rho) / (1 - rho))` times the initial
pair norm plus `n * phi`. -/
theorem pairNorm_le_of_forced_leapfrog {N : ℕ}
    (h c dt rho phi : ℝ) (hh : 0 < h) (hc : 0 < c) (hdt : 0 < dt)
    (hr : c * dt / h ≤ rho) (hrho : rho < 1)
    (E F : ℕ → (Fin N → ℝ) × (Fin N → ℝ))
    (hE : ∀ k : ℕ, E (k + 1) = leapfrogStep h c dt (E k).1 (E k).2 + F k)
    (hF : ∀ k : ℕ, pairNorm h (F k).1 (F k).2 ≤ phi) (n : ℕ) :
    pairNorm h (E n).1 (E n).2 ≤
      Real.sqrt ((1 + rho) / (1 - rho)) * (pairNorm h (E 0).1 (E 0).2 + n * phi) := by
  have hstep_sub : ∀ p q : (Fin N → ℝ) × (Fin N → ℝ),
      leapfrogStep h c dt (p - q).1 (p - q).2 =
        leapfrogStep h c dt p.1 p.2 - leapfrogStep h c dt q.1 q.2 :=
    fun p q => leapfrogStep_sub h c dt p.1 p.2 q.1 q.2
  induction n generalizing E F with
  | zero =>
    simpa [leapfrogIterate] using
      leapfrogIterate_pairNorm_le h c dt rho hh hc hdt hr hrho (E 0).1 (E 0).2 0
  | succ n ih =>
    obtain ⟨I, hI⟩ : ∃ I : ℕ → (Fin N → ℝ) × (Fin N → ℝ),
        ∀ k, I k = leapfrogIterate h c dt (E 0).1 (E 0).2 k := ⟨_, fun _ => rfl⟩
    have hIs : ∀ k, I (k + 1) = leapfrogStep h c dt (I k).1 (I k).2 := by
      intro k; rw [hI, hI]; rfl
    obtain ⟨E', hE'⟩ : ∃ E' : ℕ → (Fin N → ℝ) × (Fin N → ℝ),
        ∀ k, E' k = E (k + 1) - I (k + 1) := ⟨_, fun _ => rfl⟩
    have hrec : ∀ k, E' (k + 1) = leapfrogStep h c dt (E' k).1 (E' k).2 + F (k + 1) := by
      intro k
      rw [hE', hE', hE (k + 1), hIs (k + 1), hstep_sub]
      abel
    have hE'0 : E' 0 = F 0 := by
      rw [hE', hE 0, hIs 0, hI 0]
      change _ + F 0 - leapfrogStep h c dt (E 0).1 (E 0).2 = F 0
      abel
    have h1 := ih E' (fun k => F (k + 1)) hrec (fun k => hF (k + 1))
    rw [hE'0] at h1
    have h2 := leapfrogIterate_pairNorm_le h c dt rho hh hc hdt hr hrho (E 0).1 (E 0).2 (n + 1)
    rw [← hI] at h2
    have hdecomp : E (n + 1) = I (n + 1) + E' n := by rw [hE']; abel
    have hK : 0 ≤ Real.sqrt ((1 + rho) / (1 - rho)) := Real.sqrt_nonneg _
    have hF0 := hF 0
    calc pairNorm h (E (n + 1)).1 (E (n + 1)).2
        ≤ pairNorm h (I (n + 1)).1 (I (n + 1)).2 + pairNorm h (E' n).1 (E' n).2 := by
          rw [hdecomp]; exact pairNorm_add_le h hh.le _ _ _ _
      _ ≤ Real.sqrt ((1 + rho) / (1 - rho)) * pairNorm h (E 0).1 (E 0).2 +
            Real.sqrt ((1 + rho) / (1 - rho)) * (phi + n * phi) :=
          add_le_add h2 (h1.trans (mul_le_mul_of_nonneg_left (by linarith) hK))
      _ = Real.sqrt ((1 + rho) / (1 - rho)) *
            (pairNorm h (E 0).1 (E 0).2 + ((n + 1 : ℕ) : ℝ) * phi) := by
          push_cast; ring

/-! ## E. Global error bound -/

/-- The pair error at step `0` is the initial pair mismatch. -/
theorem leapfrogPairError_zero {N : ℕ} (u v : ℝ → ℝ → ℝ) (h c dt : ℝ)
    (u0 v0 : Fin N → ℝ) :
    leapfrogPairError u v h c dt u0 v0 0 = initialPairMismatch u v h dt u0 v0 := by
  rfl

/-- **Global error bound for the periodic Yee leapfrog scheme.** For a
smooth periodic solution with third time derivatives bounded by `Mt`
and third space derivatives bounded by `Mx`, under the Courant bound
`c * dt / h ≤ rho < 1`, the pair error at every step `n` with
`n * dt ≤ T` is at most
`sqrt((1 + rho) / (1 - rho)) * (E0 + T * sqrt L * (Mt * dt^2 + c * Mx * h^2) / 6)`,
where `E0` is the initial pair mismatch, kept explicitly. -/
theorem leapfrogPairError_le {N : ℕ} (hN : 0 < N)
    (h dt c L Mt Mx rho T : ℝ) (hh : 0 < h) (hdt : 0 < dt) (hc : 0 < c)
    (hL : L = (N : ℝ) * h) (hMt : 0 ≤ Mt) (hMx : 0 ≤ Mx)
    (hr : c * dt / h ≤ rho) (hrho : rho < 1)
    (u v : ℝ → ℝ → ℝ) (hsol : isSmoothPeriodicSolution L c Mt Mx u v)
    (u0 v0 : Fin N → ℝ) (n : ℕ) (hn : (n : ℝ) * dt ≤ T) :
    leapfrogPairError u v h c dt u0 v0 n ≤
      globalErrorBound rho T L c Mt Mx dt h (initialPairMismatch u v h dt u0 v0) := by
  obtain ⟨Ex, hEx⟩ : ∃ Ex : ℕ → (Fin N → ℝ) × (Fin N → ℝ), ∀ k,
      Ex k = ((sampledU u dt h k : Fin N → ℝ), (sampledV v dt h k : Fin N → ℝ)) -
        leapfrogIterate h c dt u0 v0 k := ⟨_, fun _ => rfl⟩
  have hrec : ∀ k, Ex (k + 1) =
      leapfrogStep h c dt (Ex k).1 (Ex k).2 + errorForcing u v h c dt k := by
    intro k
    rw [hEx, hEx, sampled_succ_eq_leapfrogStep_add_errorForcing u v h c dt k]
    have hs := leapfrogStep_sub h c dt (sampledU u dt h k) (sampledV v dt h k)
      (leapfrogIterate h c dt u0 v0 k).1 (leapfrogIterate h c dt u0 v0 k).2
    rw [Prod.fst_sub, Prod.snd_sub, hs]
    rw [show leapfrogIterate h c dt u0 v0 (k + 1) =
      leapfrogStep h c dt (leapfrogIterate h c dt u0 v0 k).1
        (leapfrogIterate h c dt u0 v0 k).2 from rfl]
    abel
  have hb := pairNorm_le_of_forced_leapfrog h c dt rho (4 * consistencyEta L dt c Mt Mx h)
    hh hc hdt hr hrho Ex (errorForcing u v h c dt) hrec
    (fun k => errorForcing_pairNorm_le hN h dt c L Mt Mx rho hh hdt hc hL hMt hMx hr hrho
      u v hsol k) n
  have h0 : pairNorm h (Ex 0).1 (Ex 0).2 = initialPairMismatch u v h dt u0 v0 := by
    rw [hEx]; rfl
  have hn' : pairNorm h (Ex n).1 (Ex n).2 = leapfrogPairError u v h c dt u0 v0 n := by
    rw [hEx]; rfl
  rw [h0, hn'] at hb
  refine hb.trans ?_
  unfold globalErrorBound
  have hX : 0 ≤ Real.sqrt L * (Mt * dt ^ 2 + c * Mx * h ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (mul_nonneg hMt (sq_nonneg _))
      (mul_nonneg (mul_nonneg hc.le hMx) (sq_nonneg _)))
  have key : (n : ℝ) * (4 * consistencyEta L dt c Mt Mx h) ≤
      T * Real.sqrt L * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 6 := by
    unfold consistencyEta
    nlinarith [mul_le_mul_of_nonneg_right hn hX]
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _)

/-- Exact staggered initialization (including the half-time `v`
sample) removes the mismatch term. -/
theorem leapfrogPairError_le_of_exact_init {N : ℕ} (hN : 0 < N)
    (h dt c L Mt Mx rho T : ℝ) (hh : 0 < h) (hdt : 0 < dt) (hc : 0 < c)
    (hL : L = (N : ℝ) * h) (hMt : 0 ≤ Mt) (hMx : 0 ≤ Mx)
    (hr : c * dt / h ≤ rho) (hrho : rho < 1)
    (u v : ℝ → ℝ → ℝ) (hsol : isSmoothPeriodicSolution L c Mt Mx u v)
    (n : ℕ) (hn : (n : ℝ) * dt ≤ T) :
    leapfrogPairError (N := N) u v h c dt (sampledU u dt h 0) (sampledV v dt h 0) n ≤
      Real.sqrt ((1 + rho) / (1 - rho)) *
        (T * Real.sqrt L * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 6) := by
  have hb := leapfrogPairError_le hN h dt c L Mt Mx rho T hh hdt hc hL hMt hMx hr hrho u v hsol
    (sampledU u dt h 0) (sampledV v dt h 0) n hn
  have h0 : initialPairMismatch u v h dt (sampledU u dt h 0 : Fin N → ℝ)
      (sampledV v dt h 0) = 0 := by
    simp [initialPairMismatch, pairNorm, pairNormSq, weightedNormSq,
      weightedInner]
  rw [h0, globalErrorBound, zero_add] at hb
  exact hb

/-! ## F. Refinement -/

/-- Halving both `dt` and `h` keeps the Courant number and divides the
truncation term of the bound by four. -/
theorem globalErrorBound_refine_half (rho T L c Mt Mx dt h E0 : ℝ) (hh : h ≠ 0) :
    c * (dt / 2) / (h / 2) = c * dt / h ∧
      globalErrorBound rho T L c Mt Mx (dt / 2) (h / 2) E0 =
        Real.sqrt ((1 + rho) / (1 - rho)) *
          (E0 + (T * Real.sqrt L * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 6) / 4) := by
  constructor
  · field_simp
  · unfold globalErrorBound
    ring

end MathlibExt.Analysis.Numerical.PeriodicYeeError
