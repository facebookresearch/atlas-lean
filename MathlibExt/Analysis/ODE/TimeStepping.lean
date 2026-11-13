/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Group.Even
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Ring.Parity
import MathlibExt.Analysis.ODE.ExplicitEuler

/-!
# Numerical time stepping for ODEs and diffusion

Explicit Euler reuse for scalar decay, discrete conservation and positivity,
periodic-grid FTCS diffusion, and a certified analytic-vs-numerical comparison.

## i. Overview

This module is the ATLAS MF14 numerical-time-stepping pilot. It reuses the landed
`MathlibExt.Analysis.ODE.ExplicitEuler` theory (quadratic local truncation bound and
first-order global convergence via discrete Grönwall) under its exact smoothness and
Lipschitz hypotheses — proving no new Euler convergence theorem — and adds the
structure-preserving discrete-time checks: linear conservation and
step-size-restricted positivity for a chosen update, positivity, conservation and
FTCS analysis on a periodic finite grid, and a certified analytic-vs-numerical
comparison for scalar decay.

## ii. Key results

* `decay_local_truncation_le`: quadratic local truncation bound for explicit Euler
  applied to scalar decay, by direct reuse (existential constant, as in the source).
* `decay_global_convergence`: first-order global convergence for scalar decay with
  explicit Lipschitz constant `|λ|`, by direct reuse.
* `eulerStep_conserves_dotProduct`, `eulerStep_iterate_conserves_dotProduct`: exact
  conservation of left-kernel weights, for one step and for iterates.
* `scalarEuler_nonneg`, `scalarEuler_neg_of_large_step`: positivity holds under the
  step-size restriction `h ≤ 1 / λ`, and fails above it (witness `x = 1`).
* `ftcsStep_nonneg`, `ftcsStep_conserves_sum`: FTCS positivity for `0 ≤ r ≤ 1 / 2`
  and exact mass conservation on the periodic grid.
* `ftcsStep_altMode`, `altMode_amplification_gt_one`: for even `m` the alternating mode
  is scaled by `1 - 4 * r`, hence amplified (`|1 - 4 * r| > 1`) for `r > 1 / 2`.
* `decay_euler_error_le`, `decay_euler_numeric_bound`: certified `O(h)` comparison
  of Euler iterates against `Real.exp`, plus the `λ = 1`, `T = 1`, `h = 1 / 10`,
  `n = 10` instance with explicit constant.

## iii. Table of contents

* A. Reuse of the landed explicit Euler theory
* B. Discrete conservation and step-size-restricted positivity
* C. Explicit 1D diffusion (FTCS) on a periodic grid
* D. Certified analytic-vs-numerical comparison

## iv. References

* E. Hairer, S. P. Nørsett and G. Wanner, Solving Ordinary Differential
  Equations I, 2nd ed., Section I.7 and Theorem I.7.3.
* `MathlibExt.Analysis.ODE.ExplicitEuler`: landed ATLAS Euler theory reused here.
* R. J. LeVeque, Finite Difference Methods for Ordinary and Partial Differential
  Equations, SIAM (2007), Sections 9.3 and 9.6: stability of the FTCS scheme for
  `u_t = D u_xx` exactly when `k ≤ h² / (2 D)`, i.e. `r ≤ 1 / 2` with `r = D k / h²`, by
  the method of lines and by von Neumann analysis.
-/

open scoped Matrix BigOperators

@[expose] public section

namespace MathlibExt.Analysis.ODE.TimeStepping

/-! ## A. Reuse of the landed explicit Euler theory

Direct instantiation of `ODE.exists_explicitEuler_localTruncationError_le` and
`MathlibExt.Analysis.ODE.ExplicitEulerWanted.explicit_euler_first_order_convergence`
for scalar decay `x' = -λ * x` (`λ > 0`) on `[0, T]`. Both source lemmas are
existential in the constant `C`, so the applied statements below are existential
as well. The `C²` and Lipschitz hypotheses are discharged exactly as stated. -/

private lemma hasDerivAt_decayExp (lam t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-lam * t)) (-lam * Real.exp (-lam * t)) t := by
  have hlin : HasDerivAt (fun s : ℝ => -lam * s) (-lam) t := by
    simpa using (hasDerivAt_id t).const_mul (-lam)
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-lam * x)) (Real.exp (-lam * t) * -lam) t :=
    hlin.exp
  have hcomm : Real.exp (-lam * t) * -lam = -lam * Real.exp (-lam * t) := mul_comm _ _
  rwa [hcomm] at hexp

private lemma decayContDiff (lam : ℝ) :
    ContDiff ℝ 2 (Function.uncurry fun _ x : ℝ => -lam * x) := by
  have hfun : (Function.uncurry fun _ x : ℝ => -lam * x) = fun p : ℝ × ℝ => -lam * p.2 := by
    funext p
    obtain ⟨a, b⟩ := p
    rfl
  rw [hfun]
  exact ContDiff.mul contDiff_const contDiff_snd

private lemma decayLipschitz (lam : ℝ) (t₀ T : ℝ) :
    ∀ t ∈ Set.Icc t₀ T, LipschitzWith ⟨|lam|, abs_nonneg lam⟩ (fun x : ℝ => -lam * x) := by
  intro t _
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  show ‖-lam * x - -lam * y‖ ≤ |lam| * ‖x - y‖
  have hfactor : -lam * x - -lam * y = -lam * (x - y) := by ring
  apply le_of_eq
  rw [hfactor, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]

/-- Quadratic local truncation bound for explicit Euler applied to scalar decay
`x' = -λ * x` on `[0, T]`, by direct reuse of
`ODE.exists_explicitEuler_localTruncationError_le` (existential constant, as in the
source lemma). -/
lemma decay_local_truncation_le {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ Set.Ioc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T, t + h ≤ T →
      ‖Real.exp (-lam * (t + h)) - (Real.exp (-lam * t) + h • (-lam * Real.exp (-lam * t)))‖ ≤
        C * h ^ 2 := by
  have hf : ContDiff ℝ 2 (Function.uncurry fun _ x : ℝ => -lam * x) := decayContDiff lam
  have hx : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt (fun t : ℝ => Real.exp (-lam * t)) (-lam * Real.exp (-lam * t)) t :=
    fun t _ => hasDerivAt_decayExp lam t
  obtain ⟨C, hC0, hC⟩ :=
    ODE.exists_explicitEuler_localTruncationError_le (fun _ x : ℝ => -lam * x) 0 T hT hf
      (fun t : ℝ => Real.exp (-lam * t)) hx
  refine ⟨C, hC0, ?_⟩
  intro h hh t ht hth
  have hh' : h ∈ Set.Ioc (0 : ℝ) (T - 0) := by simpa using hh
  exact hC h hh' t ht hth

/-- First-order global convergence of explicit Euler for scalar decay `x' = -λ * x`
on `[0, T]` with explicit Lipschitz constant `|λ|`, by direct reuse of
`MathlibExt.Analysis.ODE.ExplicitEulerWanted.explicit_euler_first_order_convergence`
(existential constant, as in the source lemma). -/
lemma decay_global_convergence {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T) :
    ∃ x : ℝ → ℝ, x 0 = 1 ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt x (-lam * x t) t) ∧
      ∃ C : ℝ, ∀ h ∈ Set.Ioc (0 : ℝ) T, ∀ X : ℕ → ℝ, X 0 = 1 →
        (∀ n, X (n + 1) = X n + h • (-lam * X n)) →
        ∀ n : ℕ, (n : ℝ) * h ≤ T → ‖X n - x ((n : ℝ) * h)‖ ≤ C * h := by
  have hf : ContDiff ℝ 2 (Function.uncurry fun _ x : ℝ => -lam * x) := decayContDiff lam
  have hlip : ∀ t ∈ Set.Icc (0 : ℝ) T,
      LipschitzWith ⟨|lam|, abs_nonneg lam⟩ ((fun _ x : ℝ => -lam * x) t) :=
    decayLipschitz lam 0 T
  obtain ⟨x, hx0, hx, C, hC⟩ :=
    MathlibExt.Analysis.ODE.ExplicitEulerWanted.explicit_euler_first_order_convergence
      (fun _ x : ℝ => -lam * x) 0 T 1 ⟨|lam|, abs_nonneg lam⟩ hT hf hlip
  refine ⟨x, hx0, by simpa using hx, C, ?_⟩
  intro h hh X hX0 hX n hn
  have hh' : h ∈ Set.Ioc (0 : ℝ) (T - 0) := by simpa using hh
  have hn' : (n : ℝ) * h ≤ T - 0 := by simpa using hn
  have hXn : ∀ n, X (n + 1) = X n + h • (fun _ x : ℝ => -lam * x) (0 + ↑n * h) (X n) := by
    simpa using hX
  have hbound := hC h hh' X hX0 hXn n hn'
  simpa using hbound

/-! ## B. Discrete conservation and step-size-restricted positivity

Exact conservation of left-kernel weights by the linear Euler update, and the
sharp step-size restriction for scalar-decay positivity. -/

/-- One explicit Euler step for the linear system `x' = A *ᵥ x`. -/
def eulerStep {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : ℝ) (x : Fin n → ℝ) :
    Fin n → ℝ :=
  x + h • (A *ᵥ x)

/-- A weight vector in the left kernel of `A` is conserved by one Euler step. -/
lemma eulerStep_conserves_dotProduct {n : ℕ} (w : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hker : ∀ x, w ⬝ᵥ (A *ᵥ x) = 0) (h : ℝ)
    (x : Fin n → ℝ) : w ⬝ᵥ eulerStep A h x = w ⬝ᵥ x := by
  simp [eulerStep, hker]

/-- Conservation of left-kernel weights persists under iteration of the Euler step. -/
lemma eulerStep_iterate_conserves_dotProduct {n : ℕ} (w : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hker : ∀ x, w ⬝ᵥ (A *ᵥ x) = 0) (h : ℝ) (k : ℕ)
    (x : Fin n → ℝ) : w ⬝ᵥ (eulerStep A h)^[k] x = w ⬝ᵥ x := by
  induction k generalizing x with
  | zero => rw [Function.iterate_zero_apply]
  | succ k ih =>
      rw [Function.iterate_succ_apply', eulerStep_conserves_dotProduct w A hker h]
      exact ih _

/-- Scalar decay stays nonnegative under the step-size restriction `h ≤ 1 / λ`. -/
lemma scalarEuler_nonneg {lam h x : ℝ} (hlam : 0 < lam) (hh0 : 0 ≤ h) (hh : h ≤ 1 / lam)
    (hx : 0 ≤ x) : 0 ≤ (1 - lam * h) * x := by
  have h1 : lam * h ≤ 1 := by
    calc lam * h ≤ lam * (1 / lam) := mul_le_mul_of_nonneg_left hh hlam.le
      _ = 1 := mul_one_div_cancel hlam.ne'
  have h2 : (0 : ℝ) ≤ 1 - lam * h := by linarith
  exact mul_nonneg h2 hx

/-- Above the step-size restriction, scalar decay sends the positive value
`x = 1` to a negative value. -/
lemma scalarEuler_neg_of_large_step {lam h : ℝ} (hlam : 0 < lam) (hh : 1 / lam < h) :
    ∃ x : ℝ, 0 < x ∧ (1 - lam * h) * x < 0 := by
  refine ⟨1, zero_lt_one, ?_⟩
  rw [mul_one]
  have h1 : (1 : ℝ) < lam * h := by
    calc (1 : ℝ) = lam * (1 / lam) := (mul_one_div_cancel hlam.ne').symm
      _ < lam * h := mul_lt_mul_of_pos_left hh hlam
  linarith

/-! ## C. Explicit 1D diffusion (FTCS) on a periodic grid

The grid is the discrete circle `Fin m`: the right neighbour of `i` is `finRotate m i`
(`i + 1`, wrapping from `m - 1` to `0`) and the left neighbour is `(finRotate m).symm i`.
This is the periodic boundary condition, the setting in which von Neumann analysis is
exact: every grid Fourier mode is an eigenvector of the step. Only the alternating mode
(`ξ h = π`, even `m`) is formalized here. A closed grid with zero-flux boundaries is a
different operator (an endpoint spike is updated by `1 - r` there, not `1 - 2 * r`) and is
not treated here. One FTCS step preserves nonnegativity for `0 ≤ r ≤ 1 / 2` and conserves
the total mass; for even `m` the alternating mode is scaled by `1 - 4 * r`. -/

/-- One explicit FTCS diffusion step on the periodic grid `Fin m` with mesh ratio `r`:
`u i + r * (u (i - 1) + u (i + 1) - 2 * u i)`, with the neighbours taken cyclically
through `finRotate m`. -/
def ftcsStep {m : ℕ} (r : ℝ) (u : Fin m → ℝ) : Fin m → ℝ :=
  fun i => u i + r * (u ((finRotate m).symm i) + u (finRotate m i) - 2 * u i)

/-- FTCS on a periodic grid conserves the total mass. -/
lemma ftcsStep_conserves_sum {m : ℕ} (r : ℝ) (u : Fin m → ℝ) :
    ∑ i, ftcsStep r u i = ∑ i, u i := by
  have hprev : ∑ i, u ((finRotate m).symm i) = ∑ i, u i := Equiv.sum_comp _ u
  have hnext : ∑ i, u (finRotate m i) = ∑ i, u i := Equiv.sum_comp _ u
  have hsum : (∑ i, (u ((finRotate m).symm i) + u (finRotate m i) - 2 * u i)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hprev, hnext]
    ring
  simp only [ftcsStep]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero]

/-- Convex-combination form of one FTCS step. -/
lemma ftcsStep_convex {m : ℕ} (r : ℝ) (u : Fin m → ℝ) (i : Fin m) :
    ftcsStep r u i =
      (1 - 2 * r) * u i + r * u ((finRotate m).symm i) + r * u (finRotate m i) := by
  simp only [ftcsStep]
  ring

/-- FTCS preserves nonnegativity for `0 ≤ r ≤ 1 / 2`. -/
lemma ftcsStep_nonneg {m : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    {u : Fin m → ℝ} (hu : ∀ i, 0 ≤ u i) : ∀ i, 0 ≤ ftcsStep r u i := by
  intro i
  rw [ftcsStep_convex]
  have h1 : (0 : ℝ) ≤ 1 - 2 * r := by linarith
  exact add_nonneg (add_nonneg (mul_nonneg h1 (hu i)) (mul_nonneg hr0 (hu _)))
    (mul_nonneg hr0 (hu _))

/-- Alternating mode `u i = (-1) ^ i.val` on `Fin m`. -/
def altMode {m : ℕ} : Fin m → ℝ := fun i => (-1 : ℝ) ^ i.val

private lemma altMode_finRotate {m : ℕ} (heven : Even m) (i : Fin m) :
    altMode (finRotate m i) = -altMode i := by
  cases m with
  | zero => exact i.elim0
  | succ n =>
    simp only [altMode]
    rw [coe_finRotate]
    split_ifs with hi
    · have hodd : Odd n := by
        obtain ⟨k, hk⟩ := heven
        exact ⟨k - 1, by omega⟩
      rw [hi, Fin.val_last, hodd.neg_one_pow]
      norm_num
    · rw [pow_succ]
      ring

private lemma altMode_finRotate_symm {m : ℕ} (heven : Even m) (i : Fin m) :
    altMode ((finRotate m).symm i) = -altMode i := by
  have h := altMode_finRotate heven ((finRotate m).symm i)
  rw [Equiv.apply_symm_apply] at h
  rw [h, neg_neg]

/-- One FTCS step scales the alternating mode by `1 - 4 * r` (requires `m` even). -/
lemma ftcsStep_altMode {m : ℕ} (heven : Even m) (r : ℝ) :
    ftcsStep r altMode = (1 - 4 * r) • (altMode : Fin m → ℝ) := by
  funext i
  simp only [ftcsStep, Pi.smul_apply, smul_eq_mul]
  rw [altMode_finRotate_symm heven i, altMode_finRotate heven i]
  ring

/-- Outside the stability regime the alternating-mode amplification factor exceeds
one in absolute value: `|1 - 4 * r| > 1` for `r > 1 / 2`. -/
lemma altMode_amplification_gt_one {r : ℝ} (hr : 1 / 2 < r) : 1 < |1 - 4 * r| := by
  have hneg : 1 - 4 * r < 0 := by linarith
  rw [abs_of_neg hneg]
  linarith

/-! ## D. Certified analytic-vs-numerical comparison

The reused global-convergence theorem identifies Euler iterates against the exact
decay solution (via uniqueness through an integrating factor), yielding a
certified `O(h)` error bound with an explicit numeric instance. -/

private lemma decay_solution_unique {lam T : ℝ} (hT : 0 ≤ T) {x y : ℝ → ℝ}
    (hx : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt x (-lam * x t) t)
    (hy : ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivAt y (-lam * y t) t)
    (h0 : x 0 = y 0) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) : x t = y t := by
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt ((x - y) * fun s : ℝ => Real.exp (lam * s)) 0 s := by
    intro s hs
    have hsub := (hx s hs).sub (hy s hs)
    have hlin : HasDerivAt (fun s : ℝ => lam * s) lam s := by
      simpa using (hasDerivAt_id s).const_mul lam
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (lam * s)) (Real.exp (lam * s) * lam) s :=
      hlin.exp
    have hmul := hsub.mul hexp
    simp only [Pi.sub_apply] at hmul
    have hzero : (-lam * x s - -lam * y s) * Real.exp (lam * s) +
        (x s - y s) * (Real.exp (lam * s) * lam) = 0 := by ring
    rwa [hzero] at hmul
  have hconst : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ((x - y) * fun s : ℝ => Real.exp (lam * s)) s =
        ((x - y) * fun s : ℝ => Real.exp (lam * s)) 0 := by
    intro s hs
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hle := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := (x - y) * fun s : ℝ => Real.exp (lam * s)) (f' := fun _ => (0 : ℝ))
      (C := (0 : ℝ)) (fun u hu => (hderiv u hu).hasDerivWithinAt) (fun u _ => by simp)
      (convex_Icc 0 T) h0mem hs
    simp only [zero_mul] at hle
    have heq := norm_le_zero_iff.mp hle
    exact sub_eq_zero.mp heq
  have hgs := hconst t ht
  simp only [Pi.mul_apply, Pi.sub_apply] at hgs
  rw [h0, sub_self, zero_mul] at hgs
  have hexp_ne : Real.exp (lam * t) ≠ 0 := (Real.exp_pos _).ne'
  have hsub0 : x t - y t = 0 := by
    rcases mul_eq_zero.mp hgs with h | h
    · exact h
    · exact absurd h hexp_ne
  exact sub_eq_zero.mp hsub0

/-- Certified first-order error bound for scalar-decay Euler iterates against the
exact solution `Real.exp (-λ * (n * h))`, derived from the reused
global-convergence theorem (existential constant, as in the source lemma). -/
lemma decay_euler_error_le {lam T : ℝ} (hlam : 0 < lam) (hT : 0 < T) :
    ∃ C : ℝ, ∀ h ∈ Set.Ioc (0 : ℝ) T, ∀ n : ℕ, (n : ℝ) * h ≤ T →
      |(1 - lam * h) ^ n - Real.exp (-lam * ((n : ℝ) * h))| ≤ C * h := by
  obtain ⟨x, hx0, hx, C, hC⟩ := decay_global_convergence hlam hT
  have hexp_deriv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt (fun t : ℝ => Real.exp (-lam * t)) (-lam * Real.exp (-lam * t)) t :=
    fun t _ => hasDerivAt_decayExp lam t
  have hexp0 : (fun t : ℝ => Real.exp (-lam * t)) 0 = 1 := by simp
  have hxexp : ∀ t ∈ Set.Icc (0 : ℝ) T, x t = (fun t : ℝ => Real.exp (-lam * t)) t := by
    intro t ht
    exact decay_solution_unique hT.le hx hexp_deriv (by rw [hx0]; exact hexp0.symm) t ht
  refine ⟨C, ?_⟩
  intro h hh n hn
  have hX0 : (fun k : ℕ => (1 - lam * h) ^ k) 0 = 1 := by simp
  have hXrec : ∀ k : ℕ, (fun k : ℕ => (1 - lam * h) ^ k) (k + 1) =
      (fun k : ℕ => (1 - lam * h) ^ k) k + h • (-lam * (fun k : ℕ => (1 - lam * h) ^ k) k) := by
    intro k
    show (1 - lam * h) ^ (k + 1) = (1 - lam * h) ^ k + h • (-lam * (1 - lam * h) ^ k)
    rw [pow_succ, smul_eq_mul]
    ring
  have hmem : (n : ℝ) * h ∈ Set.Icc (0 : ℝ) T :=
    ⟨mul_nonneg (Nat.cast_nonneg n) hh.1.le, hn⟩
  have hbound := hC h hh (fun k : ℕ => (1 - lam * h) ^ k) hX0 hXrec n hn
  rw [hxexp _ hmem] at hbound
  simpa [Real.norm_eq_abs] using hbound

/-- Numeric instance `λ = 1`, `T = 1`, `h = 1 / 10`, `n = 10` with explicit
constant `C = 1`, via verified decimal bounds on `Real.exp 1`. -/
lemma decay_euler_numeric_bound : |(9 / 10 : ℝ) ^ 10 - Real.exp (-1)| ≤ 1 * (1 / 10) := by
  have he1lo : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he1hi : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
  have hexp_neg : Real.exp (-1 : ℝ) = 1 / Real.exp 1 := by rw [Real.exp_neg, ← one_div]
  have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hhi : Real.exp (-1 : ℝ) < 0.368 := by
    rw [hexp_neg]
    calc (1 : ℝ) / Real.exp 1 ≤ 1 / 2.7182818283 :=
          one_div_le_one_div_of_le (by norm_num) he1lo.le
      _ < 0.368 := by norm_num
  have hlo : (0.367 : ℝ) < Real.exp (-1 : ℝ) := by
    rw [hexp_neg]
    calc (0.367 : ℝ) < 1 / 2.7182818286 := by norm_num
      _ ≤ 1 / Real.exp 1 := one_div_le_one_div_of_le hpos he1hi.le
  have hval : (9 / 10 : ℝ) ^ 10 = 0.3486784401 := by norm_num
  rw [hval]
  have hneg : (0.3486784401 : ℝ) - Real.exp (-1 : ℝ) < 0 := by linarith
  rw [abs_of_neg hneg]
  linarith

end MathlibExt.Analysis.ODE.TimeStepping
