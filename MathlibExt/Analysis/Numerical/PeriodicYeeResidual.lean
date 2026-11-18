/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil
public import MathlibExt.Analysis.Numerical.PeriodicYeeEnergy
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Periodic Yee residual

Let `u, v` solve the first-order wave system `u_t = c * v_x`,
`v_t = c * u_x`, periodic in space with period `L = N * h`, three
times continuously differentiable in each argument, with third time
derivatives bounded by `Mt` and third space derivatives bounded by
`Mx`. Sample on the staggered grid, `u_j^n = u(n * dt, j * h)` and
`v_j^n = v(n * dt - dt / 2, j * h - h / 2)`, and insert the exact
samples into the periodic leapfrog update built from `dPlus` and
`dMinus`. Each component residual then has weighted grid norm at most

`sqrt L * dt * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 24`.

The `1 / 24` constant comes from centred Taylor expansions and belongs
to the staggered locations: a travelling sine wave meets the bound,
while collocated sampling of `v` exceeds it on a concrete grid. No
continuum existence or solver convergence claim is made.
-/

@[expose] public section

namespace MathlibExt.Analysis.Numerical.PeriodicYeeResidual

open MathlibExt.Analysis.Numerical.PeriodicLeapfrogStencil
open MathlibExt.Analysis.Numerical.PeriodicYeeEnergy

/-! ### Weighted grid norm -/

/-- Weighted grid norm: the square root of the squared weighted grid
norm `PeriodicYeeEnergy.weightedNormSq`, which stays the one canonical
definition; this is only its unsquared view. -/
noncomputable def weightedNorm {N : ℕ} (h : ℝ) (w : Fin N → ℝ) : ℝ :=
  Real.sqrt (weightedNormSq h w)

/-! ### Staggered samples of a smooth solution -/

/-- Cell-centred samples `u_j^n = u(n * dt, j * h)`. -/
noncomputable def sampledU {N : ℕ} (u : ℝ → ℝ → ℝ) (dt h : ℝ) (n : ℕ) :
    Fin N → ℝ :=
  fun j => u ((n : ℝ) * dt) ((j.val : ℝ) * h)

/-- Staggered samples `v_j^n = v(n * dt - dt / 2, j * h - h / 2)`. -/
noncomputable def sampledV {N : ℕ} (v : ℝ → ℝ → ℝ) (dt h : ℝ) (n : ℕ) :
    Fin N → ℝ :=
  fun j => v ((n : ℝ) * dt - dt / 2) ((j.val : ℝ) * h - h / 2)

/-- Collocated samples `v(n * dt, j * h)`, used only to record that
the staggered constant does not transfer to collocated sampling. -/
noncomputable def collocatedV {N : ℕ} (v : ℝ → ℝ → ℝ) (dt h : ℝ) (n : ℕ) :
    Fin N → ℝ :=
  fun j => v ((n : ℝ) * dt) ((j.val : ℝ) * h)

/-! ### Update residuals for exact staggered samples -/

/-- Residual of the `u` update on exact samples: the exact step
minus the staggered update step `c * dt * Dplus` of the exact
staggered `v` sample at the half time. -/
noncomputable def uUpdateResidual {N : ℕ} (u v : ℝ → ℝ → ℝ) (h c dt : ℝ)
    (n : ℕ) : Fin N → ℝ :=
  sampledU u dt h (n + 1) - sampledU u dt h n -
    (c * dt) • dPlus h (sampledV v dt h (n + 1))

/-- Residual of the `v` update on exact samples: the exact step
minus the staggered update step `c * dt * Dminus` of the exact
cell-centred `u` sample at the centre time. -/
noncomputable def vUpdateResidual {N : ℕ} (u v : ℝ → ℝ → ℝ) (h c dt : ℝ)
    (n : ℕ) : Fin N → ℝ :=
  sampledV v dt h (n + 1) - sampledV v dt h n -
    (c * dt) • dMinus h (sampledU u dt h n)

/-- The `u` update residual formed with collocated `v` samples
instead of staggered ones. -/
noncomputable def collocatedUUpdateResidual {N : ℕ} (u v : ℝ → ℝ → ℝ)
    (h c dt : ℝ) (n : ℕ) : Fin N → ℝ :=
  sampledU u dt h (n + 1) - sampledU u dt h n -
    (c * dt) • dPlus h (collocatedV v dt h (n + 1))

/-- The consistency bound `sqrt(L) * dt * (Mt * dt^2 + c * Mx * h^2) / 24`. -/
noncomputable def consistencyEta (L dt c Mt Mx h : ℝ) : ℝ :=
  Real.sqrt L * dt * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 24

/-! ### Admissible smooth periodic solutions -/

/-- The first-order wave system `u_t = c * v_x`, `v_t = c * u_x`. -/
def satisfiesWaveSystem (c : ℝ) (u v : ℝ → ℝ → ℝ) : Prop :=
  (∀ t x : ℝ, deriv (fun s => u s x) t = c * deriv (fun y => v t y) x) ∧
    ∀ t x : ℝ, deriv (fun s => v s x) t = c * deriv (fun y => u t y) x

/-- Spatial periodicity with period `L` for both components. -/
def isSpatiallyPeriodic (L : ℝ) (u v : ℝ → ℝ → ℝ) : Prop :=
  (∀ t x : ℝ, u t (x + L) = u t x) ∧ ∀ t x : ℝ, v t (x + L) = v t x

/-- Uniform bounds `Mt` on third time derivatives and `Mx` on
third space derivatives of both components. -/
def hasThirdDerivativeBounds (Mt Mx : ℝ) (u v : ℝ → ℝ → ℝ) : Prop :=
  (∀ t x : ℝ, |iteratedDeriv 3 (fun s => u s x) t| ≤ Mt) ∧
    (∀ t x : ℝ, |iteratedDeriv 3 (fun s => v s x) t| ≤ Mt) ∧
    (∀ t x : ℝ, |iteratedDeriv 3 (fun y => u t y) x| ≤ Mx) ∧
    ∀ t x : ℝ, |iteratedDeriv 3 (fun y => v t y) x| ≤ Mx

/-- A smooth periodic solution of the wave system with the stated
third-derivative bounds: the system holds, both components are
periodic, each component is three times continuously
differentiable in each argument separately, and the derivative
bounds hold on a domain including the initial half-time sample. -/
def isSmoothPeriodicSolution (L c Mt Mx : ℝ) (u v : ℝ → ℝ → ℝ) : Prop :=
  satisfiesWaveSystem c u v ∧ isSpatiallyPeriodic L u v ∧
    (∀ x : ℝ, ContDiff ℝ 3 (fun t => u t x)) ∧
    (∀ x : ℝ, ContDiff ℝ 3 (fun t => v t x)) ∧
    (∀ t : ℝ, ContDiff ℝ 3 (fun y => u t y)) ∧
    (∀ t : ℝ, ContDiff ℝ 3 (fun y => v t y)) ∧
    hasThirdDerivativeBounds Mt Mx u v

/-! ### Consistency bounds -/

private theorem taylorEval2 {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {a x : ℝ} (hax : a ≠ x) :
    taylorWithinEval f 2 (Set.uIcc a x) a x =
      f a + (x - a) * deriv f a + (x - a)^2 / 2 * iteratedDeriv 2 f a := by
  have hu : UniqueDiffOn ℝ (Set.uIcc a x) := uniqueDiffOn_uIcc hax
  have ha : a ∈ Set.uIcc a x := Set.left_mem_uIcc
  have e0 : iteratedDerivWithin 0 f (Set.uIcc a x) a = f a := by simp
  have e1 : iteratedDerivWithin 1 f (Set.uIcc a x) a = deriv f a := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) ha,
      iteratedDeriv_one]
  have e2 : iteratedDerivWithin 2 f (Set.uIcc a x) a = iteratedDeriv 2 f a := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.contDiffAt.of_le (by norm_num)) ha]
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, smul_eq_mul]
  rw [e0, e1, e2]
  have hfact : ((Nat.factorial 2 : ℝ))⁻¹ = 1 / 2 := by norm_num [Nat.factorial]
  have hfact0 : ((Nat.factorial 0 : ℝ))⁻¹ = 1 := by norm_num
  have hfact1 : ((Nat.factorial 1 : ℝ))⁻¹ = 1 := by norm_num
  rw [hfact, hfact0, hfact1]
  ring

private theorem centred_bound {f : ℝ → ℝ} {M : ℝ} (hf : ContDiff ℝ 3 f)
    (hbound : ∀ t : ℝ, |iteratedDeriv 3 f t| ≤ M) (a s : ℝ) (hs : 0 < s) :
    |f (a + s) - f (a - s) - 2 * s * deriv f a| ≤ M * s ^ 3 / 3 := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hplus_ne : a ≠ a + s := by intro h; apply hs0; linarith
  have hminus_ne : a ≠ a - s := by intro h; apply hs0; linarith
  have hfOnPlus : ContDiffOn ℝ ((2 : ℕ) + 1) f (Set.uIcc a (a + s)) := by
    have h := hf.contDiffOn (s := Set.uIcc a (a + s))
    norm_num at h ⊢
    exact h
  have hfOnMinus : ContDiffOn ℝ ((2 : ℕ) + 1) f (Set.uIcc a (a - s)) := by
    have h := hf.contDiffOn (s := Set.uIcc a (a - s))
    norm_num at h ⊢
    exact h
  obtain ⟨xp, _hxp, hp⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := a + s) (x₀ := a) (n := 2)
      hplus_ne hfOnPlus
  obtain ⟨xm, _hxm, hm⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := a - s) (x₀ := a) (n := 2)
      hminus_ne hfOnMinus
  rw [taylorEval2 hf hplus_ne] at hp
  rw [taylorEval2 hf hminus_ne] at hm
  have hp2 : f (a + s) - (f a + s * deriv f a + s ^ 2 / 2 * iteratedDeriv 2 f a) =
      iteratedDeriv 3 f xp * s ^ 3 / 6 := by
    norm_num [Nat.factorial] at hp ⊢
    linarith [hp]
  have hm2 : f (a - s) - (f a + (-s) * deriv f a + s ^ 2 / 2 * iteratedDeriv 2 f a) =
      iteratedDeriv 3 f xm * (-s) ^ 3 / 6 := by
    have h2 : (a - s - a) = -s := by ring
    rw [h2] at hm
    norm_num [Nat.factorial] at hm ⊢
    linarith [hm]
  have key : f (a + s) - f (a - s) - 2 * s * deriv f a =
      iteratedDeriv 3 f xp * s ^ 3 / 6 - iteratedDeriv 3 f xm * (-s) ^ 3 / 6 := by
    linear_combination hp2 - hm2
  have hs3 : 0 ≤ s ^ 3 := pow_nonneg hs.le 3
  have hA : |iteratedDeriv 3 f xp * s ^ 3 / 6| ≤ M * s ^ 3 / 6 := by
    rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hs.le]
    have hb := hbound xp
    have hle : |iteratedDeriv 3 f xp| * s ^ 3 ≤ M * s ^ 3 :=
      mul_le_mul_of_nonneg_right hb hs3
    linarith [hle]
  have hB : |iteratedDeriv 3 f xm * (-s) ^ 3 / 6| ≤ M * s ^ 3 / 6 := by
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_of_nonneg hs.le]
    have hb := hbound xm
    have hle : |iteratedDeriv 3 f xm| * s ^ 3 ≤ M * s ^ 3 :=
      mul_le_mul_of_nonneg_right hb hs3
    linarith [hle]
  rw [key]
  calc |iteratedDeriv 3 f xp * s ^ 3 / 6 - iteratedDeriv 3 f xm * (-s) ^ 3 / 6|
      ≤ |iteratedDeriv 3 f xp * s ^ 3 / 6| + |iteratedDeriv 3 f xm * (-s) ^ 3 / 6| :=
        abs_sub _ _
    _ ≤ M * s ^ 3 / 6 + M * s ^ 3 / 6 := by linarith [hA, hB]
    _ = M * s ^ 3 / 3 := by ring

private theorem weightedNorm_le_of_pointwise {N : ℕ} {L h : ℝ} (hh : 0 ≤ h)
    (hL : L = (N : ℝ) * h) (w : Fin N → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hpoint : ∀ j, |w j| ≤ B) :
    weightedNorm h w ≤ Real.sqrt L * B := by
  have hsum : ∑ j, w j * w j ≤ (N : ℝ) * B ^ 2 := by
    have hcard : ∑ _j : Fin N, B ^ 2 = (N : ℝ) * B ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ]
    rw [← hcard]
    apply Finset.sum_le_sum
    intro j _
    have hj := hpoint j
    have h2 : (w j) ^ 2 ≤ B ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg hB])
    calc w j * w j = (w j) ^ 2 := (pow_two _).symm
      _ ≤ B ^ 2 := h2
  have hLB : 0 ≤ L := by
    rw [hL]
    exact mul_nonneg (Nat.cast_nonneg N) hh
  have hsqrt : Real.sqrt (h * ∑ j, w j * w j) ≤ Real.sqrt (L * B ^ 2) := by
    apply Real.sqrt_le_sqrt
    calc h * ∑ j, w j * w j ≤ h * ((N : ℝ) * B ^ 2) := by
          apply mul_le_mul_of_nonneg_left hsum hh
      _ = L * B ^ 2 := by rw [hL]; ring
  have hsqrtLB : Real.sqrt (L * B ^ 2) = Real.sqrt L * B := by
    rw [Real.sqrt_mul hLB, Real.sqrt_sq hB]
  unfold weightedNorm weightedNormSq weightedInner at *
  exact hsqrt.trans_eq hsqrtLB

private theorem weightedNorm_single_le {N : ℕ} {h : ℝ} (hh : 0 ≤ h)
    (w : Fin N → ℝ) (j0 : Fin N) :
    Real.sqrt h * |w j0| ≤ weightedNorm h w := by
  have hsingle : h * (w j0 * w j0) ≤ h * ∑ j, w j * w j := by
    apply mul_le_mul_of_nonneg_left _ hh
    apply Finset.single_le_sum (f := fun j => w j * w j)
    · intro i _
      exact mul_self_nonneg _
    · exact Finset.mem_univ j0
  have hsqrt : Real.sqrt (h * (w j0 * w j0)) ≤ Real.sqrt (h * ∑ j, w j * w j) :=
    Real.sqrt_le_sqrt hsingle
  have heq : Real.sqrt (h * (w j0 * w j0)) = Real.sqrt h * |w j0| := by
    rw [Real.sqrt_mul hh]
    congr 1
    rw [← pow_two, Real.sqrt_sq_eq_abs]
  unfold weightedNorm weightedNormSq weightedInner
  rw [← heq]
  exact hsqrt

private theorem sampledV_periodicSucc {N : ℕ} (_hN : 0 < N) {L h : ℝ}
    (hL : L = (N : ℝ) * h) (v : ℝ → ℝ → ℝ)
    (hper : ∀ t x : ℝ, v t (x + L) = v t x) (dt : ℝ) (m : ℕ) (j : Fin N) :
    sampledV v dt h m (periodicSucc j) =
      v ((m : ℝ) * dt - dt / 2) ((j.val : ℝ) * h + h / 2) := by
  by_cases hc : j.val + 1 < N
  · have hval : (periodicSucc j).val = j.val + 1 := by
      simp [periodicSucc, Nat.mod_eq_of_lt hc]
    unfold sampledV
    rw [hval]
    push_cast
    ring_nf
  · have hjeq : j.val + 1 = N := by
      have hjlt := j.isLt
      omega
    have hval : (periodicSucc j).val = 0 := by
      simp [periodicSucc, hjeq]
    have hjcast : (j.val : ℝ) = (N : ℝ) - 1 := by
      have h1 : (j.val : ℝ) + 1 = (N : ℝ) := by exact_mod_cast hjeq
      linarith
    unfold sampledV
    rw [hval]
    simp only [Nat.cast_zero, zero_mul, zero_sub]
    have hpos : (j.val : ℝ) * h + h / 2 = -h / 2 + L := by
      rw [hjcast, hL]
      ring
    rw [show (-(h / 2) : ℝ) = -h / 2 by ring, hpos]
    exact (hper _ (-h / 2)).symm

private theorem sampledU_periodicPred {N : ℕ} (hN : 0 < N) {L h : ℝ}
    (hL : L = (N : ℝ) * h) (u : ℝ → ℝ → ℝ)
    (hper : ∀ t x : ℝ, u t (x + L) = u t x) (dt : ℝ) (m : ℕ) (j : Fin N) :
    sampledU u dt h m (periodicPred j) =
      u ((m : ℝ) * dt) ((j.val : ℝ) * h - h) := by
  by_cases hc : 0 < j.val
  · have hval : (periodicPred j).val = j.val - 1 := by
      have hjlt := j.isLt
      have e1 : j.val + N - 1 = (j.val - 1) + N := by omega
      simp only [periodicPred]
      rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    unfold sampledU
    rw [hval]
    have hcast : ((j.val - 1 : ℕ) : ℝ) = (j.val : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ j.val)]
      simp
    rw [hcast]
    ring_nf
  · have hj0 : j.val = 0 := by omega
    have hval : (periodicPred j).val = N - 1 := by
      have e1 : j.val + N - 1 = N - 1 := by omega
      simp only [periodicPred]
      rw [e1, Nat.mod_eq_of_lt (by omega : N - 1 < N)]
    unfold sampledU
    rw [hval, hj0]
    simp only [Nat.cast_zero, zero_mul, zero_sub]
    have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      simp
    rw [hcast]
    have hpos : ((N : ℝ) - 1) * h = -h + L := by
      rw [hL]
      ring
    rw [hpos]
    exact hper _ (-h)

/-- The weighted norm is nonnegative at a nonnegative weight. -/
theorem weightedNorm_nonneg {N : ℕ} (h : ℝ) (hh : 0 ≤ h) (w : Fin N → ℝ) :
    0 ≤ weightedNorm h w := by
  have hsum : 0 ≤ ∑ j, w j * w j :=
    Finset.sum_nonneg (fun j _ => mul_self_nonneg (w j))
  have _ : 0 ≤ h * ∑ j, w j * w j := mul_nonneg hh hsum
  exact Real.sqrt_nonneg _

/-- The consistency bound is nonnegative for nonnegative data. -/
theorem consistencyEta_nonneg (L dt c Mt Mx h : ℝ) (_hL : 0 ≤ L)
    (hdt : 0 ≤ dt) (hc : 0 ≤ c) (hMt : 0 ≤ Mt) (hMx : 0 ≤ Mx) :
    0 ≤ consistencyEta L dt c Mt Mx h := by
  unfold consistencyEta
  positivity

/-- Consistency of the `u` update: its residual on exact staggered
samples has weighted norm at most the stated bound. -/
theorem uUpdateResidual_weightedNorm_le {N : ℕ} (hN : 0 < N)
    (h dt c L Mt Mx : ℝ) (hh : 0 < h) (hdt : 0 < dt) (hc : 0 < c)
    (hL : L = (N : ℝ) * h) (hMt : 0 ≤ Mt) (hMx : 0 ≤ Mx)
    (u v : ℝ → ℝ → ℝ) (hsol : isSmoothPeriodicSolution L c Mt Mx u v)
    (n : ℕ) :
    weightedNorm h (uUpdateResidual (N := N) u v h c dt n) ≤
      consistencyEta L dt c Mt Mx h := by
  obtain ⟨hsys, hper, hu_t, _hv_t, _hu_x, hv_x, hb⟩ := hsol
  obtain ⟨hb_u_t, _hb_v_t, _hb_u_x, hb_v_x⟩ := hb
  have hBnn : 0 ≤ dt * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 24 := by
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg hdt.le
    apply add_nonneg
    · exact mul_nonneg hMt (pow_nonneg hdt.le 2)
    · exact mul_nonneg (mul_nonneg hc.le hMx) (pow_nonneg hh.le 2)
  have hmain : weightedNorm h (uUpdateResidual (N := N) u v h c dt n) ≤
      Real.sqrt L * (dt * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 24) := by
    apply weightedNorm_le_of_pointwise hh.le hL _ hBnn
    intro j
    set xj : ℝ := (j.val : ℝ) * h with hxj
    set tmid : ℝ := (n : ℝ) * dt + dt / 2 with htmid
    have hsSucc : sampledV v dt h (n + 1) (periodicSucc j) =
        v tmid (xj + h / 2) := by
      have h1 := sampledV_periodicSucc hN hL v hper.2 dt (n + 1) j
      have htime : ((n + 1 : ℕ) : ℝ) * dt - dt / 2 = tmid := by
        rw [htmid]; push_cast; ring
      rw [htime] at h1
      exact h1
    have hsNorm : sampledV v dt h (n + 1) j = v tmid (xj - h / 2) := by
      unfold sampledV
      have htime : ((n + 1 : ℕ) : ℝ) * dt - dt / 2 = tmid := by
        rw [htmid]; push_cast; ring
      rw [htime]
    have hres : (uUpdateResidual (N := N) u v h c dt n) j =
        (u (((n + 1 : ℕ) : ℝ) * dt) xj - u ((n : ℝ) * dt) xj) -
          c * dt * ((v tmid (xj + h / 2) - v tmid (xj - h / 2)) / h) := by
      unfold uUpdateResidual dPlus
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sampledU]
      rw [hsSucc, hsNorm]
    rw [hres]
    have hpde : deriv (fun s => u s xj) tmid =
        c * deriv (fun y => v tmid y) xj := hsys.1 tmid xj
    have htime : |u (((n + 1 : ℕ) : ℝ) * dt) xj - u ((n : ℝ) * dt) xj -
        dt * deriv (fun s => u s xj) tmid| ≤ Mt * dt ^ 3 / 24 := by
      have h1 := centred_bound (hu_t xj) (fun t => hb_u_t t xj) tmid (dt / 2)
        (by linarith [hdt])
      have e1 : tmid + dt / 2 = ((n + 1 : ℕ) : ℝ) * dt := by
        rw [htmid]; push_cast; ring
      have e2 : tmid - dt / 2 = (n : ℝ) * dt := by rw [htmid]; ring
      rw [e1, e2] at h1
      have e3 : Mt * (dt / 2) ^ 3 / 3 = Mt * dt ^ 3 / 24 := by ring
      rw [e3] at h1
      have e4 : (2 : ℝ) * (dt / 2) = dt := by ring
      rw [e4] at h1
      exact h1
    have hspace : |(v tmid (xj + h / 2) - v tmid (xj - h / 2)) / h -
        deriv (fun y => v tmid y) xj| ≤ Mx * h ^ 2 / 24 := by
      have h1 := centred_bound (hv_x tmid) (fun y => hb_v_x tmid y) xj (h / 2)
        (by linarith [hh])
      have e3 : Mx * (h / 2) ^ 3 / 3 = Mx * h ^ 3 / 24 := by ring
      rw [e3] at h1
      have hh0 : (h : ℝ) ≠ 0 := ne_of_gt hh
      have heq : (v tmid (xj + h / 2) - v tmid (xj - h / 2)) / h -
            deriv (fun y => v tmid y) xj =
          (v tmid (xj + h / 2) - v tmid (xj - h / 2) -
            2 * (h / 2) * deriv (fun y => v tmid y) xj) / h := by
        field_simp
      rw [heq, abs_div, abs_of_nonneg hh.le, div_le_iff₀ hh]
      have e4 : Mx * h ^ 2 / 24 * h = Mx * h ^ 3 / 24 := by ring
      rw [e4]
      exact h1
    calc |(u (((n + 1 : ℕ) : ℝ) * dt) xj - u ((n : ℝ) * dt) xj) -
          c * dt * ((v tmid (xj + h / 2) - v tmid (xj - h / 2)) / h)|
        = |(u (((n + 1 : ℕ) : ℝ) * dt) xj - u ((n : ℝ) * dt) xj -
            dt * deriv (fun s => u s xj) tmid) -
            c * dt * ((v tmid (xj + h / 2) - v tmid (xj - h / 2)) / h -
              deriv (fun y => v tmid y) xj)| := by
          congr 1
          rw [hpde]
          ring
      _ ≤ |u (((n + 1 : ℕ) : ℝ) * dt) xj - u ((n : ℝ) * dt) xj -
            dt * deriv (fun s => u s xj) tmid| +
            |c * dt * ((v tmid (xj + h / 2) - v tmid (xj - h / 2)) / h -
              deriv (fun y => v tmid y) xj)| := abs_sub _ _
      _ ≤ Mt * dt ^ 3 / 24 + c * dt * (Mx * h ^ 2 / 24) := by
          apply add_le_add htime
          rw [abs_mul, abs_of_nonneg (mul_nonneg hc.le hdt.le)]
          exact mul_le_mul_of_nonneg_left hspace (mul_nonneg hc.le hdt.le)
      _ = dt * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 24 := by ring
  have heta : consistencyEta L dt c Mt Mx h =
      Real.sqrt L * (dt * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 24) := by
    unfold consistencyEta
    ring
  rw [heta]
  exact hmain

/-- Consistency of the `v` update: its residual on exact staggered
samples has weighted norm at most the stated bound. -/
theorem vUpdateResidual_weightedNorm_le {N : ℕ} (hN : 0 < N)
    (h dt c L Mt Mx : ℝ) (hh : 0 < h) (hdt : 0 < dt) (hc : 0 < c)
    (hL : L = (N : ℝ) * h) (hMt : 0 ≤ Mt) (hMx : 0 ≤ Mx)
    (u v : ℝ → ℝ → ℝ) (hsol : isSmoothPeriodicSolution L c Mt Mx u v)
    (n : ℕ) :
    weightedNorm h (vUpdateResidual (N := N) u v h c dt n) ≤
      consistencyEta L dt c Mt Mx h := by
  obtain ⟨hsys, hper, _hu_t, hv_t, hu_x, _hv_x, hb⟩ := hsol
  obtain ⟨_hb_u_t, hb_v_t, hb_u_x, _hb_v_x⟩ := hb
  have hBnn : 0 ≤ dt * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 24 := by
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg hdt.le
    apply add_nonneg
    · exact mul_nonneg hMt (pow_nonneg hdt.le 2)
    · exact mul_nonneg (mul_nonneg hc.le hMx) (pow_nonneg hh.le 2)
  have hmain : weightedNorm h (vUpdateResidual (N := N) u v h c dt n) ≤
      Real.sqrt L * (dt * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 24) := by
    apply weightedNorm_le_of_pointwise hh.le hL _ hBnn
    intro j
    set xj : ℝ := (j.val : ℝ) * h with hxj
    set xc : ℝ := xj - h / 2 with hxc
    set tn : ℝ := (n : ℝ) * dt with htn
    have hsPlus : sampledV v dt h (n + 1) j = v (tn + dt / 2) xc := by
      unfold sampledV
      have htime : ((n + 1 : ℕ) : ℝ) * dt - dt / 2 = tn + dt / 2 := by
        rw [htn]; push_cast; ring
      rw [htime]
    have hsMinus : sampledV v dt h n j = v (tn - dt / 2) xc := by
      unfold sampledV
      have htime : (n : ℝ) * dt - dt / 2 = tn - dt / 2 := by rw [htn]
      rw [htime]
    have hsU : sampledU u dt h n j = u tn xj := by
      unfold sampledU
      rw [htn]
    have hsPred : sampledU u dt h n (periodicPred j) = u tn (xj - h) := by
      have h1 := sampledU_periodicPred hN hL u hper.1 dt n j
      exact h1
    have hres : (vUpdateResidual (N := N) u v h c dt n) j =
        (v (tn + dt / 2) xc - v (tn - dt / 2) xc) -
          c * dt * ((u tn xj - u tn (xj - h)) / h) := by
      unfold vUpdateResidual dMinus
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsPlus, hsMinus, hsU, hsPred]
    rw [hres]
    have hpde : deriv (fun s => v s xc) tn =
        c * deriv (fun y => u tn y) xc := hsys.2 tn xc
    have htime : |v (tn + dt / 2) xc - v (tn - dt / 2) xc -
        dt * deriv (fun s => v s xc) tn| ≤ Mt * dt ^ 3 / 24 := by
      have h1 := centred_bound (hv_t xc) (fun t => hb_v_t t xc) tn (dt / 2)
        (by linarith [hdt])
      have e3 : Mt * (dt / 2) ^ 3 / 3 = Mt * dt ^ 3 / 24 := by ring
      rw [e3] at h1
      have e4 : (2 : ℝ) * (dt / 2) = dt := by ring
      rw [e4] at h1
      exact h1
    have hspace : |(u tn xj - u tn (xj - h)) / h -
        deriv (fun y => u tn y) xc| ≤ Mx * h ^ 2 / 24 := by
      have h1 := centred_bound (hu_x tn) (fun y => hb_u_x tn y) xc (h / 2)
        (by linarith [hh])
      have epos1 : xc + h / 2 = xj := by rw [hxc]; ring
      have epos2 : xc - h / 2 = xj - h := by rw [hxc]; ring
      rw [epos1, epos2] at h1
      have e3 : Mx * (h / 2) ^ 3 / 3 = Mx * h ^ 3 / 24 := by ring
      rw [e3] at h1
      have hh0 : (h : ℝ) ≠ 0 := ne_of_gt hh
      have heq : (u tn xj - u tn (xj - h)) / h -
            deriv (fun y => u tn y) xc =
          (u tn xj - u tn (xj - h) -
            2 * (h / 2) * deriv (fun y => u tn y) xc) / h := by
        field_simp
      rw [heq, abs_div, abs_of_nonneg hh.le, div_le_iff₀ hh]
      have e4 : Mx * h ^ 2 / 24 * h = Mx * h ^ 3 / 24 := by ring
      rw [e4]
      exact h1
    calc |(v (tn + dt / 2) xc - v (tn - dt / 2) xc) -
          c * dt * ((u tn xj - u tn (xj - h)) / h)|
        = |(v (tn + dt / 2) xc - v (tn - dt / 2) xc -
            dt * deriv (fun s => v s xc) tn) -
            c * dt * ((u tn xj - u tn (xj - h)) / h -
              deriv (fun y => u tn y) xc)| := by
          congr 1
          rw [hpde]
          ring
      _ ≤ |v (tn + dt / 2) xc - v (tn - dt / 2) xc -
            dt * deriv (fun s => v s xc) tn| +
            |c * dt * ((u tn xj - u tn (xj - h)) / h -
              deriv (fun y => u tn y) xc)| := abs_sub _ _
      _ ≤ Mt * dt ^ 3 / 24 + c * dt * (Mx * h ^ 2 / 24) := by
          apply add_le_add htime
          rw [abs_mul, abs_of_nonneg (mul_nonneg hc.le hdt.le)]
          exact mul_le_mul_of_nonneg_left hspace (mul_nonneg hc.le hdt.le)
      _ = dt * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 24 := by ring
  have heta : consistencyEta L dt c Mt Mx h =
      Real.sqrt L * (dt * (Mt * dt ^ 2 + c * Mx * h ^ 2) / 24) := by
    unfold consistencyEta
    ring
  rw [heta]
  exact hmain

/-- **Staggered-sample consistency.** For a smooth periodic
solution of the wave system with the stated third-derivative
bounds, both component update residuals on exact staggered
samples have weighted grid norm at most
`sqrt(L) * dt * (Mt * dt^2 + c * Mx * h^2) / 24`. -/
theorem staggeredSampleResiduals_bounded {N : ℕ} (hN : 0 < N)
    (h dt c L Mt Mx : ℝ) (hh : 0 < h) (hdt : 0 < dt) (hc : 0 < c)
    (hL : L = (N : ℝ) * h) (hMt : 0 ≤ Mt) (hMx : 0 ≤ Mx)
    (u v : ℝ → ℝ → ℝ) (hsol : isSmoothPeriodicSolution L c Mt Mx u v)
    (n : ℕ) :
    weightedNorm h (uUpdateResidual (N := N) u v h c dt n) ≤
        consistencyEta L dt c Mt Mx h ∧
      weightedNorm h (vUpdateResidual (N := N) u v h c dt n) ≤
        consistencyEta L dt c Mt Mx h := by
  exact ⟨uUpdateResidual_weightedNorm_le hN h dt c L Mt Mx hh hdt hc hL hMt hMx u v hsol n,
    vUpdateResidual_weightedNorm_le hN h dt c L Mt Mx hh hdt hc hL hMt hMx u v hsol n⟩

/-! ### Travelling sine wave fixture -/

/-- First component of the travelling sine wave, `sin(x - c * t)`. -/
noncomputable def travellingSineU (c : ℝ) (t x : ℝ) : ℝ :=
  Real.sin (x - c * t)

/-- Second component of the travelling sine wave, `-sin(x - c * t)`,
chosen so that the pair solves the wave system. -/
noncomputable def travellingSineV (c : ℝ) (t x : ℝ) : ℝ :=
  -Real.sin (x - c * t)

private theorem deriv_sin_sub_const (t y : ℝ) :
    deriv (fun a : ℝ => Real.sin (a - t)) y = Real.cos (y - t) := by
  have d1 : DifferentiableAt ℝ (fun a : ℝ => a - t) y := by fun_prop
  rw [deriv_sin d1]; simp

private theorem deriv_cos_sub_const (t y : ℝ) :
    deriv (fun a : ℝ => Real.cos (a - t)) y = -Real.sin (y - t) := by
  have d1 : DifferentiableAt ℝ (fun a : ℝ => a - t) y := by fun_prop
  rw [deriv_cos d1]; simp

private theorem deriv_negsin_sub_const (t y : ℝ) :
    deriv (fun a : ℝ => -Real.sin (a - t)) y = -Real.cos (y - t) := by
  have d1 : DifferentiableAt ℝ (fun a : ℝ => a - t) y := by fun_prop
  rw [deriv.fun_neg, deriv_sin d1]; simp

private theorem deriv_negcos_sub_const (t y : ℝ) :
    deriv (fun a : ℝ => -Real.cos (a - t)) y = Real.sin (y - t) := by
  have d1 : DifferentiableAt ℝ (fun a : ℝ => a - t) y := by fun_prop
  rw [deriv.fun_neg, deriv_cos d1]; simp

private theorem iter3_sin_sub_const (t y : ℝ) :
    iteratedDeriv 3 (fun a : ℝ => Real.sin (a - t)) y = -Real.cos (y - t) := by
  have e1 : deriv (fun a : ℝ => Real.sin (a - t)) = fun a => Real.cos (a - t) := by
    funext a; exact deriv_sin_sub_const t a
  have e2 : deriv (fun a : ℝ => Real.cos (a - t)) = fun a => -Real.sin (a - t) := by
    funext a; exact deriv_cos_sub_const t a
  have e3 : deriv (fun a : ℝ => -Real.sin (a - t)) = fun a => -Real.cos (a - t) := by
    funext a; exact deriv_negsin_sub_const t a
  have step : iteratedDeriv 3 (fun a : ℝ => Real.sin (a - t)) =
      deriv (deriv (deriv (fun a : ℝ => Real.sin (a - t)))) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [step, e1, e2, e3]

private theorem iter3_negsin_sub_const (t y : ℝ) :
    iteratedDeriv 3 (fun a : ℝ => -Real.sin (a - t)) y = Real.cos (y - t) := by
  have e1 : deriv (fun a : ℝ => -Real.sin (a - t)) = fun a => -Real.cos (a - t) := by
    funext a; exact deriv_negsin_sub_const t a
  have e2 : deriv (fun a : ℝ => -Real.cos (a - t)) = fun a => Real.sin (a - t) := by
    funext a; exact deriv_negcos_sub_const t a
  have e3 : deriv (fun a : ℝ => Real.sin (a - t)) = fun a => Real.cos (a - t) := by
    funext a; exact deriv_sin_sub_const t a
  have step : iteratedDeriv 3 (fun a : ℝ => -Real.sin (a - t)) =
      deriv (deriv (deriv (fun a : ℝ => -Real.sin (a - t)))) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [step, e1, e2, e3]

private theorem deriv_sin_scaled (x c s : ℝ) :
    deriv (fun a : ℝ => Real.sin (x - c * a)) s = -c * Real.cos (x - c * s) := by
  have d1 : DifferentiableAt ℝ (fun a : ℝ => x - c * a) s := by fun_prop
  rw [deriv_sin d1]; simp; ring

private theorem deriv_negsin_scaled (x c s : ℝ) :
    deriv (fun a : ℝ => -Real.sin (x - c * a)) s = c * Real.cos (x - c * s) := by
  have d1 : DifferentiableAt ℝ (fun a : ℝ => x - c * a) s := by fun_prop
  rw [deriv.fun_neg, deriv_sin d1]; simp; ring

private theorem deriv_cos_scaled (x c s : ℝ) :
    deriv (fun a : ℝ => Real.cos (x - c * a)) s = c * Real.sin (x - c * s) := by
  have d1 : DifferentiableAt ℝ (fun a : ℝ => x - c * a) s := by fun_prop
  rw [deriv_cos d1]; simp; ring

private theorem deriv_kmul_cos_scaled (k x c s : ℝ) :
    deriv (fun a : ℝ => k * Real.cos (x - c * a)) s =
      (k * c) * Real.sin (x - c * s) := by
  have hd : DifferentiableAt ℝ (fun a : ℝ => Real.cos (x - c * a)) s := by fun_prop
  rw [deriv_const_mul_field, deriv_cos_scaled]; ring

private theorem deriv_kmul_sin_scaled (k x c s : ℝ) :
    deriv (fun a : ℝ => k * Real.sin (x - c * a)) s =
      (-(k * c)) * Real.cos (x - c * s) := by
  have hd : DifferentiableAt ℝ (fun a : ℝ => Real.sin (x - c * a)) s := by fun_prop
  rw [deriv_const_mul_field, deriv_sin_scaled]; ring

private theorem iter3_sin_scaled (x c t : ℝ) :
    iteratedDeriv 3 (fun s : ℝ => Real.sin (x - c * s)) t =
      c ^ 3 * Real.cos (x - c * t) := by
  have e1 : deriv (fun s : ℝ => Real.sin (x - c * s)) =
      fun s => (-c) * Real.cos (x - c * s) := by
    funext s; exact deriv_sin_scaled x c s
  have e2 : deriv (fun s : ℝ => (-c) * Real.cos (x - c * s)) =
      fun s => (-c * c) * Real.sin (x - c * s) := by
    funext s; exact deriv_kmul_cos_scaled (-c) x c s
  have e3 : deriv (fun s : ℝ => (-c * c) * Real.sin (x - c * s)) =
      fun s => (-((-c * c) * c)) * Real.cos (x - c * s) := by
    funext s; exact deriv_kmul_sin_scaled (-c * c) x c s
  have step : iteratedDeriv 3 (fun s : ℝ => Real.sin (x - c * s)) =
      deriv (deriv (deriv (fun s : ℝ => Real.sin (x - c * s)))) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [step, e1, e2, e3]
  ring

private theorem iter3_negsin_scaled (x c t : ℝ) :
    iteratedDeriv 3 (fun s : ℝ => -Real.sin (x - c * s)) t =
      -(c ^ 3) * Real.cos (x - c * t) := by
  have e1 : deriv (fun s : ℝ => -Real.sin (x - c * s)) =
      fun s => c * Real.cos (x - c * s) := by
    funext s; exact deriv_negsin_scaled x c s
  have e2 : deriv (fun s : ℝ => c * Real.cos (x - c * s)) =
      fun s => (c * c) * Real.sin (x - c * s) := by
    funext s; exact deriv_kmul_cos_scaled c x c s
  have e3 : deriv (fun s : ℝ => (c * c) * Real.sin (x - c * s)) =
      fun s => (-((c * c) * c)) * Real.cos (x - c * s) := by
    funext s; exact deriv_kmul_sin_scaled (c * c) x c s
  have step : iteratedDeriv 3 (fun s : ℝ => -Real.sin (x - c * s)) =
      deriv (deriv (deriv (fun s : ℝ => -Real.sin (x - c * s)))) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [step, e1, e2, e3]
  ring

private theorem travellingSine_smooth_general (c : ℝ) (hc : 0 < c) :
    isSmoothPeriodicSolution (2 * Real.pi) c (c ^ 3) 1
      (travellingSineU c) (travellingSineV c) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro t x
    simp only [travellingSineU, travellingSineV]
    rw [deriv_sin_scaled, deriv_negsin_sub_const]
    ring
  · intro t x
    simp only [travellingSineU, travellingSineV]
    rw [deriv_negsin_scaled, deriv_sin_sub_const]
  · intro t x
    simp only [travellingSineU]
    have e : x + 2 * Real.pi - c * t = (x - c * t) + 2 * Real.pi := by ring
    rw [e, Real.sin_add_two_pi]
  · intro t x
    simp only [travellingSineV]
    have e : x + 2 * Real.pi - c * t = (x - c * t) + 2 * Real.pi := by ring
    rw [e, Real.sin_add_two_pi]
  · intro x
    simp only [travellingSineU]
    exact Real.contDiff_sin.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  · intro x
    simp only [travellingSineV]
    exact (Real.contDiff_sin.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))).neg
  · intro t
    simp only [travellingSineU]
    exact Real.contDiff_sin.comp (contDiff_id.sub contDiff_const)
  · intro t
    simp only [travellingSineV]
    exact (Real.contDiff_sin.comp (contDiff_id.sub contDiff_const)).neg
  · intro t x
    simp only [travellingSineU]
    rw [iter3_sin_scaled]
    have hc3 : 0 ≤ c ^ 3 := pow_nonneg hc.le 3
    calc |c ^ 3 * Real.cos (x - c * t)| = c ^ 3 * |Real.cos (x - c * t)| := by
          rw [abs_mul, abs_of_nonneg hc3]
      _ ≤ c ^ 3 * 1 := by
          apply mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hc3
      _ = c ^ 3 := by ring
  · intro t x
    simp only [travellingSineV]
    rw [iter3_negsin_scaled]
    have hc3 : 0 ≤ c ^ 3 := pow_nonneg hc.le 3
    calc |-(c ^ 3) * Real.cos (x - c * t)| = c ^ 3 * |Real.cos (x - c * t)| := by
          rw [abs_mul, abs_neg, abs_of_nonneg hc3]
      _ ≤ c ^ 3 * 1 := by
          apply mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hc3
      _ = c ^ 3 := by ring
  · intro t x
    simp only [travellingSineU]
    rw [iter3_sin_sub_const]
    simpa using Real.abs_cos_le_one (x - c * t)
  · intro t x
    simp only [travellingSineV]
    rw [iter3_negsin_sub_const]
    exact Real.abs_cos_le_one _

/-- The nonzero travelling sine wave, sampled at the staggered
locations, satisfies the same consistency bound with third-derivative
bounds `c ^ 3` in time and `1` in space, and period `2 * pi`. -/
theorem travellingSine_staggeredResiduals_bounded {N : ℕ} (hN : 0 < N)
    (h dt c : ℝ) (hh : 0 < h) (hdt : 0 < dt) (hc : 0 < c)
    (hL : 2 * Real.pi = (N : ℝ) * h) (n : ℕ) :
    weightedNorm h
        (uUpdateResidual (N := N) (travellingSineU c) (travellingSineV c) h c dt n) ≤
        consistencyEta (2 * Real.pi) dt c (c ^ 3) 1 h ∧
      weightedNorm h
        (vUpdateResidual (N := N) (travellingSineU c) (travellingSineV c) h c dt n) ≤
        consistencyEta (2 * Real.pi) dt c (c ^ 3) 1 h := by
  exact staggeredSampleResiduals_bounded hN h dt c (2 * Real.pi) (c ^ 3) 1
    hh hdt hc hL (pow_nonneg hc.le 3) (by norm_num)
    (travellingSineU c) (travellingSineV c) (travellingSine_smooth_general c hc) n

/-! ### Collocated sampling boundary -/

private theorem collocated_residual_one :
    (collocatedUUpdateResidual (N := 4) (travellingSineU 1) (travellingSineV 1)
      (Real.pi / 2) 1 (Real.pi / 6) 0) (⟨1, by norm_num⟩ : Fin 4) =
      (2 * Real.sqrt 3 - 5) / 6 := by
  have hsucc : periodicSucc (⟨1, by norm_num⟩ : Fin 4) = (⟨2, by norm_num⟩ : Fin 4) := by
    apply Fin.ext
    simp [periodicSucc]
  have hU1 : sampledU (travellingSineU 1) (Real.pi / 6) (Real.pi / 2) 1
        (⟨1, by norm_num⟩ : Fin 4) = Real.sqrt 3 / 2 := by
    unfold sampledU travellingSineU
    simp only [Nat.cast_one, one_mul]
    have e : Real.pi / 2 - Real.pi / 6 = Real.pi / 3 := by ring
    rw [e, Real.sin_pi_div_three]
  have hU0 : sampledU (travellingSineU 1) (Real.pi / 6) (Real.pi / 2) 0
        (⟨1, by norm_num⟩ : Fin 4) = 1 := by
    unfold sampledU travellingSineU
    simp only [Nat.cast_zero, zero_mul, sub_zero, one_mul]
    have e : ((1 : ℕ) : ℝ) * (Real.pi / 2) = Real.pi / 2 := by norm_num
    rw [e, Real.sin_pi_div_two]
  have hVsucc : collocatedV (travellingSineV 1) (Real.pi / 6) (Real.pi / 2) 1
        (periodicSucc (⟨1, by norm_num⟩ : Fin 4)) = -1 / 2 := by
    rw [hsucc]
    unfold collocatedV travellingSineV
    simp only [Nat.cast_one, one_mul]
    have e : ((2 : ℕ) : ℝ) * (Real.pi / 2) - Real.pi / 6 =
        Real.pi - Real.pi / 6 := by push_cast; ring
    rw [e, Real.sin_pi_sub, Real.sin_pi_div_six]
    norm_num
  have hV1 : collocatedV (travellingSineV 1) (Real.pi / 6) (Real.pi / 2) 1
        (⟨1, by norm_num⟩ : Fin 4) = -Real.sqrt 3 / 2 := by
    unfold collocatedV travellingSineV
    simp only [Nat.cast_one, one_mul]
    have e : Real.pi / 2 - Real.pi / 6 = Real.pi / 3 := by ring
    rw [e, Real.sin_pi_div_three]
    ring
  unfold collocatedUUpdateResidual dPlus
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hU1, hU0, hVsucc, hV1]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- Collocated sampling does not inherit the staggered bound:
for some admissible smooth periodic solution and some grid, the
collocated `u` residual strictly exceeds the staggered
consistency bound at the same data. The centred-difference
constant belongs to the staggered locations only. -/
theorem exists_collocatedResidual_exceeding_consistencyEta :
    ∃ (N : ℕ) (h dt c L Mt Mx : ℝ) (u v : ℝ → ℝ → ℝ) (n : ℕ),
      0 < N ∧ 0 < h ∧ 0 < dt ∧ 0 < c ∧ L = (N : ℝ) * h ∧
        0 ≤ Mt ∧ 0 ≤ Mx ∧ isSmoothPeriodicSolution L c Mt Mx u v ∧
        consistencyEta L dt c Mt Mx h <
          weightedNorm h (collocatedUUpdateResidual (N := N) u v h c dt n) := by
  refine ⟨4, Real.pi / 2, Real.pi / 6, 1, 2 * Real.pi, 1, 1,
    travellingSineU 1, travellingSineV 1, 0, by norm_num,
    div_pos Real.pi_pos (by norm_num), div_pos Real.pi_pos (by norm_num),
    by norm_num, ?_, by norm_num, by norm_num, ?_, ?_⟩
  · push_cast
    ring
  · have hsol := travellingSine_smooth_general 1 one_pos
    rwa [one_pow] at hsol
  · have hs174 : Real.sqrt 3 < 1.74 := by
      rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1.74)]
      norm_num
    have hsingle := weightedNorm_single_le (h := Real.pi / 2)
      (div_nonneg Real.pi_pos.le (by norm_num))
      (collocatedUUpdateResidual (N := 4) (travellingSineU 1) (travellingSineV 1)
        (Real.pi / 2) 1 (Real.pi / 6) 0) (⟨1, by norm_num⟩ : Fin 4)
    rw [collocated_residual_one] at hsingle
    have habs : |(2 * Real.sqrt 3 - 5) / 6| = (5 - 2 * Real.sqrt 3) / 6 := by
      have hs2 : Real.sqrt 3 < 2 := by
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [abs_of_nonpos (by linarith [hs2])]
      ring
    rw [habs] at hsingle
    have hLBnn : 0 ≤ Real.sqrt (Real.pi / 2) * ((5 - 2 * Real.sqrt 3) / 6) := by
      apply mul_nonneg (Real.sqrt_nonneg _)
      apply div_nonneg _ (by norm_num)
      linarith [hs174]
    have heta_lt : consistencyEta (2 * Real.pi) (Real.pi / 6) 1 1 1 (Real.pi / 2) <
        Real.sqrt (Real.pi / 2) * ((5 - 2 * Real.sqrt 3) / 6) := by
      refine lt_of_pow_lt_pow_left₀ 2 hLBnn ?_
      have heta_eq : consistencyEta (2 * Real.pi) (Real.pi / 6) 1 1 1 (Real.pi / 2) =
          Real.sqrt (2 * Real.pi) *
            ((Real.pi / 6) * ((Real.pi / 6) ^ 2 + (Real.pi / 2) ^ 2) / 24) := by
        unfold consistencyEta
        ring
      have hLBsq : (Real.sqrt (Real.pi / 2) * ((5 - 2 * Real.sqrt 3) / 6)) ^ 2 =
          (Real.pi / 2) * ((5 - 2 * Real.sqrt 3) / 6) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (div_nonneg Real.pi_pos.le (by norm_num))]
      rw [heta_eq, hLBsq]
      have hA : (Real.pi / 6) * ((Real.pi / 6) ^ 2 + (Real.pi / 2) ^ 2) / 24 =
          5 * Real.pi ^ 3 / 2592 := by ring
      rw [hA]
      have hpi6 : Real.pi ^ 6 < 977 := by
        have h1 : Real.pi ^ 6 ≤ (3.1416 : ℝ) ^ 6 :=
          pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 6
        exact lt_of_le_of_lt h1 (by norm_num)
      have eL : (Real.sqrt (2 * Real.pi) * (5 * Real.pi ^ 3 / 2592)) ^ 2 =
          Real.pi * (50 * Real.pi ^ 6 / 2592 ^ 2) := by
        rw [mul_pow, Real.sq_sqrt (by linarith [Real.pi_pos])]
        ring
      calc (Real.sqrt (2 * Real.pi) * (5 * Real.pi ^ 3 / 2592)) ^ 2
          = Real.pi * (50 * Real.pi ^ 6 / 2592 ^ 2) := eL
        _ < Real.pi * ((5 - 2 * Real.sqrt 3) ^ 2 / 72) := by
            apply mul_lt_mul_of_pos_left _ Real.pi_pos
            have hbase : (1.52 : ℝ) ≤ 5 - 2 * Real.sqrt 3 := by linarith [hs174]
            have hsq : (1.52 : ℝ) ^ 2 ≤ (5 - 2 * Real.sqrt 3) ^ 2 :=
              pow_le_pow_left₀ (by norm_num) hbase 2
            linarith [hpi6, hsq]
        _ = (Real.pi / 2) * ((5 - 2 * Real.sqrt 3) / 6) ^ 2 := by ring
    exact lt_of_lt_of_le heta_lt hsingle

end MathlibExt.Analysis.Numerical.PeriodicYeeResidual
