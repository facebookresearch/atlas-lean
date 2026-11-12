/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.TuringPatterns
public import MathlibExt.Analysis.PDE.SemilinearFlow.Interface
public import MathlibExt.Analysis.PDE.SemilinearFlow.Instability
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Nonlinear Turing instability from an unstable Neumann eigenmode

`MathlibExt.Biology.Dynamics.TuringPatterns` proves the *linear* theory of diffusion-driven
instability for `u_t = D u_xx + f(u)`: the dispersion relation, the unstable band, and the
unstable Neumann modes `cos(k_n x)`, `k_n = n π / L`, on `[0, L]`. Its docstring leaves the
linearization principle open. This file closes it under explicit assumptions: an unstable Neumann
mode makes the homogeneous steady state nonlinearly (Lyapunov) unstable for the reaction–diffusion
flow, via the linearized-instability theorem of
`MathlibExt.Analysis.PDE.SemilinearFlow.Instability`.

## Setting

The phase space is `C([0, L]; ℝ²)` with the sup norm, the frozen space of the PDE-01 interface
(`MathlibExt.Analysis.PDE.SemilinearFlow.Interface`) with `Ω = (0, L)` and two species.
Neither the Neumann heat semigroup nor the local flow of the Turing system is constructed here.
They enter as hypotheses:

* **spectral input**: `IsUnstableMode J d_u d_v k_n`, as proved in `TuringPatterns` (e.g. by
  `isUnstableMode_neumannWavenumber_iff`), in the Turing regime `tr J < 0`, `d_u, d_v ≥ 0`;
* **semigroup**: the linearized semigroup `S` acts on the Neumann mode through the modal ODE
  `c' = (J - k_n² D) c` (`ActsByModalODE`, which is what `Δ_N cos(k_n x) = -k_n² cos(k_n x)`
  gives), and has a growth bound `‖S t‖ ≤ M e^{ω t}` with `ω < p λ`. Here `λ` is the growth rate
  of the mode and `p > 1` the order of the nonlinear remainder. For a general C₀ semigroup the
  spectrum of the generator does not bound `‖S t‖`, so this bound is assumed rather than derived;
* **differentiability**: the kinetics `f` have Jacobian `J` at the steady state with a Hölder
  remainder of order `p`. From it, `exists_norm_timeMap_sub_le` *derives* the expansion
  `Φ T (u₀ + y) = u₀ + S T y + O(‖y‖ᵖ)` of the time-`T` map in the PDE-01 mild formulation;
* **flow**: mild solutions on `[0, T]` from a ball around the steady state, plus the step
  identity of the semiflow (what the PDE-01 local-flow instantiation for the Turing system
  provides).

## Main results

* `exists_growthRate_of_isUnstableMode`: in the Turing regime an unstable mode has a *real*
  positive growth rate `growthRate J d_u d_v k` with a real eigenvector (Turing instabilities
  do not oscillate). This is what lets the real phase space be used.
* `ActsByModalODE.apply_eigen`: `S t (cos(k_n ·) v) = e^{λ t} cos(k_n ·) v` for an eigenvector `v`.
* `exists_norm_timeMap_sub_le`: time-map expansion from a Hölder-differentiable reaction
  (Duhamel, Lipschitz dependence on data, Grönwall).
* `norm_nemytskii_sub_le`: the Nemytskii reaction term inherits the Hölder remainder, with
  derivative `pointwiseMatrix J`.
* `exists_escape_of_isUnstableMode`: nonlinear instability from an unstable Neumann mode, given
  the time-map expansion.
* `exists_escape_of_isUnstableMode_of_mild`: the same with the expansion derived from the
  kinetics and the mild formulation.

## Not covered

Constructing the Neumann semigroup and proving `ActsByModalODE` and the growth bound for it
(its spectral bound is the largest Neumann growth rate, which needs completeness of the cosine
modes), and the local flow of the Turing system. An unstable *continuum* wavenumber is not
enough: the hypothesis is on an admissible Neumann wavenumber `k_n`.

## References

* A. M. Turing, *The chemical basis of morphogenesis*, Phil. Trans. R. Soc. Lond. B 237 (1952)
  37–72.
* D. Henry, *Geometric Theory of Semilinear Parabolic Equations*, Lecture Notes in Math. 840,
  Springer (1981), §5.1.
* J. Shatah and W. Strauss, *Spectral condition for instability*, Contemp. Math. 255 (2000),
  189–198.
* J. D. Murray, *Mathematical Biology II*, 3rd ed., Springer (2003), ch. 2.
-/

@[expose] public section

open Matrix Set MeasureTheory
open scoped NNReal

namespace MathlibExt.Biology.Dynamics.TuringInstability

open MathlibExt.Biology.Dynamics.TuringPatterns
open MathlibExt.Analysis.PDE.SemilinearFlow

/-! ### The real growth rate of a Turing-unstable mode -/

/-- The **growth rate** of the Fourier mode of wavenumber `k`: the larger root
`λ = (τ + √(τ² - 4 δ)) / 2` of the characteristic polynomial `λ² - τ λ + δ` of the mode matrix
`J - k² D`, where `τ = tr (J - k² D)` and `δ = det (J - k² D)`. When `δ < 0` (the Turing case)
it is a positive real eigenvalue of `J - k² D` (`exists_mulVec_eq_growthRate_smul`,
`growthRate_pos`). It is a root whenever `τ² - 4 δ ≥ 0` (`growthRate_sq_sub`); for a negative
discriminant `Real.sqrt` truncates to `0` and the value is only the common real part `τ / 2`. -/
noncomputable def growthRate (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv k : ℝ) : ℝ :=
  ((modeMatrix J du dv k).trace +
    Real.sqrt ((modeMatrix J du dv k).trace ^ 2 - 4 * (modeMatrix J du dv k).det)) / 2

/-- A negative determinant makes the growth rate positive. -/
theorem growthRate_pos {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv k : ℝ}
    (h : (modeMatrix J du dv k).det < 0) : 0 < growthRate J du dv k := by
  unfold growthRate
  set τ := (modeMatrix J du dv k).trace
  set δ := (modeMatrix J du dv k).det
  have hs : |τ| < Real.sqrt (τ ^ 2 - 4 * δ) :=
    Real.lt_sqrt (abs_nonneg _) |>.2 (by rw [sq_abs]; linarith)
  have := neg_abs_le τ
  linarith

/-- The growth rate is a root of the characteristic polynomial when the discriminant is
nonnegative, in particular when the determinant is negative. -/
theorem growthRate_sq_sub {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv k : ℝ}
    (h : 0 ≤ (modeMatrix J du dv k).trace ^ 2 - 4 * (modeMatrix J du dv k).det) :
    growthRate J du dv k ^ 2 - (modeMatrix J du dv k).trace * growthRate J du dv k +
      (modeMatrix J du dv k).det = 0 := by
  unfold growthRate
  set τ := (modeMatrix J du dv k).trace
  set δ := (modeMatrix J du dv k).det
  have hs := Real.sq_sqrt h
  linear_combination hs / 4

/-- When `det (J - k² D) < 0`, the growth rate is a real eigenvalue of `J - k² D` with a real
eigenvector. -/
theorem exists_mulVec_eq_growthRate_smul {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv k : ℝ}
    (h : (modeMatrix J du dv k).det < 0) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ modeMatrix J du dv k *ᵥ v = growthRate J du dv k • v := by
  set M := modeMatrix J du dv k
  set r := growthRate J du dv k
  have hroot := growthRate_sq_sub (J := J) (du := du) (dv := dv) (k := k)
    (by nlinarith [sq_nonneg M.trace])
  have hdet : (r • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det = 0 := by
    rw [← hroot]
    simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.smul_apply, Matrix.sub_apply]
    ring
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨v, hv, ?_⟩
  simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero, eq_comm]
    using hMv

/-- **Turing instabilities are real.** In the Turing regime (`tr J < 0`, `d_u, d_v ≥ 0`), an
unstable mode has determinant `det (J - k² D) < 0`, so its growth rate is a positive real
eigenvalue of `J - k² D` with a real eigenvector: the unstable mode grows without oscillating. -/
theorem exists_growthRate_of_isUnstableMode {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv k : ℝ}
    (htr : J.trace < 0) (hdu : 0 ≤ du) (hdv : 0 ≤ dv) (hk : IsUnstableMode J du dv k) :
    0 < growthRate J du dv k ∧
      ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ modeMatrix J du dv k *ᵥ v = growthRate J du dv k • v := by
  have hdet : (modeMatrix J du dv k).det < 0 := by
    rw [det_modeMatrix]
    exact (isUnstableMode_iff_dispersionDet_neg htr hdu hdv k).1 hk
  exact ⟨growthRate_pos hdet, exists_mulVec_eq_growthRate_smul hdet⟩

/-! ### Neumann modes in the phase space `C([0, L]; ℝ²)` -/

/-- The real **Neumann mode** `x ↦ cos(k_n x) w` on `[0, L]`, `k_n = n π / L`, as an element of
the phase space `C([0, L]; ℝ²)` (sup norm) of the frozen PDE-01 setting with `Ω = (0, L)` and two
species. It has zero flux at both ends (`hasDerivAt_fourierMode_neumannWavenumber`) and
`Δ_N cos(k_n x) = -k_n² cos(k_n x)`. -/
noncomputable def neumannMode (L : ℝ) (n : ℕ) (w : Fin 2 → ℝ) : C(Icc (0 : ℝ) L, Fin 2 → ℝ) :=
  ⟨fun x => Real.cos (neumannWavenumber L n * x) • w, by fun_prop⟩

@[simp]
theorem neumannMode_apply (L : ℝ) (n : ℕ) (w : Fin 2 → ℝ) (x : Icc (0 : ℝ) L) :
    neumannMode L n w x = Real.cos (neumannWavenumber L n * x) • w :=
  rfl

theorem neumannMode_smul (L : ℝ) (n : ℕ) (c : ℝ) (w : Fin 2 → ℝ) :
    neumannMode L n (c • w) = c • neumannMode L n w := by
  ext x i
  simp only [neumannMode_apply, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- On a nonempty interval (`0 ≤ L`) the Neumann mode has the sup norm of its amplitude. -/
theorem norm_neumannMode {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (w : Fin 2 → ℝ) :
    ‖neumannMode L n w‖ = ‖w‖ := by
  refine le_antisymm ((ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => ?_) ?_
  · rw [neumannMode_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  · have := (neumannMode L n w).norm_coe_le_norm ⟨0, le_rfl, hL⟩
    simpa using this

/-- A Neumann mode with nonzero amplitude is a nonzero element of the phase space. -/
theorem neumannMode_ne_zero {L : ℝ} (hL : 0 ≤ L) (n : ℕ) {w : Fin 2 → ℝ} (hw : w ≠ 0) :
    neumannMode L n w ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_neumannMode hL]
  exact norm_ne_zero_iff.2 hw

/-! ### The linearized semigroup on a Neumann mode -/

/-- A family `S` of bounded operators on `C([0, L]; ℝ²)` **acts on the Neumann mode `n` through
the modal ODE** of the matrix `M`: for every amplitude `w` there is a solution `c` of
`c' = M c`, `c 0 = w`, with `S t (cos(k_n ·) w) = cos(k_n ·) c t` for all `t ≥ 0`.

For the semigroup generated by the linearization `D Δ_N + J` of the Turing system this holds
with `M = J - k_n² D`, because `Δ_N cos(k_n x) = -k_n² cos(k_n x)` turns the linearized PDE on
the mode into that ODE (`fourierMode_isLinearizedSolution_iff`). Constructing the Neumann
semigroup is outside PDE-01, so this is the semigroup hypothesis of the instability theorems. -/
def ActsByModalODE {L : ℝ} (S : ℝ≥0 → C(Icc (0 : ℝ) L, Fin 2 → ℝ) →L[ℝ] C(Icc (0 : ℝ) L, Fin 2 → ℝ))
    (n : ℕ) (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∀ w : Fin 2 → ℝ, ∃ c : ℝ → Fin 2 → ℝ, c 0 = w ∧ (∀ t, HasDerivAt c (M *ᵥ c t) t) ∧
    ∀ t : ℝ≥0, S t (neumannMode L n w) = neumannMode L n (c t)

/-- **Eigenfunctions of the linearized semigroup.** If `S` acts on the Neumann mode `n` through
the modal ODE of `M` and `M v = r v`, then `cos(k_n ·) v` is an eigenfunction of every `S t`
with eigenvalue `e^{r t}` (uniqueness for the linear ODE `c' = M c`). -/
theorem ActsByModalODE.apply_eigen {L : ℝ}
    {S : ℝ≥0 → C(Icc (0 : ℝ) L, Fin 2 → ℝ) →L[ℝ] C(Icc (0 : ℝ) L, Fin 2 → ℝ)} {n : ℕ}
    {M : Matrix (Fin 2) (Fin 2) ℝ} (hS : ActsByModalODE S n M) {r : ℝ} {v : Fin 2 → ℝ}
    (hv : M *ᵥ v = r • v) (t : ℝ≥0) :
    S t (neumannMode L n v) = Real.exp (r * t) • neumannMode L n v := by
  obtain ⟨c, hc0, hc, hSc⟩ := hS v
  set A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
  have hA : ∀ x, A x = M *ᵥ x := fun _ => rfl
  have he : ∀ s, HasDerivAt (fun s => Real.exp (r * s) • v) (M *ᵥ (Real.exp (r * s) • v)) s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (r * s)) (Real.exp (r * s) * r) s := by
      simpa using ((hasDerivAt_id s).const_mul r).exp
    convert h1.smul_const v using 1
    rw [Matrix.mulVec_smul, hv, smul_smul]
  have heq : EqOn c (fun s => Real.exp (r * s) • v) (Icc 0 t) := by
    refine ODE_solution_unique (v := fun _ x => A x) (K := ‖A‖₊) (fun _ => A.lipschitzWith)
      (fun s _ => (hc s).continuousAt.continuousWithinAt)
      (fun s _ => by simpa [hA] using (hc s).hasDerivWithinAt)
      (fun s _ => (he s).continuousAt.continuousWithinAt)
      (fun s _ => by simpa [hA] using (he s).hasDerivWithinAt) (by simp [hc0])
  rw [hSc, show c t = Real.exp (r * t) • v from heq ⟨t.2, le_rfl⟩, neumannMode_smul]

/-! ### Nonlinear instability from a time-map expansion -/

/-- Powers of a semigroup at a fixed time: `(S T)ᵐ = S (m T)`. -/
private theorem pow_eq_nsmul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {S : ℝ≥0 → X →L[ℝ] X} (hS : IsC0Semigroup S) (T : ℝ≥0) (m : ℕ) :
    S T ^ m = S (m * T) := by
  induction m with
  | zero => simp [hS.map_zero]
  | succ m ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_one_mul, hS.map_add, ContinuousLinearMap.mul_def]

/-- **Nonlinear Turing instability, time-map form.**

Let `J` be the Jacobian of the kinetics at a homogeneous steady state `u₀` with `tr J < 0`,
`d_u, d_v ≥ 0`, and let the Neumann mode `n` on `[0, L]` be linearly unstable
(`IsUnstableMode J d_u d_v k_n`, e.g. from `isUnstableMode_neumannWavenumber_iff`). The phase
space is `C([0, L]; ℝ²)` with the sup norm. Assume:

* **semigroup**: the linearized semigroup `S` is a C₀ semigroup acting on the Neumann mode `n`
  through the modal ODE of `J - k_n² D` (`ActsByModalODE`), with growth bound
  `‖S t‖ ≤ M e^{ω t}` where `ω < p λ` for the growth rate `λ = growthRate J d_u d_v k_n`
  (e.g. `ω = λ + ε` when the mode `n` is dominant);
* **differentiability**: the time-`T` map of the nonlinear flow `Φ` is
  `u₀ + S T y + O(‖y‖ᵖ)` on the ball `‖y‖ ≤ ρ` (derived from a Hölder-differentiable reaction in
  `exists_norm_timeMap_sub_le`);
* **flow**: `Φ` starts at the identity and steps by its time-`T` map along orbits that stay in
  the ball.

Then `u₀` is nonlinearly unstable: some distance `ε > 0` is reached at a nonnegative time from
initial data arbitrarily close to `u₀`. -/
theorem exists_escape_of_isUnstableMode {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv L : ℝ} {n : ℕ}
    (htr : J.trace < 0) (hdu : 0 ≤ du) (hdv : 0 ≤ dv) (hL : 0 ≤ L)
    (hunst : IsUnstableMode J du dv (neumannWavenumber L n))
    {S : ℝ≥0 → C(Icc (0 : ℝ) L, Fin 2 → ℝ) →L[ℝ] C(Icc (0 : ℝ) L, Fin 2 → ℝ)}
    (hS : IsC0Semigroup S) (hmode : ActsByModalODE S n (modeMatrix J du dv (neumannWavenumber L n)))
    {M ω p : ℝ} (hgrowth : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (ω * t)) (hp : 1 < p)
    (hω : ω < p * growthRate J du dv (neumannWavenumber L n))
    {Φ : ℝ → C(Icc (0 : ℝ) L, Fin 2 → ℝ) → C(Icc (0 : ℝ) L, Fin 2 → ℝ)}
    {u₀ : C(Icc (0 : ℝ) L, Fin 2 → ℝ)} {T : ℝ≥0} {ρ C : ℝ} (hT : 0 < T) (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (m : ℕ) (x : C(Icc (0 : ℝ) L, Fin 2 → ℝ)),
      (∀ k ≤ m, ‖Φ (k * T) x - u₀‖ ≤ ρ) → Φ ((m + 1) * T) x = Φ T (Φ (m * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - S T y‖ ≤ C * ‖y‖ ^ p) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - u₀‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖Φ t x - u₀‖ := by
  obtain ⟨hr, v, hv0, hv⟩ := exists_growthRate_of_isUnstableMode htr hdu hdv hunst
  set r := growthRate J du dv (neumannWavenumber L n)
  have hT' : (0 : ℝ) < T := hT
  have hnorm : ‖Real.exp (r * T)‖ = Real.exp (r * T) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Instability.exists_escape_of_timeMap (𝕜 := ℝ) (L := S T) (ν := Real.exp (r * T))
    (M := M) (μ := Real.exp (ω * T)) T.2 hρ hC hp hΦ0 hstep hrem
    (neumannMode_ne_zero hL n hv0) (hmode.apply_eigen hv T) ?_ (Real.exp_pos _).le ?_ ?_
  · rw [hnorm]; exact Real.one_lt_exp_iff.2 (by positivity)
  · rw [hnorm, ← Real.exp_mul, Real.exp_lt_exp]; nlinarith
  · intro m
    rw [pow_eq_nsmul hS, ← Real.exp_nat_mul]
    refine (hgrowth _).trans_eq ?_
    push_cast; ring_nf

/-! ### The time-map expansion from a differentiable reaction -/

/-- **Integral Grönwall inequality.** A continuous `ψ ≥ 0` with
`ψ t ≤ a + K ∫₀ᵗ ψ` on `[0, T]` (`K ≥ 0`) satisfies `ψ t ≤ a exp (K t)` there. (Same statement
as the private helper of `MathlibExt.Analysis.PDE.SemilinearFlow.Interface`.) -/
private theorem le_mul_exp_of_le_add_mul_integral {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hψ0 : ∀ t, 0 ≤ ψ t) {a K T : ℝ} (hK : 0 ≤ K)
    (h : ∀ t ∈ Icc 0 T, ψ t ≤ a + K * ∫ s in (0 : ℝ)..t, ψ s) :
    ∀ t ∈ Icc 0 T, ψ t ≤ a * Real.exp (K * t) := by
  set Ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, ψ s with hΨ_def
  have hd : ∀ t, HasDerivAt Ψ (ψ t) t := fun t => (hψ.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hΨ0 : ∀ t ∈ Icc 0 T, 0 ≤ Ψ t := fun t ht =>
    intervalIntegral.integral_nonneg ht.1 fun s _ => hψ0 s
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le (f := Ψ) (f' := ψ) (δ := 0) (K := K)
    (ε := a) (a := 0) (b := T) (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt) (by simp [Ψ]) (fun t ht => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hψ0 t),
        abs_of_nonneg (hΨ0 t ⟨ht.1, ht.2.le⟩)]
      linarith [h t ⟨ht.1, ht.2.le⟩])
  intro t ht
  have h1 := hG t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (hΨ0 t ht), sub_zero] at h1
  have h2 : ψ t ≤ a + K * gronwallBound 0 K a t :=
    (h t ht).trans (by linarith [mul_le_mul_of_nonneg_left h1 hK])
  rcases eq_or_ne K 0 with rfl | hK0
  · simpa using h2
  · rw [gronwallBound_of_K_ne_0 hK0] at h2
    have : a + K * (0 * Real.exp (K * t) + a / K * (Real.exp (K * t) - 1)) =
        a * Real.exp (K * t) := by field_simp; ring
    linarith

/-- **Time-map expansion from a Hölder-differentiable reaction** (the differentiability input
of linearized instability, in the PDE-01 mild formulation).

Let `SA` be a C₀ semigroup on a real Banach space `X` (for the Turing system, the Neumann heat
semigroup `e^{t D Δ_N}` on `C(Ω̄; ℝ²)`) and `F` a reaction term that is Lipschitz on bounded sets.
Let `u₀` be an equilibrium: `SA t u₀ = u₀` (a homogeneous state is fixed by the Neumann heat
semigroup) and `F u₀ = 0`. Suppose `F` is differentiable at `u₀` with a Hölder remainder:
`‖F (u₀ + z) - F u₀ - B z‖ ≤ K ‖z‖ᵖ` for `‖z‖ ≤ r`. Let `S` be the linearized semigroup, i.e.
`t ↦ S t y` is the mild solution of `w' = A w + B w`, `w 0 = y`. Let `Φ` be the nonlinear flow on
`[0, T]` from the ball `‖x - u₀‖ ≤ ρ₀`, bounded by `R` there. Then the time-`T` map satisfies
`‖Φ T (u₀ + y) - u₀ - S T y‖ ≤ C ‖y‖ᵖ` for `‖y‖ ≤ ρ`, for some `ρ > 0` and `C ≥ 0`.

The proof writes the error `e t = Φ t x - u₀ - S t y` as a Duhamel integral of
`F (Φ s x) - B (S s y) = [Hölder remainder] + B (e s)`, bounds `‖Φ s x - u₀‖` by Lipschitz
dependence on initial data (`exists_norm_sub_le_of_norm_le`) and closes with Grönwall. -/
theorem exists_norm_timeMap_sub_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] {SA S : ℝ≥0 → X →L[ℝ] X} {F : X → X} {B : X →L[ℝ] X}
    {Φ : ℝ → X → X} {u₀ : X} {T ρ₀ R r K p : ℝ}
    (hSA : IsC0Semigroup SA)
    (hF : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (Metric.closedBall 0 R))
    (hT : 0 ≤ T) (hρ₀ : 0 < ρ₀) (hr : 0 < r) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hSAu₀ : ∀ t, SA t u₀ = u₀) (hFu₀ : F u₀ = 0)
    (hFrem : ∀ z, ‖z‖ ≤ r → ‖F (u₀ + z) - F u₀ - B z‖ ≤ K * ‖z‖ ^ p)
    (hS : ∀ y, IsMildSolution SA B y T fun t => S t.toNNReal y)
    (hΦ : ∀ x, ‖x - u₀‖ ≤ ρ₀ →
      IsMildSolution SA F x T (fun t => Φ t x) ∧ ∀ t ∈ Icc 0 T, ‖Φ t x‖ ≤ R) :
    ∃ ρ > 0, ∃ C ≥ 0, ∀ y, ‖y‖ ≤ ρ →
      ‖Φ T (u₀ + y) - u₀ - S T.toNNReal y‖ ≤ C * ‖y‖ ^ p := by
  -- The equilibrium is a mild solution.
  have hequil : IsMildSolution SA F u₀ T fun _ => u₀ :=
    ⟨continuousOn_const, fun t _ => by simp [hFu₀], fun t _ => by simp [duhamel, hFu₀, hSAu₀]⟩
  obtain ⟨Cl, hCl0, hCl⟩ := exists_norm_sub_le_of_norm_le hSA hF (max R ‖u₀‖) T
  obtain ⟨M₀, hM₀⟩ := hSA.locally_bounded T.toNNReal
  set Ms := max M₀ 0
  have hMs0 : 0 ≤ Ms := le_max_right _ _
  have hMs : ∀ τ : ℝ≥0, (τ : ℝ) ≤ T → ‖SA τ‖ ≤ Ms := fun τ hτ =>
    (hM₀ τ (Real.le_toNNReal_iff_coe_le hT |>.2 hτ)).trans (le_max_left _ _)
  set b := Ms * ‖B‖
  have hb : 0 ≤ b := by positivity
  refine ⟨min ρ₀ (r / (Cl + 1)), lt_min hρ₀ (by positivity),
    Ms * K * T * Cl ^ p * Real.exp (b * T), by positivity, fun y hy => ?_⟩
  set x := u₀ + y with hx_def
  have hx : ‖x - u₀‖ ≤ ρ₀ := by simpa [x] using hy.trans (min_le_left _ _)
  obtain ⟨hu, hubd⟩ := hΦ x hx
  have hw := hS y
  -- Distance of the nonlinear orbit from the equilibrium.
  have hdist : ∀ s ∈ Icc 0 T, ‖Φ s x - u₀‖ ≤ Cl * ‖y‖ := by
    intro s hs
    have := hCl x u₀ (fun t => Φ t x) (fun _ => u₀) hu hequil
      (fun t ht => ⟨(hubd t ht).trans (le_max_left _ _), le_max_right _ _⟩) s hs
    simpa [x] using this
  have hsmall : Cl * ‖y‖ ≤ r := by
    have h1 : ‖y‖ ≤ r / (Cl + 1) := hy.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg y]
  -- The error and its Duhamel representation.
  set e : ℝ → X := fun t => Φ t x - u₀ - S t.toNNReal y with he_def
  have he_cont : ContinuousOn e (Icc 0 T) := (hu.1.sub continuousOn_const).sub hw.1
  have he_eq : ∀ t ∈ Icc 0 T, e t =
      ∫ s in (0 : ℝ)..t, SA (t - s).toNNReal (F (Φ s x) - B (S s.toNNReal y)) := by
    intro t ht
    have hsub : (fun s => SA (t - s).toNNReal (F (Φ s x) - B (S s.toNNReal y))) =
        fun s => SA (t - s).toNNReal (F (Φ s x)) - SA (t - s).toNNReal (B (S s.toNNReal y)) :=
      funext fun s => map_sub _ _ _
    rw [hsub, intervalIntegral.integral_sub (hu.2.1 t ht) (hw.2.1 t ht)]
    have h1 : Φ t x = _ := hu.2.2 t ht
    have h2 : S t.toNNReal y = _ := hw.2.2 t ht
    simp only [e]
    rw [h1, h2]
    simp only [duhamel, x, map_add, hSAu₀]
    abel
  -- Grönwall for the norm of the error, extended continuously off `[0, T]`.
  set ψ : ℝ → ℝ := fun t => ‖e (projIcc 0 T hT t)‖ with hψ_def
  have hψc : Continuous ψ :=
    (he_cont.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun t => (projIcc 0 T hT t).2).norm
  have hψe : ∀ t ∈ Icc 0 T, ψ t = ‖e t‖ := fun t ht => by simp [ψ, projIcc_of_mem hT ht]
  set c := K * (Cl * ‖y‖) ^ p with hc_def
  have hc : 0 ≤ c := by positivity
  have hineq : ∀ t ∈ Icc 0 T, ψ t ≤ Ms * c * T + b * ∫ s in (0 : ℝ)..t, ψ s := by
    intro t ht
    rw [hψe t ht, he_eq t ht]
    have hbound : ∀ s ∈ Ioc 0 t,
        ‖SA (t - s).toNNReal (F (Φ s x) - B (S s.toNNReal y))‖ ≤ Ms * c + b * ψ s := by
      intro s hs
      have hsT : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
      have hsplit : F (Φ s x) - B (S s.toNNReal y) =
          (F (u₀ + (Φ s x - u₀)) - F u₀ - B (Φ s x - u₀)) + B (e s) := by
        simp only [e, hFu₀, map_sub, add_sub_cancel]
        abel
      have hR : ‖F (u₀ + (Φ s x - u₀)) - F u₀ - B (Φ s x - u₀)‖ ≤ c :=
        (hFrem _ ((hdist s hsT).trans hsmall)).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hdist s hsT) hp) hK)
      have hSn : ‖SA (t - s).toNNReal‖ ≤ Ms := hMs _ (by
        rw [Real.coe_toNNReal']
        exact max_le (by linarith [hs.1, ht.2]) hT)
      calc _ ≤ ‖SA (t - s).toNNReal‖ * ‖F (Φ s x) - B (S s.toNNReal y)‖ := (SA _).le_opNorm _
        _ ≤ Ms * (c + ‖B‖ * ‖e s‖) := by
          refine mul_le_mul hSn ?_ (norm_nonneg _) hMs0
          rw [hsplit]
          exact (norm_add_le _ _).trans (add_le_add hR (B.le_opNorm _))
        _ = Ms * c + b * ψ s := by rw [hψe s hsT]; ring
    have hint := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht.1
      (Filter.Eventually.of_forall hbound)
      ((continuous_const.add (continuous_const.mul hψc)).intervalIntegrable 0 t)
    have hbψ : Continuous fun s => b * ψ s := continuous_const.mul hψc
    rw [intervalIntegral.integral_add (intervalIntegrable_const (μ := volume))
      (hbψ.intervalIntegrable 0 t), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, smul_eq_mul, sub_zero] at hint
    have : t * (Ms * c) ≤ Ms * c * T := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left ht.2 (by positivity)
    linarith
  have hG := le_mul_exp_of_le_add_mul_integral hψc (fun t => norm_nonneg _) hb hineq T
    ⟨hT, le_rfl⟩
  rw [hψe T ⟨hT, le_rfl⟩] at hG
  calc ‖Φ T (u₀ + y) - u₀ - S T.toNNReal y‖ = ‖e T‖ := rfl
    _ ≤ Ms * c * T * Real.exp (b * T) := hG
    _ = Ms * K * T * Cl ^ p * Real.exp (b * T) * ‖y‖ ^ p := by
      rw [hc_def, Real.mul_rpow hCl0 (norm_nonneg _)]
      ring

/-! ### The Turing reaction term at a homogeneous steady state -/

/-- The pointwise action `y ↦ (x ↦ J y(x))` of a `2 × 2` matrix on `C(K; ℝ²)`. At a homogeneous
steady state `a` with kinetics Jacobian `J`, this is the derivative of the Nemytskii reaction
term `u ↦ f ∘ u` (`norm_nemytskii_sub_le`). -/
noncomputable def pointwiseMatrix (K : Type*) [TopologicalSpace K] [CompactSpace K]
    (J : Matrix (Fin 2) (Fin 2) ℝ) : C(K, Fin 2 → ℝ) →L[ℝ] C(K, Fin 2 → ℝ) :=
  (LinearMap.toContinuousLinearMap (Matrix.mulVecLin J)).compLeftContinuous ℝ K

@[simp]
theorem pointwiseMatrix_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (J : Matrix (Fin 2) (Fin 2) ℝ) (y : C(K, Fin 2 → ℝ)) (x : K) :
    pointwiseMatrix K J y x = J *ᵥ y x :=
  rfl

/-- **Differentiability of the Nemytskii reaction term.** If the kinetics `f : ℝ² → ℝ²` have
Jacobian `J` at `a` with a Hölder remainder, `‖f (a + z) - f a - J z‖ ≤ C ‖z‖ᵖ` for `‖z‖ ≤ r`,
then the reaction term `u ↦ f ∘ u` on `C(K; ℝ²)` (sup norm) has derivative `pointwiseMatrix K J`
at the constant state `a`, with the same remainder bound. -/
theorem norm_nemytskii_sub_le {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hfc : Continuous f) {a : Fin 2 → ℝ}
    {J : Matrix (Fin 2) (Fin 2) ℝ} {r C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hf : ∀ z, ‖z‖ ≤ r → ‖f (a + z) - f a - J *ᵥ z‖ ≤ C * ‖z‖ ^ p)
    (y : C(K, Fin 2 → ℝ)) (hy : ‖y‖ ≤ r) :
    ‖nemytskii f hfc (ContinuousMap.const K a + y) - nemytskii f hfc (ContinuousMap.const K a) -
      pointwiseMatrix K J y‖ ≤ C * ‖y‖ ^ p := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  have hyx : ‖y x‖ ≤ ‖y‖ := y.norm_coe_le_norm x
  calc ‖f (a + y x) - f a - J *ᵥ y x‖ ≤ C * ‖y x‖ ^ p := hf _ (hyx.trans hy)
    _ ≤ C * ‖y‖ ^ p :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hyx hp) hC

/-! ### Nonlinear Turing instability in the PDE-01 mild formulation -/

/-- **Nonlinear Turing instability (mild formulation).**

The two-species system `u_t = D u_xx + f(u)` on `[0, L]` with Neumann boundary conditions, in
the phase space `C([0, L]; ℝ²)` (sup norm) of PDE-01, at a homogeneous steady state `a`
(`f a = 0`). Hypotheses:

* **spectral input** (from `TuringPatterns`): `tr J < 0`, `d_u, d_v ≥ 0`, and the Neumann
  mode `n` is linearly unstable, `IsUnstableMode J d_u d_v k_n`;
* **differentiability**: the kinetics are Lipschitz on bounded sets and have Jacobian `J` at `a`
  with a Hölder remainder `‖f (a + z) - f a - J z‖ ≤ K ‖z‖ᵖ` (`‖z‖ ≤ r`, `p > 1`; e.g. `f` of
  class `C²` with `p = 2`);
* **semigroups**: the diffusion semigroup `SA` (`e^{t D Δ_N}`) is C₀ and fixes the constant
  state; the linearized semigroup `S` is C₀, its orbits are the mild solutions of
  `w' = D Δ_N w + J w`, it acts on the Neumann mode `n` through the modal ODE of
  `J - k_n² D`, and it has growth bound `‖S t‖ ≤ M e^{ω t}` with `ω < p λ`, where
  `λ = growthRate J d_u d_v k_n`;
* **flow**: `Φ` starts at the identity, steps by its time-`T` map along orbits in the ball
  `‖x - a‖ ≤ ρ₀`, and from that ball gives mild solutions on `[0, T]` bounded by `R`
  (the local-flow instantiation of PDE-01 for the Turing system supplies these).

Then the steady state is nonlinearly unstable. -/
theorem exists_escape_of_isUnstableMode_of_mild {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv L : ℝ}
    {n : ℕ} (htr : J.trace < 0) (hdu : 0 ≤ du) (hdv : 0 ≤ dv) (hL : 0 ≤ L)
    (hunst : IsUnstableMode J du dv (neumannWavenumber L n))
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hfc : Continuous f)
    (hfL : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L f (Metric.closedBall 0 R))
    {a : Fin 2 → ℝ} (hfa : f a = 0) {r K p : ℝ} (hr : 0 < r) (hK : 0 ≤ K) (hp : 1 < p)
    (hf : ∀ z, ‖z‖ ≤ r → ‖f (a + z) - f a - J *ᵥ z‖ ≤ K * ‖z‖ ^ p)
    {SA S : ℝ≥0 → C(Icc (0 : ℝ) L, Fin 2 → ℝ) →L[ℝ] C(Icc (0 : ℝ) L, Fin 2 → ℝ)}
    (hSA : IsC0Semigroup SA) (hSAa : ∀ t, SA t (ContinuousMap.const _ a) = ContinuousMap.const _ a)
    (hS : IsC0Semigroup S) {T : ℝ≥0} (hT : 0 < T)
    (hSmild : ∀ y, IsMildSolution SA (pointwiseMatrix _ J) y T fun t => S t.toNNReal y)
    (hmode : ActsByModalODE S n (modeMatrix J du dv (neumannWavenumber L n)))
    {M ω : ℝ} (hgrowth : ∀ t : ℝ≥0, ‖S t‖ ≤ M * Real.exp (ω * t))
    (hω : ω < p * growthRate J du dv (neumannWavenumber L n))
    {Φ : ℝ → C(Icc (0 : ℝ) L, Fin 2 → ℝ) → C(Icc (0 : ℝ) L, Fin 2 → ℝ)} {ρ₀ R : ℝ}
    (hρ₀ : 0 < ρ₀) (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (m : ℕ) (x : C(Icc (0 : ℝ) L, Fin 2 → ℝ)),
      (∀ k ≤ m, ‖Φ (k * T) x - ContinuousMap.const _ a‖ ≤ ρ₀) →
        Φ ((m + 1) * T) x = Φ T (Φ (m * T) x))
    (hΦ : ∀ x, ‖x - ContinuousMap.const _ a‖ ≤ ρ₀ →
      IsMildSolution SA (nemytskii f hfc) x T (fun t => Φ t x) ∧
        ∀ t ∈ Icc 0 (T : ℝ), ‖Φ t x‖ ≤ R) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - ContinuousMap.const _ a‖ < δ ∧
      ∃ t, 0 ≤ t ∧ ε ≤ ‖Φ t x - ContinuousMap.const _ a‖ := by
  have hFa : nemytskii f hfc (ContinuousMap.const (Icc (0 : ℝ) L) a) = 0 := by
    ext x i; simp [nemytskii, hfa]
  obtain ⟨ρ, hρ, C, hC, hrem⟩ := exists_norm_timeMap_sub_le (S := S) (T := (T : ℝ)) hSA
    (lipschitzOnWith_nemytskii hfc hfL) T.2 hρ₀ hr hK (by linarith) hSAa hFa
    (fun z hz => norm_nemytskii_sub_le hfc hK (by linarith) hf z hz) hSmild hΦ
  refine exists_escape_of_isUnstableMode htr hdu hdv hL hunst hS hmode hgrowth hp hω hT
    (lt_min hρ hρ₀) hC hΦ0 (fun m x hx => hstep m x fun k hk => (hx k hk).trans (min_le_right _ _))
    (fun y hy => ?_)
  simpa using hrem y (hy.trans (min_le_left _ _))

end MathlibExt.Biology.Dynamics.TuringInstability
