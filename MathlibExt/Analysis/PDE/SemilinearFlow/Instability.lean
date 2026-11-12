/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Algebra.Ring.GeomSum

/-!
# Linearized instability for semilinear flows

The instability half of the principle of linearized stability for a semilinear evolution
equation `u' = A u + f(u)` (Henry 1981, §5.1), following the approach of Shatah and Strauss
(2000). Proved here under an eigenvalue hypothesis: an equilibrium whose linearization has an
eigenvalue in the unstable region that dominates the growth of the linear semigroup is
nonlinearly (Lyapunov) unstable.

The flow and its linearized semigroup are not constructed here; they are explicit hypotheses
(construction of the local semiflow and of the analytic semigroup is a separate task). The
assumptions are:

* **Topology.** The phase space is a normed space `X` over `ℝ` or `ℂ` (for a parabolic problem,
  a fractional power space `X^α` of the sectorial operator `A`; Henry, §1.4), and stability is
  measured in its norm. Completeness is only used in the spectral-radius form.
* **Smoothness.** Near the equilibrium `u₀` the time-`T` map of the flow is
  `u₀ + L y + O(‖y‖ᵖ)` with `p > 1` on a ball `‖y‖ ≤ ρ` (for a semilinear problem this is
  expected from `f` being `C¹` with Hölder-continuous derivative of order `p - 1`; that
  derivation is not done here). Only that ball is used: the flow need only step by its
  time-`T` map along orbits whose states at times `0, T, …, nT` all lie in the ball, so a
  local semiflow that exists for time `T` from the ball qualifies.
* **Spectrum.** `L` has an eigenvalue `ν` with `|ν| > 1` and `‖Lⁿ‖ ≤ M μⁿ` with `μ < |ν|ᵖ`.
  On a complex Banach space this holds whenever the spectral radius satisfies `r(L) < |ν|ᵖ`,
  in particular when `|ν| = r(L)`. For the linearized semigroup `S t = e^{t B}` this reads: an
  eigenvalue `κ` of `B` with `Re κ > 0` and a growth bound `‖S t‖ ≤ M e^{ω t}` with
  `ω < p Re κ`.

## Main results

* `exists_escape_of_eigenvalue`: a fixed point of a map with such a linearization is unstable;
  the escaping orbit stays in the ball of radius `ρ` until it escapes.
* `exists_escape_of_timeMap`, `not_lyapunovStable_of_timeMap`: the same for a flow, through its
  time-`T` map.
* `exists_escape_of_semigroup`: the same, stated with the linearized semigroup, its growth
  bound and a generator eigenvalue.
* `exists_escape_of_spectralRadius`, `exists_escape_of_spectralRadius_eq`: spectral-radius and
  dominant-eigenvalue forms of the spectral hypothesis (Gelfand's formula).

## Scope

The general version, with only some spectrum outside the closed unit disk and no eigenvector,
needs approximate eigenvectors at a spectral point of maximal modulus (or a spectral projection
onto the unstable part); it is deferred, so we assume an eigenvector and the growth condition
`μ < |ν|ᵖ`. An unstable *continuum* wavenumber of a reaction–diffusion system is not enough
on a bounded domain: the spectral hypothesis concerns the actual operator, and when no
admissible wavenumber of the domain lies in the unstable band, no Neumann Fourier mode is an
unstable eigenvector (see the tests).

## References

* D. Henry, *Geometric Theory of Semilinear Parabolic Equations*, Lecture Notes in Math. 840,
  Springer (1981), §5.1.
* J. Shatah and W. Strauss, *Spectral condition for instability*, Contemp. Math. 255 (2000),
  189–198.
-/

@[expose] public section

open Filter Finset

namespace MathlibExt.Analysis.PDE.SemilinearFlow.Instability

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Discrete Duhamel formula: `yₙ - Lⁿ y₀ = ∑_{j<n} Lʲ (y_{n-1-j+1} - L y_{n-1-j})`. -/
private theorem duhamel (L : X →L[𝕜] X) (y : ℕ → X) (n : ℕ) :
    y n - (L ^ n) (y 0) =
      ∑ j ∈ range n, (L ^ j) (y (n - 1 - j + 1) - L (y (n - 1 - j))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ', pow_zero, one_apply_eq_self]
    have hsum : ∑ j ∈ range n, (L ^ (j + 1)) (y (n + 1 - 1 - (j + 1) + 1) -
        L (y (n + 1 - 1 - (j + 1)))) = L (y n - (L ^ n) (y 0)) := by
      rw [ih, map_sum]
      refine sum_congr rfl fun j hj => ?_
      have : n + 1 - 1 - (j + 1) = n - 1 - j := by omega
      rw [this, pow_succ', mul_apply_eq_comp]
    rw [hsum, map_sub, pow_succ', mul_apply_eq_comp]
    simp only [Nat.add_sub_cancel, Nat.sub_zero]
    abel

/-- Geometric bound `∑_{j<n} μʲ q^{n-1-j} ≤ qⁿ / (q - μ)` for `0 ≤ μ < q`. -/
private theorem geom_sum_le {μ q : ℝ} (hμ : 0 ≤ μ) (hq : μ < q) (n : ℕ) :
    ∑ j ∈ range n, μ ^ j * q ^ (n - 1 - j) ≤ q ^ n / (q - μ) := by
  have h := geom_sum₂_mul μ q n
  rw [le_div_iff₀ (sub_pos.2 hq)]
  have : (∑ j ∈ range n, μ ^ j * q ^ (n - 1 - j)) * (q - μ) = q ^ n - μ ^ n := by
    linear_combination -h
  rw [this]
  linarith [pow_nonneg hμ n]

/-- Choice of the escape radius: for `K ≥ 0`, `r > 0`, `p > 1`, `ρ > 0` there is `η > 0` with
`η ≤ 2ρ/3` and `K (r η)^{p-1} ≤ 1/2`. -/
private theorem exists_escape_radius {K r ρ p : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (hρ : 0 < ρ)
    (hp : 1 < p) : ∃ η, 0 < η ∧ η ≤ 2 * ρ / 3 ∧ K * (r * η) ^ (p - 1) ≤ 1 / 2 := by
  set b : ℝ := (2 * K + 1)⁻¹ with hb
  have hb0 : 0 < b := inv_pos.2 (by linarith)
  have hp1 : 0 < p - 1 := by linarith
  refine ⟨min (2 * ρ / 3) (b ^ (1 / (p - 1)) / r), lt_min (by positivity) (by positivity),
    min_le_left _ _, ?_⟩
  have h1 : r * min (2 * ρ / 3) (b ^ (1 / (p - 1)) / r) ≤ b ^ (1 / (p - 1)) := by
    rw [← le_div_iff₀' hr]; exact min_le_right _ _
  have h2 : (r * min (2 * ρ / 3) (b ^ (1 / (p - 1)) / r)) ^ (p - 1) ≤ b := by
    calc _ ≤ (b ^ (1 / (p - 1))) ^ (p - 1) :=
          Real.rpow_le_rpow (by positivity) h1 hp1.le
      _ = b := by rw [← Real.rpow_mul hb0.le, one_div_mul_cancel hp1.ne', Real.rpow_one]
  calc K * _ ≤ K * b := mul_le_mul_of_nonneg_left h2 hK
    _ ≤ 1 / 2 := by
      rw [hb, ← div_eq_mul_inv, div_le_iff₀ (by linarith)]; linarith

/-- **Linearized instability of a fixed point of a map** (dominant-eigenvalue form).

Let `G : X → X` satisfy `G (x₀ + y) = x₀ + L y + O(‖y‖ᵖ)` on the ball `‖y‖ ≤ ρ`, with `p > 1`
and `L` a bounded linear operator. Suppose `L` has an eigenvalue `ν` with `|ν| > 1` and the
powers of `L` grow at most like `M μⁿ` with `μ < |ν|ᵖ`. Then `x₀` is not Lyapunov stable for the
iterates of `G`: there is `ε > 0` such that every neighbourhood of `x₀` contains a point whose
orbit reaches distance `ε` from `x₀`, and the orbit stays in the ball of radius `ρ` before
that, so only the values of `G` on that ball are used. -/
theorem exists_escape_of_eigenvalue {G : X → X} {x₀ : X} {L : X →L[𝕜] X}
    {ρ C p M μ : ℝ} {ν : 𝕜} {v : X}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hG : ∀ y, ‖y‖ ≤ ρ → ‖G (x₀ + y) - x₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hv : v ≠ 0) (hLv : L v = ν • v) (hν : 1 < ‖ν‖)
    (hμ0 : 0 ≤ μ) (hμ : μ < ‖ν‖ ^ p) (hM : ∀ n : ℕ, ‖L ^ n‖ ≤ M * μ ^ n) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - x₀‖ < δ ∧
      ∃ n, (∀ k < n, ‖G^[k] x - x₀‖ ≤ ρ) ∧ ε ≤ ‖G^[n] x - x₀‖ := by
  set r := ‖ν‖ with hr
  set q := r ^ p with hq
  have hr0 : 0 < r := by linarith
  have hM0 : 0 ≤ M := by
    have := hM 0
    rw [pow_zero, pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  set K := M * C * (3 / 2 : ℝ) ^ p / (q - μ) with hK
  have hK0 : 0 ≤ K := div_nonneg (by positivity) (by linarith)
  obtain ⟨η, hη0, hηρ, hηK⟩ := exists_escape_radius hK0 hr0 hρ hp
  refine ⟨η / 2, by positivity, fun δ hδ => ?_⟩
  -- unit eigenvector and initial point
  have hv0 : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w : X := ((‖v‖⁻¹ : ℝ) : 𝕜) • v with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hv0), inv_mul_cancel₀ hv0.ne']
  have hLw : L w = ν • w := by rw [hw, map_smul, hLv, smul_comm]
  set t : ℝ := min δ η / 2 with ht
  have ht0 : 0 < t := by positivity
  have htδ : t < δ := by have := min_le_left δ η; rw [ht]; linarith
  set x : X := x₀ + (t : 𝕜) • w with hx
  set y : ℕ → X := fun k => G^[k] x - x₀ with hy
  have hy0 : y 0 = (t : 𝕜) • w := by simp [hy, hx]
  have hnorm0 : ‖y 0‖ = t := by
    rw [hy0, norm_smul, hw1, mul_one, RCLike.norm_ofReal, abs_of_pos ht0]
  have hysucc : ∀ k, y (k + 1) = G (x₀ + y k) - x₀ := by
    intro k; simp only [hy, Function.iterate_succ_apply', add_sub_cancel]
  have hLpow : ∀ k, ‖(L ^ k) (y 0)‖ = t * r ^ k := by
    intro k
    have : (L ^ k) w = ν ^ k • w := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hLw, smul_smul]; ring_nf
    rw [hy0, map_smul, this, smul_smul, norm_smul, hw1, mul_one, norm_mul, norm_pow,
      RCLike.norm_ofReal, abs_of_pos ht0, mul_comm]
  have hrem : ∀ k, ‖y k‖ ≤ ρ → ‖y (k + 1) - L (y k)‖ ≤ C * ‖y k‖ ^ p := by
    intro k hk; rw [hysucc]; exact hG _ hk
  have hpow : ∀ i : ℕ, (t * r ^ i) ^ p = t ^ p * q ^ i := by
    intro i
    rw [Real.mul_rpow ht0.le (by positivity), ← Real.rpow_natCast_mul hr0.le, mul_comm (i : ℝ) p,
      Real.rpow_mul_natCast hr0.le]
  have hclaim : ∀ n, (∀ k < n, t * r ^ k ≤ η) → ‖y n - (L ^ n) (y 0)‖ ≤ t * r ^ n / 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp only [pow_zero, one_apply_eq_self, sub_self, norm_zero]; positivity
    have hyi : ∀ i < n, ‖y i‖ ≤ 3 / 2 * (t * r ^ i) := by
      intro i hi
      have h := ih i hi (fun k hk => hn k (hk.trans hi))
      calc ‖y i‖ = ‖(y i - (L ^ i) (y 0)) + (L ^ i) (y 0)‖ := by rw [sub_add_cancel]
        _ ≤ ‖y i - (L ^ i) (y 0)‖ + ‖(L ^ i) (y 0)‖ := norm_add_le _ _
        _ ≤ t * r ^ i / 2 + t * r ^ i := by rw [hLpow]; linarith
        _ = 3 / 2 * (t * r ^ i) := by ring
    have hri : ∀ i < n, ‖y (i + 1) - L (y i)‖ ≤ C * ((3 / 2 : ℝ) ^ p * (t ^ p * q ^ i)) := by
      intro i hi
      have hyiρ : ‖y i‖ ≤ ρ := (hyi i hi).trans (by have := hn i hi; linarith)
      calc _ ≤ C * ‖y i‖ ^ p := hrem i hyiρ
        _ ≤ C * (3 / 2 * (t * r ^ i)) ^ p :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) (hyi i hi) (by linarith)) hC
        _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity), hpow]
    have han : t * r ^ n ≤ r * η := by
      have := hn (n - 1) (by omega)
      calc t * r ^ n = r * (t * r ^ (n - 1)) := by
            rw [← mul_assoc, mul_comm r t, mul_assoc, ← pow_succ', Nat.sub_add_cancel hnpos]
        _ ≤ r * η := mul_le_mul_of_nonneg_left this hr0.le
    rw [duhamel L y n]
    calc ‖∑ j ∈ range n, (L ^ j) (y (n - 1 - j + 1) - L (y (n - 1 - j)))‖
        ≤ ∑ j ∈ range n, ‖(L ^ j) (y (n - 1 - j + 1) - L (y (n - 1 - j)))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range n, M * μ ^ j * (C * ((3 / 2 : ℝ) ^ p * (t ^ p * q ^ (n - 1 - j)))) := by
          refine sum_le_sum fun j hj => ?_
          have hj' : n - 1 - j < n := by omega
          exact (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul (hM j) (hri _ hj') (norm_nonneg _) (by positivity))
      _ = M * C * (3 / 2 : ℝ) ^ p * t ^ p * ∑ j ∈ range n, μ ^ j * q ^ (n - 1 - j) := by
          rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      _ ≤ M * C * (3 / 2 : ℝ) ^ p * t ^ p * (q ^ n / (q - μ)) :=
          mul_le_mul_of_nonneg_left (geom_sum_le hμ0 hμ n) (by positivity)
      _ = K * (t * r ^ n) ^ (p - 1) * (t * r ^ n) := by
          rw [mul_assoc K, ← Real.rpow_add_one (by positivity), sub_add_cancel, hpow, hK]
          ring
      _ ≤ 1 / 2 * (t * r ^ n) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) han (by linarith)) hK0).trans hηK
      _ = t * r ^ n / 2 := by ring
  have hex : ∃ N, η < t * r ^ N := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (η / t) hν
    exact ⟨N, by rwa [div_lt_iff₀' ht0] at hN⟩
  classical
  refine ⟨x, ?_, Nat.find hex, fun k hk => ?_, ?_⟩
  · rw [show x - x₀ = y 0 by simp [hy], hnorm0]; exact htδ
  · have hnmin : ∀ j < k, t * r ^ j ≤ η :=
      fun j hj => le_of_not_gt (Nat.find_min hex (hj.trans hk))
    have hk' : t * r ^ k ≤ η := le_of_not_gt (Nat.find_min hex hk)
    have h := hclaim k hnmin
    change ‖y k‖ ≤ ρ
    calc ‖y k‖ = ‖(y k - (L ^ k) (y 0)) + (L ^ k) (y 0)‖ := by rw [sub_add_cancel]
      _ ≤ ‖y k - (L ^ k) (y 0)‖ + ‖(L ^ k) (y 0)‖ := norm_add_le _ _
      _ ≤ ρ := by rw [hLpow]; linarith
  · have hnspec : η < t * r ^ Nat.find hex := Nat.find_spec hex
    have h := hclaim _ (fun k hk => le_of_not_gt (Nat.find_min hex hk))
    change η / 2 ≤ ‖y (Nat.find hex)‖
    have h2 := norm_sub_norm_le ((L ^ Nat.find hex) (y 0)) (y (Nat.find hex))
    rw [norm_sub_rev ((L ^ Nat.find hex) (y 0)), hLpow] at h2
    linarith

/-- **Linearized instability for a flow, through its time-`T` map.**

`Φ t x` is the state at time `t` of the solution starting at `x`; `u₀` is the equilibrium. The
flow is only required to step by its time-`T` map along orbits whose states at times
`0, T, …, nT` all lie in the ball `‖x - u₀‖ ≤ ρ`, so a local semiflow that exists for time `T`
from that ball qualifies. Near `u₀` the time-`T` map is
`u₀ + L y + O(‖y‖ᵖ)`; `L` has an eigenvalue `ν` with `|ν| > 1` and `‖Lⁿ‖ ≤ M μⁿ` with
`μ < |ν|ᵖ`. Then `u₀` is unstable: some `ε > 0` is reached at a nonnegative time from initial
data arbitrarily close to `u₀`. -/
theorem exists_escape_of_timeMap {Φ : ℝ → X → X} {u₀ : X} {T : ℝ} {L : X →L[𝕜] X}
    {ρ C p M μ : ℝ} {ν : 𝕜} {v : X}
    (hT : 0 ≤ T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) (x : X), (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hv : v ≠ 0) (hLv : L v = ν • v) (hν : 1 < ‖ν‖)
    (hμ0 : 0 ≤ μ) (hμ : μ < ‖ν‖ ^ p) (hM : ∀ n : ℕ, ‖L ^ n‖ ≤ M * μ ^ n) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - u₀‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖Φ t x - u₀‖ := by
  obtain ⟨ε, hε, h⟩ := exists_escape_of_eigenvalue hρ hC hp hrem hv hLv hν hμ0 hμ hM
  refine ⟨ε, hε, fun δ hδ => ?_⟩
  obtain ⟨x, hx, n, hball, hesc⟩ := h δ hδ
  have hiter : ∀ k ≤ n, Φ (k * T) x = (Φ T)^[k] x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hk
    rcases k with _ | k
    · simp [hΦ0]
    · have hb : ∀ j ≤ k, ‖Φ (j * T) x - u₀‖ ≤ ρ := fun j hj =>
        (ih j (by omega) (by omega)) ▸ hball j (by omega)
      rw [Nat.cast_succ, hstep k x hb, ih k (by omega) (by omega), Function.iterate_succ_apply']
  exact ⟨x, hx, n * T, by positivity, (hiter n le_rfl).symm ▸ hesc⟩

/-- Lyapunov form of `exists_escape_of_timeMap`: the equilibrium `u₀` of the flow `Φ` is not
Lyapunov stable in the norm of `X`. -/
theorem not_lyapunovStable_of_timeMap {Φ : ℝ → X → X} {u₀ : X} {T : ℝ} {L : X →L[𝕜] X}
    {ρ C p M μ : ℝ} {ν : 𝕜} {v : X}
    (hT : 0 ≤ T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) (x : X), (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hv : v ≠ 0) (hLv : L v = ν • v) (hν : 1 < ‖ν‖)
    (hμ0 : 0 ≤ μ) (hμ : μ < ‖ν‖ ^ p) (hM : ∀ n : ℕ, ‖L ^ n‖ ≤ M * μ ^ n) :
    ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, ‖x - u₀‖ < δ → ∀ t, 0 ≤ t → ‖Φ t x - u₀‖ < ε := by
  intro hstab
  obtain ⟨ε, hε, h⟩ :=
    exists_escape_of_timeMap hT hρ hC hp hΦ0 hstep hrem hv hLv hν hμ0 hμ hM
  obtain ⟨δ, hδ, hδε⟩ := hstab ε hε
  obtain ⟨x, hx, t, ht, hesc⟩ := h δ hδ
  exact (hδε x hx t ht).not_ge hesc

section Semigroup

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- **Linearized instability for a semilinear flow from its linearized semigroup.**

`S` is the linearized semigroup at the equilibrium `u₀` (for a semilinear parabolic problem,
`S t = e^{t B}` with `B` the linearization; Henry 1981, §5.1), with growth bound
`‖S t‖ ≤ M e^{ω t}`. The eigenvalue enters only through `hSφ : S T φ = e^{T κ} φ` at the
chosen time `T > 0`, with `Re κ > 0`. The theorem does not relate `κ` to a generator: `hSφ` is
the spectral-mapping input (an eigenvalue `κ` of the generator `B` with eigenvector `φ` gives
`e^{T B} φ = e^{T κ} φ`), to be supplied by the semigroup construction. The time-`T` map of
the flow is `u₀ + S T y + O(‖y‖ᵖ)` near `u₀`. If `ω < p · Re κ` (in particular, if `κ` is a dominant
eigenvalue and `S` has growth bound `Re κ`), then `u₀` is unstable. -/
theorem exists_escape_of_semigroup {Φ : ℝ → Y → Y} {S : ℝ → Y →L[ℂ] Y} {u₀ φ : Y}
    {T ρ C p M ω : ℝ} {κ : ℂ}
    (hT : 0 < T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) (x : Y), (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - S T y‖ ≤ C * ‖y‖ ^ p)
    (hS0 : S 0 = 1) (hSadd : ∀ s t, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t)
    (hSbound : ∀ t, 0 ≤ t → ‖S t‖ ≤ M * Real.exp (ω * t))
    (hφ : φ ≠ 0) (hSφ : S T φ = Complex.exp (T * κ) • φ)
    (hκ : 0 < κ.re) (hω : ω < p * κ.re) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - u₀‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖Φ t x - u₀‖ := by
  have hnorm : ‖Complex.exp (T * κ)‖ = Real.exp (T * κ.re) := by
    rw [Complex.norm_exp, Complex.re_ofReal_mul]
  have hpowS : ∀ n : ℕ, S T ^ n = S (n * T) := by
    intro n
    induction n with
    | zero => simp [hS0]
    | succ n ih =>
      rw [pow_succ, ih, ← hSadd _ _ (by positivity) hT.le, Nat.cast_succ, add_one_mul]
  refine exists_escape_of_timeMap (μ := Real.exp (ω * T)) (M := M) hT.le hρ hC hp hΦ0 hstep
    hrem hφ hSφ ?_ (Real.exp_pos _).le ?_ ?_
  · rw [hnorm]; exact Real.one_lt_exp_iff.2 (by positivity)
  · rw [hnorm, ← Real.exp_mul, Real.exp_lt_exp]; nlinarith
  · intro n
    rw [hpowS, ← Real.exp_nat_mul, show (n : ℝ) * (ω * T) = ω * (n * T) by ring]
    exact hSbound _ (by positivity)

end Semigroup

section SpectralRadius

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Gelfand's formula as a growth bound: if `r(L) < μ` then `‖Lⁿ‖ ≤ M μⁿ` for some `M`. -/
private theorem exists_norm_pow_le_of_spectralRadius_lt {L : Y →L[ℂ] Y} {μ : ℝ}
    (hμ : spectralRadius ℂ L < ENNReal.ofReal μ) : ∃ M, ∀ n : ℕ, ‖L ^ n‖ ≤ M * μ ^ n := by
  have hμ0 : 0 < μ := ENNReal.ofReal_pos.1 (lt_of_le_of_lt (by positivity) hμ)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius L).eventually
      (gt_mem_nhds hμ))
  set N' := max N 1
  refine ⟨1 + ∑ n ∈ range N', ‖L ^ n‖ / μ ^ n, fun n => ?_⟩
  have hsum0 : 0 ≤ ∑ n ∈ range N', ‖L ^ n‖ / μ ^ n :=
    sum_nonneg fun _ _ => by positivity
  by_cases hn : n < N'
  · have h1 : ‖L ^ n‖ / μ ^ n ≤ ∑ n ∈ range N', ‖L ^ n‖ / μ ^ n :=
      single_le_sum (f := fun n => ‖L ^ n‖ / μ ^ n) (fun _ _ => by positivity) (mem_range.2 hn)
    calc ‖L ^ n‖ = ‖L ^ n‖ / μ ^ n * μ ^ n := by field_simp
      _ ≤ (1 + ∑ n ∈ range N', ‖L ^ n‖ / μ ^ n) * μ ^ n :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · push Not at hn
    have hn1 : n ≠ 0 := by omega
    have h := hN n (le_trans (le_max_left _ _) hn)
    rw [← ENNReal.ofNNReal_toNNReal, ← ENNReal.coe_rpow_of_nonneg _ (by positivity),
      ENNReal.coe_lt_coe, one_div] at h
    have h2 : ‖L ^ n‖₊ < μ.toNNReal ^ n := by
      calc ‖L ^ n‖₊ = (‖L ^ n‖₊ ^ ((n : ℝ)⁻¹)) ^ n := (NNReal.rpow_inv_natCast_pow _ hn1).symm
        _ < μ.toNNReal ^ n := pow_lt_pow_left₀ h (by positivity) hn1
    have h3 : ‖L ^ n‖ ≤ μ ^ n := by
      have := NNReal.coe_lt_coe.2 h2
      rw [coe_nnnorm, NNReal.coe_pow, Real.coe_toNNReal _ hμ0.le] at this
      exact this.le
    calc ‖L ^ n‖ ≤ 1 * μ ^ n := by rwa [one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **Linearized instability, spectral-radius form.** On a complex Banach space, if the
linearization `L` has an eigenvalue `ν` with `|ν| > 1` and spectral radius `r(L) < |ν|ᵖ`,
the fixed point `x₀` of `G` is unstable. -/
theorem exists_escape_of_spectralRadius {G : Y → Y} {x₀ : Y} {L : Y →L[ℂ] Y}
    {ρ C p : ℝ} {ν : ℂ} {v : Y}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hG : ∀ y, ‖y‖ ≤ ρ → ‖G (x₀ + y) - x₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hv : v ≠ 0) (hLv : L v = ν • v) (hν : 1 < ‖ν‖)
    (hr : spectralRadius ℂ L < ENNReal.ofReal (‖ν‖ ^ p)) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - x₀‖ < δ ∧
      ∃ n, (∀ k < n, ‖G^[k] x - x₀‖ ≤ ρ) ∧ ε ≤ ‖G^[n] x - x₀‖ := by
  obtain ⟨μ, hμ0, hrμ, hμν⟩ := ENNReal.lt_iff_exists_real_btwn.1 hr
  obtain ⟨M, hM⟩ := exists_norm_pow_le_of_spectralRadius_lt hrμ
  have hμ : μ < ‖ν‖ ^ p := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hμν
  exact exists_escape_of_eigenvalue hρ hC hp hG hv hLv hν hμ0 hμ hM

/-- **Linearized instability, dominant-eigenvalue form.** If the eigenvalue `ν` of the
linearization `L` attains the spectral radius and `|ν| > 1`, the fixed point `x₀` of `G` is
unstable for any remainder order `p > 1`. -/
theorem exists_escape_of_spectralRadius_eq {G : Y → Y} {x₀ : Y} {L : Y →L[ℂ] Y}
    {ρ C p : ℝ} {ν : ℂ} {v : Y}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hG : ∀ y, ‖y‖ ≤ ρ → ‖G (x₀ + y) - x₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hv : v ≠ 0) (hLv : L v = ν • v) (hν : 1 < ‖ν‖)
    (hr : spectralRadius ℂ L = ‖ν‖₊) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - x₀‖ < δ ∧
      ∃ n, (∀ k < n, ‖G^[k] x - x₀‖ ≤ ρ) ∧ ε ≤ ‖G^[n] x - x₀‖ := by
  refine exists_escape_of_spectralRadius hρ hC hp hG hv hLv hν ?_
  rw [hr, ← enorm_eq_nnnorm, ← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  exact Real.self_lt_rpow_of_one_lt hν hp

end SpectralRadius

end MathlibExt.Analysis.PDE.SemilinearFlow.Instability
