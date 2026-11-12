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
public import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Linearized instability without an eigenvector

The general form of the instability half of the principle of linearized stability for maps
(Henry 1981, §5.1; Shatah and Strauss 2000): if `G (x₀ + y) = x₀ + L y + O(‖y‖ᵖ)` with `p > 1`
and `L` a bounded operator on a complex Banach space whose spectrum meets
`{z : 1 < ‖z‖}`, then the fixed point `x₀` of `G` is unstable. No eigenvector and no growth
condition on `L` is assumed. This is the general version deferred in
`MathlibExt.Analysis.PDE.SemilinearFlow.Instability`, which assumes an eigenvector `L v = ν v`
and a growth bound `‖Lⁿ‖ ≤ M μⁿ` with `μ < ‖ν‖ᵖ`.

The proof replaces the eigenvector by **approximate eigenvectors**: unit vectors `v` with
`‖L v - ν v‖` arbitrarily small. A spectral value `ν` of maximal modulus `‖ν‖ = r(L)` lies on
the frontier of the spectrum, and every frontier point of the spectrum of a bounded operator
on a Banach space is an approximate eigenvalue (`exists_approxEigenvector_of_mem_frontier`).
Gelfand's formula then gives `‖Lⁿ‖ ≤ M μⁿ` for any `μ > r(L)`, in particular for some
`μ < r(L)ᵖ` since `r(L) > 1`. For a fixed initial size `t`, the escape time `N` is fixed first
and the approximate eigenvector is then chosen precise enough that `Lⁿ v` stays within
`‖ν‖ⁿ / 4` of `νⁿ v` for all `n ≤ N`; the discrete Duhamel argument of the eigenvector case
then goes through on `[0, N]`.

As in `Instability`, the flow and the linearized semigroup are explicit hypotheses, and the
remainder estimate is assumed only on the ball `‖y‖ ≤ ρ`; the escaping orbit stays in that ball
until it escapes.

## Main results

* `exists_escape_of_approxEigenvalue`: over `ℝ` or `ℂ`, an approximate eigenvalue `ν` with
  `‖ν‖ > 1` and a growth bound `‖Lⁿ‖ ≤ M μⁿ`, `μ < ‖ν‖ᵖ`, give instability.
* `exists_approxEigenvector_of_mem_frontier`: a frontier point of the spectrum of a bounded
  operator on a Banach space is an approximate eigenvalue.
* `mem_frontier_spectrum_of_nnnorm_eq_spectralRadius`: a nonzero spectral value of maximal
  modulus is a frontier point of the spectrum.
* `exists_escape_of_mem_spectrum`, `exists_escape_of_one_lt_spectralRadius`: on a complex
  Banach space, spectrum outside the closed unit disk gives instability.
* `exists_escape_of_timeMap_mem_spectrum`, `not_lyapunovStable_of_timeMap_mem_spectrum`: the
  same for a flow, through its time-`T` map. For a linearized semigroup `S t = e^{t B}`, take
  `L = S T`: an unstable spectral value `κ` of the generator (`Re κ > 0`) gives the spectral
  value `e^{T κ}` of `S T` of modulus `> 1` once the spectral inclusion
  `e^{T σ(B)} ⊆ σ(e^{T B})` is supplied by the semigroup construction.

## Scope

The spectral forms are stated on complex Banach spaces. A real phase space whose
linearization has only non-real unstable spectrum needs complexification and is not covered
here; the approximate-eigenvalue form `exists_escape_of_approxEigenvalue` holds over `ℝ` when
a real approximate eigenvalue is available. The spectral-projection route (splitting off the
part of the spectrum of maximal modulus) is not needed and is not formalized.

## References

* D. Henry, *Geometric Theory of Semilinear Parabolic Equations*, Lecture Notes in Math. 840,
  Springer (1981), §5.1.
* J. Shatah and W. Strauss, *Spectral condition for instability*, Contemp. Math. 255 (2000),
  189–198.
-/

@[expose] public section

open Filter Finset

namespace MathlibExt.Analysis.PDE.SemilinearFlow.GeneralInstability

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- Discrete Duhamel formula: `yₙ - Lⁿ y₀ = ∑_{j<n} Lʲ (y_{n-1-j+1} - L y_{n-1-j})`.
(Private copy of the helper in `Instability`.) -/
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

/-- Geometric bound `∑_{j<n} μʲ q^{n-1-j} ≤ qⁿ / (q - μ)` for `0 ≤ μ < q`.
(Private copy of the helper in `Instability`.) -/
private theorem geom_sum_le {μ q : ℝ} (hμ : 0 ≤ μ) (hq : μ < q) (n : ℕ) :
    ∑ j ∈ range n, μ ^ j * q ^ (n - 1 - j) ≤ q ^ n / (q - μ) := by
  have h := geom_sum₂_mul μ q n
  rw [le_div_iff₀ (sub_pos.2 hq)]
  have : (∑ j ∈ range n, μ ^ j * q ^ (n - 1 - j)) * (q - μ) = q ^ n - μ ^ n := by
    linear_combination -h
  rw [this]
  linarith [pow_nonneg hμ n]

/-- Choice of the escape radius: for `K ≥ 0`, `r > 0`, `p > 1`, `ρ > 0` there is `η > 0` with
`η ≤ 2ρ/3` and `K (r η)^{p-1} ≤ 1/4`. (Adapted from the helper in `Instability`, with 1/4 in
place of 1/2.) -/
private theorem exists_escape_radius {K r ρ p : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (hρ : 0 < ρ)
    (hp : 1 < p) : ∃ η, 0 < η ∧ η ≤ 2 * ρ / 3 ∧ K * (r * η) ^ (p - 1) ≤ 1 / 4 := by
  set b : ℝ := (4 * K + 1)⁻¹ with hb
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
    _ ≤ 1 / 4 := by
      rw [hb, ← div_eq_mul_inv, div_le_iff₀ (by linarith)]; linarith

/-- Powers of `L` on an approximate eigenvector:
`‖Lⁿ v - νⁿ v‖ ≤ ‖L v - ν v‖ ‖ν‖ⁿ ∑_{j<n} ‖Lʲ‖` when `‖ν‖ ≥ 1`. -/
private theorem norm_pow_apply_sub_le {L : X →L[𝕜] X} {ν : 𝕜} (hν : 1 ≤ ‖ν‖) (v : X)
    (n : ℕ) :
    ‖(L ^ n) v - ν ^ n • v‖ ≤ ‖L v - ν • v‖ * (‖ν‖ ^ n * ∑ j ∈ range n, ‖L ^ j‖) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : (L ^ (n + 1)) v - ν ^ (n + 1) • v =
        (L ^ n) (L v - ν • v) + ν • ((L ^ n) v - ν ^ n • v) := by
      rw [pow_succ, mul_apply_eq_comp, map_sub, map_smul, smul_sub, smul_smul, ← pow_succ']
      abel
    have hA : ‖(L ^ n) (L v - ν • v)‖ ≤ ‖L v - ν • v‖ * (‖ν‖ ^ (n + 1) * ‖L ^ n‖) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [mul_comm ‖L ^ n‖]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ hν)
    have hB : ‖ν • ((L ^ n) v - ν ^ n • v)‖ ≤
        ‖L v - ν • v‖ * (‖ν‖ ^ (n + 1) * ∑ j ∈ range n, ‖L ^ j‖) := by
      rw [norm_smul]
      calc ‖ν‖ * ‖(L ^ n) v - ν ^ n • v‖
          ≤ ‖ν‖ * (‖L v - ν • v‖ * (‖ν‖ ^ n * ∑ j ∈ range n, ‖L ^ j‖)) :=
            mul_le_mul_of_nonneg_left ih (norm_nonneg _)
        _ = _ := by ring
    rw [hsplit, sum_range_succ]
    calc _ ≤ ‖(L ^ n) (L v - ν • v)‖ + ‖ν • ((L ^ n) v - ν ^ n • v)‖ := norm_add_le _ _
      _ ≤ _ := by linarith

/-- **Linearized instability at an approximate eigenvalue.**

Let `G : X → X` satisfy `G (x₀ + y) = x₀ + L y + O(‖y‖ᵖ)` on the ball `‖y‖ ≤ ρ`, with `p > 1`
and `L` a bounded linear operator. Suppose `ν` is an approximate eigenvalue of `L` (for every
`κ > 0` there is a unit vector `v` with `‖L v - ν v‖ ≤ κ`) with `‖ν‖ > 1`, and the powers of `L`
grow at most like `M μⁿ` with `μ < ‖ν‖ᵖ`. Then `x₀` is not Lyapunov stable for the iterates of
`G`: there is `ε > 0` such that every neighbourhood of `x₀` contains a point whose orbit reaches
distance `ε` from `x₀`, and the orbit stays in the ball of radius `ρ` before that. -/
theorem exists_escape_of_approxEigenvalue {G : X → X} {x₀ : X} {L : X →L[𝕜] X}
    {ρ C p M μ : ℝ} {ν : 𝕜}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hG : ∀ y, ‖y‖ ≤ ρ → ‖G (x₀ + y) - x₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (happrox : ∀ κ > 0, ∃ v : X, ‖v‖ = 1 ∧ ‖L v - ν • v‖ ≤ κ) (hν : 1 < ‖ν‖)
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
  set t : ℝ := min δ η / 2 with ht
  have ht0 : 0 < t := by positivity
  have htδ : t < δ := by have := min_le_left δ η; rw [ht]; linarith
  have hex : ∃ N, η < t * r ^ N := by
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (η / t) hν
    exact ⟨N, by rwa [div_lt_iff₀' ht0] at hN⟩
  classical
  set N := Nat.find hex with hN
  -- approximate eigenvector, precise enough on `[0, N]`
  set S : ℝ := ∑ j ∈ range (N + 1), ‖L ^ j‖ with hS
  have hS0 : 0 ≤ S := sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨w, hw1, hwL⟩ := happrox (1 / (4 * (S + 1))) (by positivity)
  have hwpow : ∀ n ≤ N, ‖(L ^ n) w - ν ^ n • w‖ ≤ r ^ n / 4 := by
    intro n hn
    have hsub : ∑ j ∈ range n, ‖L ^ j‖ ≤ S :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega))
        fun _ _ _ => norm_nonneg _
    calc _ ≤ ‖L w - ν • w‖ * (r ^ n * ∑ j ∈ range n, ‖L ^ j‖) :=
          norm_pow_apply_sub_le hν.le w n
      _ ≤ 1 / (4 * (S + 1)) * (r ^ n * S) :=
          mul_le_mul hwL (mul_le_mul_of_nonneg_left hsub (by positivity))
            (by positivity) (by positivity)
      _ ≤ r ^ n / 4 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [pow_pos hr0 n]
  set x : X := x₀ + (t : 𝕜) • w with hx
  set y : ℕ → X := fun k => G^[k] x - x₀ with hy
  have hy0 : y 0 = (t : 𝕜) • w := by simp [hy, hx]
  have hnorm0 : ‖y 0‖ = t := by
    rw [hy0, norm_smul, hw1, mul_one, RCLike.norm_ofReal, abs_of_pos ht0]
  have hysucc : ∀ k, y (k + 1) = G (x₀ + y k) - x₀ := by
    intro k; simp only [hy, Function.iterate_succ_apply', add_sub_cancel]
  have hLdev : ∀ n ≤ N, ‖(L ^ n) (y 0) - ν ^ n • y 0‖ ≤ t * r ^ n / 4 := by
    intro n hn
    rw [hy0, map_smul, smul_comm, ← smul_sub, norm_smul, RCLike.norm_ofReal, abs_of_pos ht0]
    calc t * _ ≤ t * (r ^ n / 4) := mul_le_mul_of_nonneg_left (hwpow n hn) ht0.le
      _ = _ := by ring
  have hνy : ∀ n, ‖ν ^ n • y 0‖ = t * r ^ n := by
    intro n; rw [norm_smul, hnorm0, norm_pow, mul_comm]
  have hLup : ∀ n ≤ N, ‖(L ^ n) (y 0)‖ ≤ 5 / 4 * (t * r ^ n) := by
    intro n hn
    have h := norm_le_norm_add_norm_sub' ((L ^ n) (y 0)) (ν ^ n • y 0)
    rw [hνy] at h; linarith [hLdev n hn]
  have hLlo : ∀ n ≤ N, 3 / 4 * (t * r ^ n) ≤ ‖(L ^ n) (y 0)‖ := by
    intro n hn
    have h := norm_le_norm_add_norm_sub' (ν ^ n • y 0) ((L ^ n) (y 0))
    rw [hνy, norm_sub_rev] at h; linarith [hLdev n hn]
  have hrem : ∀ k, ‖y k‖ ≤ ρ → ‖y (k + 1) - L (y k)‖ ≤ C * ‖y k‖ ^ p := by
    intro k hk; rw [hysucc]; exact hG _ hk
  have hpow : ∀ i : ℕ, (t * r ^ i) ^ p = t ^ p * q ^ i := by
    intro i
    rw [Real.mul_rpow ht0.le (by positivity), ← Real.rpow_natCast_mul hr0.le, mul_comm (i : ℝ) p,
      Real.rpow_mul_natCast hr0.le]
  have hclaim : ∀ n ≤ N, (∀ k < n, t * r ^ k ≤ η) →
      ‖y n - (L ^ n) (y 0)‖ ≤ t * r ^ n / 4 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro hnN hn
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · simp only [pow_zero, one_apply_eq_self, sub_self, norm_zero]; positivity
    have hyi : ∀ i < n, ‖y i‖ ≤ 3 / 2 * (t * r ^ i) := by
      intro i hi
      have h := ih i hi (by omega) (fun k hk => hn k (hk.trans hi))
      calc ‖y i‖ = ‖(y i - (L ^ i) (y 0)) + (L ^ i) (y 0)‖ := by rw [sub_add_cancel]
        _ ≤ ‖y i - (L ^ i) (y 0)‖ + ‖(L ^ i) (y 0)‖ := norm_add_le _ _
        _ ≤ t * r ^ i / 4 + 5 / 4 * (t * r ^ i) := add_le_add h (hLup i (by omega))
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
      _ ≤ 1 / 4 * (t * r ^ n) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by positivity) han (by linarith)) hK0).trans hηK
      _ = t * r ^ n / 4 := by ring
  refine ⟨x, ?_, N, fun k hk => ?_, ?_⟩
  · rw [show x - x₀ = y 0 by simp [hy], hnorm0]; exact htδ
  · have hnmin : ∀ j < k, t * r ^ j ≤ η :=
      fun j hj => le_of_not_gt (Nat.find_min hex (hj.trans hk))
    have hk' : t * r ^ k ≤ η := le_of_not_gt (Nat.find_min hex hk)
    have h := hclaim k hk.le hnmin
    have hup := hLup k hk.le
    change ‖y k‖ ≤ ρ
    calc ‖y k‖ = ‖(y k - (L ^ k) (y 0)) + (L ^ k) (y 0)‖ := by rw [sub_add_cancel]
      _ ≤ ‖y k - (L ^ k) (y 0)‖ + ‖(L ^ k) (y 0)‖ := norm_add_le _ _
      _ ≤ ρ := by linarith
  · have hnspec : η < t * r ^ N := Nat.find_spec hex
    have h := hclaim N le_rfl (fun k hk => le_of_not_gt (Nat.find_min hex hk))
    have hlo := hLlo N le_rfl
    change η / 2 ≤ ‖y N‖
    have h2 := norm_sub_norm_le ((L ^ N) (y 0)) (y N)
    rw [norm_sub_rev ((L ^ N) (y 0))] at h2
    linarith

section Spectrum

variable [CompleteSpace X]

/-- **Frontier points of the spectrum are approximate eigenvalues.** If `ν` lies on the
frontier of the spectrum of a bounded operator `L` on a Banach space, then for every `κ > 0`
there is a unit vector `v` with `‖L v - ν v‖ ≤ κ`.

Proof: a resolvent point `w` near `ν` has `‖(w - L)⁻¹‖ ≥ ‖w - ν‖⁻¹` (otherwise `ν - L` would be
a unit by `Units.ofNearby`), so `(w - L)⁻¹` has a large value `y`; the normalized `y` is the
approximate eigenvector. -/
theorem exists_approxEigenvector_of_mem_frontier {L : X →L[𝕜] X} {ν : 𝕜}
    (hν : ν ∈ frontier (spectrum 𝕜 L)) : ∀ κ > 0, ∃ v : X, ‖v‖ = 1 ∧ ‖L v - ν • v‖ ≤ κ := by
  intro κ hκ
  have hνσ : ν ∈ spectrum 𝕜 L := (spectrum.isClosed L).frontier_subset hν
  have : Nontrivial (X →L[𝕜] X) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hνσ
    exact hνσ
  obtain ⟨w, hwν, hwσ⟩ : ∃ w, dist w ν < κ / 2 ∧ w ∉ spectrum 𝕜 L := by
    by_contra! h
    exact hν.2 (mem_interior_iff_mem_nhds.2
      (Metric.mem_nhds_iff.2 ⟨κ / 2, by positivity, fun w hw => h w hw⟩))
  rw [dist_eq_norm] at hwν
  have hwν0 : 0 < ‖w - ν‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hwσ (h ▸ hνσ))
  obtain ⟨u, hu⟩ := spectrum.notMem_iff.1 hwσ
  have happ : ∀ (c : 𝕜) (z : X), algebraMap 𝕜 (X →L[𝕜] X) c z = c • z := fun c z => by
    simp [Algebra.algebraMap_eq_smul_one]
  have hR : ‖w - ν‖⁻¹ ≤ ‖(↑u⁻¹ : X →L[𝕜] X)‖ := by
    by_contra! hlt
    have hpos : 0 < ‖(↑u⁻¹ : X →L[𝕜] X)‖ := Units.norm_pos u⁻¹
    have hnear : ‖(algebraMap 𝕜 (X →L[𝕜] X) ν - L) - u‖ < ‖(↑u⁻¹ : X →L[𝕜] X)‖⁻¹ := by
      rw [hu, sub_sub_sub_cancel_right, ← map_sub, Algebra.algebraMap_eq_smul_one]
      calc ‖(ν - w) • (1 : X →L[𝕜] X)‖ ≤ ‖ν - w‖ * ‖(1 : X →L[𝕜] X)‖ :=
            (norm_smul (ν - w) (1 : X →L[𝕜] X)).le
        _ ≤ ‖ν - w‖ * 1 :=
            mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _ = ‖w - ν‖ := by rw [mul_one, norm_sub_rev]
        _ < _ := (lt_inv_comm₀ hpos hwν0).1 hlt
    exact spectrum.mem_iff.1 hνσ (u.ofNearby _ hnear).isUnit
  obtain ⟨z, hz1, hzR⟩ := (↑u⁻¹ : X →L[𝕜] X).exists_lt_apply_of_lt_opNorm
    ((show 2 / κ < ‖w - ν‖⁻¹ by
      rw [lt_inv_comm₀ (by positivity) hwν0]; field_simp; linarith).trans_le hR)
  set y : X := (↑u⁻¹ : X →L[𝕜] X) z with hy
  have hy0 : 0 < ‖y‖ := (by positivity : (0 : ℝ) < 2 / κ).trans hzR
  have huy : w • y - L y = z := by
    have h := congrArg (fun T : X →L[𝕜] X => T z) u.mul_inv
    simp only [mul_apply_eq_comp, one_apply_eq_self] at h
    rw [← h, hu, sub_apply, happ]
  set v : X := ((‖y‖⁻¹ : ℝ) : 𝕜) • y with hv
  have hv1 : ‖v‖ = 1 := by
    rw [hv, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.2 hy0), inv_mul_cancel₀ hy0.ne']
  have hwv : ‖w • v - L v‖ ≤ κ / 2 := by
    rw [hv, map_smul, smul_comm w, ← smul_sub, huy, norm_smul, RCLike.norm_ofReal,
      abs_of_pos (inv_pos.2 hy0), inv_mul_eq_div, div_le_iff₀ hy0]
    have : κ / 2 * (2 / κ) = 1 := by field_simp
    nlinarith
  refine ⟨v, hv1, ?_⟩
  have hsplit : L v - ν • v = (w - ν) • v - (w • v - L v) := by rw [sub_smul]; abel
  rw [hsplit]
  calc _ ≤ ‖(w - ν) • v‖ + ‖w • v - L v‖ := norm_sub_le _ _
    _ ≤ κ / 2 + κ / 2 := by
        rw [norm_smul, hv1, mul_one]; exact add_le_add hwν.le hwv
    _ = κ := by ring

/-- **A nonzero spectral value of maximal modulus is a frontier point of the spectrum.** If
`ν ∈ σ(L)`, `ν ≠ 0` and `‖ν‖ = r(L)`, then the points `(1 + s) ν`, `s > 0`, lie outside the
spectrum and tend to `ν`. -/
theorem mem_frontier_spectrum_of_nnnorm_eq_spectralRadius {L : X →L[𝕜] X} {ν : 𝕜}
    (hν : ν ∈ spectrum 𝕜 L) (hν0 : ν ≠ 0) (hr : spectralRadius 𝕜 L = ‖ν‖₊) :
    ν ∈ frontier (spectrum 𝕜 L) := by
  rw [frontier, (spectrum.isClosed L).closure_eq]
  refine ⟨hν, fun hint => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  have hn0 : 0 < ‖ν‖ := norm_pos_iff.2 hν0
  set s : ℝ := ε / (2 * ‖ν‖) with hs
  have hs0 : 0 < s := by positivity
  set w : 𝕜 := ((1 + s : ℝ) : 𝕜) * ν with hw
  have hwnorm : ‖w‖ = (1 + s) * ‖ν‖ := by
    rw [hw, norm_mul, RCLike.norm_ofReal, abs_of_pos (by linarith)]
  have hwball : w ∈ Metric.ball ν ε := by
    rw [Metric.mem_ball, dist_eq_norm,
      show w - ν = ((s : ℝ) : 𝕜) * ν by rw [hw]; push_cast; ring, norm_mul,
      RCLike.norm_ofReal, abs_of_pos hs0, hs, div_mul_eq_mul_div, mul_div_mul_right _ _ hn0.ne']
    linarith
  have hlt : spectralRadius 𝕜 L < ‖w‖₊ := by
    rw [hr, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm, coe_nnnorm, hwnorm]
    nlinarith
  exact spectrum.notMem_iff.2
    (spectrum.mem_resolventSet_iff.1 (spectrum.mem_resolventSet_of_spectralRadius_lt hlt))
    (hball hwball)

end Spectrum

section Complex

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Gelfand's formula as a growth bound: if `r(L) < μ` then `‖Lⁿ‖ ≤ M μⁿ` for some `M`.
(Private copy of the helper in `Instability`.) -/
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

/-- **Linearized instability, spectral form** (Henry 1981, §5.1). On a complex Banach
space, if `G (x₀ + y) = x₀ + L y + O(‖y‖ᵖ)` on the ball `‖y‖ ≤ ρ` with `p > 1` and the spectrum
of `L` contains a point `z` with `‖z‖ > 1`, then the fixed point `x₀` of `G` is unstable; the
escaping orbit stays in the ball of radius `ρ` until it escapes. No eigenvector and no growth
bound on `L` is assumed. -/
theorem exists_escape_of_mem_spectrum {G : Y → Y} {x₀ : Y} {L : Y →L[ℂ] Y}
    {ρ C p : ℝ} {z : ℂ}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hG : ∀ y, ‖y‖ ≤ ρ → ‖G (x₀ + y) - x₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hz : z ∈ spectrum ℂ L) (hz1 : 1 < ‖z‖) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - x₀‖ < δ ∧
      ∃ n, (∀ k < n, ‖G^[k] x - x₀‖ ≤ ρ) ∧ ε ≤ ‖G^[n] x - x₀‖ := by
  obtain ⟨ν, hνσ, hνr⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ⟨z, hz⟩
  have hzν : ‖z‖ ≤ ‖ν‖ := by
    have h : (‖z‖₊ : ENNReal) ≤ ‖ν‖₊ := by
      rw [hνr, spectralRadius_eq_of_unital]
      exact le_iSup₂ (f := fun k _ => (‖k‖₊ : ENNReal)) z hz
    exact_mod_cast h
  have hν : 1 < ‖ν‖ := hz1.trans_le hzν
  have hν0 : ν ≠ 0 := norm_pos_iff.1 (by linarith)
  have happrox := exists_approxEigenvector_of_mem_frontier
    (mem_frontier_spectrum_of_nnnorm_eq_spectralRadius hνσ hν0 hνr.symm)
  have hr : spectralRadius ℂ L < ENNReal.ofReal (‖ν‖ ^ p) := by
    rw [← hνr, ← enorm_eq_nnnorm, ← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    exact Real.self_lt_rpow_of_one_lt hν hp
  obtain ⟨μ, hμ0, hrμ, hμν⟩ := ENNReal.lt_iff_exists_real_btwn.1 hr
  obtain ⟨M, hM⟩ := exists_norm_pow_le_of_spectralRadius_lt hrμ
  have hμ : μ < ‖ν‖ ^ p := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hμν
  exact exists_escape_of_approxEigenvalue hρ hC hp hG happrox hν hμ0 hμ hM

/-- **Linearized instability, spectral-radius form.** On a complex Banach space, a fixed point
`x₀` of `G` whose linearization `L` has spectral radius `r(L) > 1` is unstable. -/
theorem exists_escape_of_one_lt_spectralRadius {G : Y → Y} {x₀ : Y} {L : Y →L[ℂ] Y}
    {ρ C p : ℝ}
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hG : ∀ y, ‖y‖ ≤ ρ → ‖G (x₀ + y) - x₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hr : 1 < spectralRadius ℂ L) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - x₀‖ < δ ∧
      ∃ n, (∀ k < n, ‖G^[k] x - x₀‖ ≤ ρ) ∧ ε ≤ ‖G^[n] x - x₀‖ := by
  have hne : (spectrum ℂ L).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [spectralRadius_eq_of_unital, h] at hr
    simp at hr
  obtain ⟨ν, hνσ, hνr⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty hne
  refine exists_escape_of_mem_spectrum hρ hC hp hG hνσ ?_
  rw [← hνr] at hr
  exact_mod_cast hr

omit [NormedSpace ℂ Y] [CompleteSpace Y] in
/-- Escape for the time-`T` map gives escape for the flow, when the flow steps by its time-`T`
map along orbits that stay in the ball of radius `ρ`. (Factored from the proof of
`Instability.exists_escape_of_timeMap`.) -/
private theorem flow_escape_of_map_escape {Φ : ℝ → Y → Y} {u₀ : Y} {T ρ : ℝ} (hT : 0 ≤ T)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) (x : Y), (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (h : ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - u₀‖ < δ ∧
      ∃ n, (∀ k < n, ‖(Φ T)^[k] x - u₀‖ ≤ ρ) ∧ ε ≤ ‖(Φ T)^[n] x - u₀‖) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - u₀‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖Φ t x - u₀‖ := by
  obtain ⟨ε, hε, h⟩ := h
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

/-- **Linearized instability for a flow, spectral form.**

`Φ t x` is the state at time `t` of the solution starting at `x`; `u₀` is the equilibrium. The
flow is only required to step by its time-`T` map along orbits whose states at times
`0, T, …, nT` all lie in the ball `‖x - u₀‖ ≤ ρ`. Near `u₀` the time-`T` map is
`u₀ + L y + O(‖y‖ᵖ)` with `p > 1`, and the spectrum of `L` contains a point `z` with
`‖z‖ > 1`. Then `u₀` is unstable. For a linearized semigroup, `L = S T = e^{T B}` and
`z = e^{T κ}` for an unstable spectral value `κ` of `B` (`Re κ > 0`), given the spectral
inclusion `e^{T σ(B)} ⊆ σ(e^{T B})`. -/
theorem exists_escape_of_timeMap_mem_spectrum {Φ : ℝ → Y → Y} {u₀ : Y} {T : ℝ}
    {L : Y →L[ℂ] Y} {ρ C p : ℝ} {z : ℂ}
    (hT : 0 ≤ T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) (x : Y), (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hz : z ∈ spectrum ℂ L) (hz1 : 1 < ‖z‖) :
    ∃ ε > 0, ∀ δ > 0, ∃ x, ‖x - u₀‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖Φ t x - u₀‖ :=
  flow_escape_of_map_escape hT hΦ0 hstep (exists_escape_of_mem_spectrum hρ hC hp hrem hz hz1)

/-- Lyapunov form of `exists_escape_of_timeMap_mem_spectrum`: the equilibrium `u₀` of the flow
`Φ` is not Lyapunov stable in the norm of `Y`. -/
theorem not_lyapunovStable_of_timeMap_mem_spectrum {Φ : ℝ → Y → Y} {u₀ : Y} {T : ℝ}
    {L : Y →L[ℂ] Y} {ρ C p : ℝ} {z : ℂ}
    (hT : 0 ≤ T) (hρ : 0 < ρ) (hC : 0 ≤ C) (hp : 1 < p)
    (hΦ0 : ∀ x, Φ 0 x = x)
    (hstep : ∀ (n : ℕ) (x : Y), (∀ k ≤ n, ‖Φ (k * T) x - u₀‖ ≤ ρ) →
      Φ ((n + 1) * T) x = Φ T (Φ (n * T) x))
    (hrem : ∀ y, ‖y‖ ≤ ρ → ‖Φ T (u₀ + y) - u₀ - L y‖ ≤ C * ‖y‖ ^ p)
    (hz : z ∈ spectrum ℂ L) (hz1 : 1 < ‖z‖) :
    ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, ‖x - u₀‖ < δ → ∀ t, 0 ≤ t → ‖Φ t x - u₀‖ < ε := by
  intro hstab
  obtain ⟨ε, hε, h⟩ :=
    exists_escape_of_timeMap_mem_spectrum hT hρ hC hp hΦ0 hstep hrem hz hz1
  obtain ⟨δ, hδ, hδε⟩ := hstab ε hε
  obtain ⟨x, hx, t, ht, hesc⟩ := h δ hδ
  exact (hδε x hx t ht).not_ge hesc

end Complex

end MathlibExt.Analysis.PDE.SemilinearFlow.GeneralInstability
