/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite liquidation with quadratic costs

A path is a real inventory at each of `N + 1` instants, with no sign or monotonicity
restriction. Fix the initial inventory and require the last one to vanish. Completing a square
at the first free instant reduces minimisation to the same problem on the remaining intervals.
The one-interval cost starts this induction; every square eliminated has positive coefficient,
even when there is no inventory penalty.

## Reference

R. Almgren and N. Chriss, *Optimal execution of portfolio transactions*,
[Journal of Risk 3(2), 5–39 (2000), §2](https://www.smallake.kr/wp-content/uploads/2016/03/optliq.pdf).
In their linear-impact model, §2.2 treats trades of one sign so the absolute-value cost is constant.
Their (16) is the interior equation with
step `τ` and effective coefficient `η̃ = η − γτ/2`; (17) gives a particular hyperbolic formula.
Here `Δ` plays the role of `τ`, `η` that of the positive effective coefficient, and `κ` is
`λσ²`, not their decay rate. Their variance (5) samples the right endpoints: at fixed endpoints
the left-endpoint penalty below equals the corresponding right-endpoint penalty plus `ΔκX₀²`.
We minimise the stated quadratic alone, over all signed paths, including `κ = 0` and the forced
one-step path; no hyperbolic formula is required.
-/

@[expose] public section

namespace Domains.Economics.Finance.FiniteLiquidation

/-- For a real path `x₀, …, x_N`, the quadratic liquidation cost is the sum over `0 ≤ k < N`
of `Δ [η ((x_{k+1} − x_k)/Δ)² + κ x_k²]`. The inventory penalty uses the **left** endpoint.
The optimisation problem takes `N ≥ 1`, `Δ > 0`, `η > 0`, `κ ≥ 0`, `x₀ = X₀` and `x_N = 0`.
The sum itself imposes no endpoint constraints and is zero for `N = 0` or `Δ = 0` (real
division by zero is zero). -/
noncomputable def cost {N : ℕ} (Δ η κ : ℝ) (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ k : Fin N, Δ * (η * ((x k.succ - x k.castSucc) / Δ) ^ 2 + κ * x k.castSucc ^ 2)

-- Absorb the time scale into the two coefficients before eliminating interior values.
private noncomputable def energy {N : ℕ} (a b : ℝ) (x : Fin (N + 1) → ℝ) : ℝ :=
  ∑ k : Fin N, (a * (x k.succ - x k.castSucc) ^ 2 + b * x k.castSucc ^ 2)

private theorem cost_eq_energy {N : ℕ} {Δ : ℝ} (hΔ : 0 < Δ) (η κ : ℝ)
    (x : Fin (N + 1) → ℝ) : cost Δ η κ x = energy (η / Δ) (Δ * κ) x := by
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hΔ.ne']

private theorem energy_cons {n : ℕ} (a b y : ℝ) (q : Fin (n + 1) → ℝ) :
    energy a b (Fin.cons y q) = a * (q 0 - y) ^ 2 + b * y ^ 2 + energy a b q := by
  rw [energy, Fin.sum_univ_succ]
  rfl

-- `weight a b n` multiplies the squared initial inventory in the value of an (n+1)-step suffix.
private noncomputable def weight (a b : ℝ) : ℕ → ℝ
  | 0 => a + b
  | n + 1 => b + a * weight a b n / (a + weight a b n)

private theorem weight_pos {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) :
    0 < weight a b n := by
  induction n with
  | zero => exact add_pos_of_pos_of_nonneg ha hb
  | succ n ih => exact add_pos_of_nonneg_of_pos hb (div_pos (mul_pos ha ih) (add_pos ha ih))

private noncomputable def path (a b : ℝ) : (n : ℕ) → ℝ → Fin (n + 2) → ℝ
  | 0, y => Fin.cons y (fun _ => 0)
  | n + 1, y => Fin.cons y (path a b n (a * y / (a + weight a b n)))

private theorem path_zero (a b : ℝ) (n : ℕ) (y : ℝ) : path a b n y 0 = y := by
  cases n <;> simp [path]

private theorem path_last (a b : ℝ) (n : ℕ) (y : ℝ) : path a b n y (Fin.last (n + 1)) = 0 := by
  induction n generalizing y with
  | zero => simp [path]
  | succ n ih => simpa only [path, Fin.cons_last] using ih (a * y / (a + weight a b n))

-- The excess is the sum of two nonnegative terms: the excess on the tail and a square.
private theorem step_bound {a b c y z t : ℝ} (h : 0 < a + c) (ht : c * z ^ 2 ≤ t) :
    let v := (b + a * c / (a + c)) * y ^ 2
    let s := a * (z - y) ^ 2 + b * y ^ 2 + t
    v ≤ s ∧ (s = v ↔ z = a * y / (a + c) ∧ t = c * z ^ 2) := by
  dsimp only
  have gap : a * (z - y) ^ 2 + b * y ^ 2 + t - (b + a * c / (a + c)) * y ^ 2 =
      (a + c) * (z - a * y / (a + c)) ^ 2 + (t - c * z ^ 2) := by
    field_simp [h.ne']
    ring
  have hs := mul_nonneg h.le (sq_nonneg (z - a * y / (a + c)))
  refine ⟨by linarith, ?_, ?_⟩
  · intro he
    have hz : (a + c) * (z - a * y / (a + c)) ^ 2 = 0 := by linarith
    have hsq := (mul_eq_zero.mp hz).resolve_left h.ne'
    exact ⟨sub_eq_zero.mp (by simpa using hsq), by linarith⟩
  · rintro ⟨hz, ht'⟩
    simp only [← hz, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, ht'] at gap
    linarith

private theorem energy_bound {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ)
    (x : Fin (n + 2) → ℝ) (hx : x (Fin.last (n + 1)) = 0) :
    weight a b n * x 0 ^ 2 ≤ energy a b x ∧
      (energy a b x = weight a b n * x 0 ^ 2 ↔ x = path a b n (x 0)) := by
  induction n with
  | zero =>
    obtain ⟨y, q, rfl⟩ := Fin.exists_cons x
    simp only [Fin.cons_last] at hx
    have hq : q = fun _ => 0 := funext fun i => (congrArg q (Subsingleton.elim i _)).trans hx
    subst q
    simp [weight, energy, path, add_mul]
  | succ n ih =>
    obtain ⟨y, q, rfl⟩ := Fin.exists_cons x
    simp only [Fin.cons_last] at hx
    simp only [Fin.cons_zero, energy_cons]
    obtain ⟨hle, heq⟩ := ih q hx
    have hs := step_bound (b := b) (y := y) (add_pos ha (weight_pos ha hb n)) hle
    refine ⟨hs.1, hs.2.trans ?_⟩
    simp only [path, Fin.cons_inj, true_and]
    constructor
    · rintro ⟨hz, ht⟩
      exact hz ▸ heq.mp ht
    · intro hq
      have hz := (congrFun hq 0).trans (path_zero ..)
      exact ⟨hz, heq.mpr (hz.symm ▸ hq)⟩

-- The boundary flux of an optimal suffix gives the equation at the join of two intervals.
private theorem initial_flux {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) (y : ℝ) :
    (a + b) * y - a * path a b n y 1 = weight a b n * y := by
  cases n with
  | zero => simp [path, weight]
  | succ n =>
    simp only [path, Fin.cons_one, path_zero, weight]
    field_simp [(add_pos ha (weight_pos ha hb n)).ne']
    ring

private theorem balance {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) (y : ℝ)
    (i : ℕ) (hi : i + 2 ≤ n + 1) :
    let x := path a b n y
    a * (x ⟨i + 2, by omega⟩ - 2 * x ⟨i + 1, by omega⟩ + x ⟨i, by omega⟩) =
      b * x ⟨i + 1, by omega⟩ := by
  induction n generalizing y i with
  | zero => omega
  | succ n ih =>
    let z := a * y / (a + weight a b n)
    cases i with
    | zero =>
      change a * (path a b n z 1 - 2 * path a b n z 0 + y) = b * path a b n z 0
      rw [path_zero]
      have hz : z * (a + weight a b n) = a * y :=
        div_mul_cancel₀ _ (add_pos ha (weight_pos ha hb n)).ne'
      linarith only [initial_flux ha hb n z, hz]
    | succ i => exact ih z i (by omega)

/-- For `N ≥ 1` intervals of length `Δ > 0`, impact coefficient `η > 0`, inventory penalty
`κ = λσ² ≥ 0`, and any real initial inventory `X₀`, there is a unique global minimiser of
`Σ_{0 ≤ k < N} Δ [η ((x_{k+1} − x_k)/Δ)² + κ x_k²]` among all real paths with `x₀ = X₀`
and `x_N = 0`. An admissible path has the same cost as the minimiser exactly when the paths
agree at all `N + 1` instants. At every interior index `1 ≤ k < N` the minimiser satisfies
`η (x_{k+1} − 2x_k + x_{k−1})/Δ² = κ x_k`. For `N = 1` the path is `(X₀, 0)` and the
interior condition is empty. -/
theorem exists_unique_optimal_path {N : ℕ} (hN : 0 < N) {Δ η κ : ℝ}
    (hΔ : 0 < Δ) (hη : 0 < η) (hκ : 0 ≤ κ) (X₀ : ℝ) :
    ∃ p : Fin (N + 1) → ℝ, p 0 = X₀ ∧ p (Fin.last N) = 0 ∧
      (∀ x : Fin (N + 1) → ℝ, x 0 = X₀ → x (Fin.last N) = 0 →
        cost Δ η κ p ≤ cost Δ η κ x ∧ (cost Δ η κ x = cost Δ η κ p ↔ x = p)) ∧
      ∀ k : ℕ, ∀ hk : 0 < k, ∀ hkN : k < N,
        η * (p ⟨k + 1, by omega⟩ - 2 * p ⟨k, by omega⟩ + p ⟨k - 1, by omega⟩) / Δ ^ 2 =
          κ * p ⟨k, by omega⟩ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  let a := η / Δ
  let b := Δ * κ
  have ha : 0 < a := div_pos hη hΔ
  have hb : 0 ≤ b := mul_nonneg hΔ.le hκ
  let p := path a b n X₀
  have hp := path_zero a b n X₀
  have ht := path_last a b n X₀
  refine ⟨p, hp, ht, ?_, ?_⟩
  · intro x hx hxN
    have hmin := (energy_bound ha hb n p ht).2
    change p 0 = X₀ at hp
    rw [hp] at hmin
    have hvalue := hmin.mpr rfl
    have hbound := energy_bound ha hb n x hxN
    rw [hx] at hbound
    simpa only [cost_eq_energy hΔ, ← hvalue] using hbound
  · intro k hk hkN
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have he := balance ha hb n X₀ i (by omega)
    change a * (p _ - 2 * p _ + p _) = b * p _ at he
    apply (div_eq_iff (pow_ne_zero 2 hΔ.ne')).mpr
    dsimp only [a, b] at he
    field_simp [hΔ.ne'] at he
    exact he.trans (by ring)

end Domains.Economics.Finance.FiniteLiquidation
