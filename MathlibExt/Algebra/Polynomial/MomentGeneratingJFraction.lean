/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import MathlibExt.NumberTheory.HankelTransform
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace MetaMathlibExt

private noncomputable def Jcoeff (α β : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | n, (k + 1) =>
    α n * Jcoeff α β n k +
      β (n + 1) * ∑ i : Fin k, Jcoeff α β (n + 1) (i.val) * Jcoeff α β n (k - 1 - i.val)
  termination_by _n k => k

private lemma hJ0 (α β : ℕ → ℝ) (m : ℕ) : Jcoeff α β m 0 = 1 := by simp [Jcoeff]

private lemma hJsucc (α β : ℕ → ℝ) (m k : ℕ) : Jcoeff α β m (k + 1) =
    α m * Jcoeff α β m k +
      β (m + 1) * ∑ i : Fin k, Jcoeff α β (m + 1) (i.val) * Jcoeff α β m (k - 1 - i.val) := by
  simp [Jcoeff]

private lemma hSS (α β : ℕ → ℝ) (S : ℕ → PowerSeries ℝ)
    (hS : ∀ m, S m = PowerSeries.mk (Jcoeff α β m)) (n j : ℕ) :
    PowerSeries.coeff j (S n * S (n + 1)) =
      ∑ i : Fin (j + 1), Jcoeff α β (n + 1) ↑i * Jcoeff α β n (j - ↑i) := by
  have hFin : (∑ i : Fin (j + 1), Jcoeff α β (n + 1) ↑i * Jcoeff α β n (j - ↑i))
      = ∑ k ∈ Finset.range (j + 1), Jcoeff α β (n + 1) k * Jcoeff α β n (j - k) :=
    Fin.sum_univ_eq_sum_range
      (fun a => Jcoeff α β (n + 1) a * Jcoeff α β n (j - a)) (j + 1)
  have h0 := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => Jcoeff α β n a * Jcoeff α β (n + 1) b) j
  rw [Nat.succ_eq_add_one] at h0
  rw [hS n, hS (n + 1), PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  refine h0.trans ?_
  rw [hFin]
  conv_lhs =>
    rw [← Finset.sum_range_reflect
      (fun k => Jcoeff α β n k * Jcoeff α β (n + 1) (j - k)) (j + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have e1 : j + 1 - 1 - k = j - k := by omega
  have e2 : j - (j - k) = k := by omega
  simp only [e1, e2]
  exact mul_comm _ _

private lemma hSeq (α β : ℕ → ℝ) (S : ℕ → PowerSeries ℝ)
    (hS : ∀ m, S m = PowerSeries.mk (Jcoeff α β m)) (n : ℕ) :
    S n * (1 - PowerSeries.C (α n) * PowerSeries.X -
      PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 * S (n + 1)) = 1 := by
  have eA : S n * (PowerSeries.C (α n) * PowerSeries.X)
      = PowerSeries.C (α n) * (PowerSeries.X * S n) := by ring
  have eD : S n * (PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 * S (n + 1))
      = PowerSeries.C (β (n + 1)) * (PowerSeries.X ^ 2 * (S n * S (n + 1))) := by ring
  have eMain : S n * (1 - PowerSeries.C (α n) * PowerSeries.X -
        PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 * S (n + 1))
      = S n - PowerSeries.C (α n) * (PowerSeries.X * S n)
        - PowerSeries.C (β (n + 1)) * (PowerSeries.X ^ 2 * (S n * S (n + 1))) := by
    rw [sub_sub, mul_sub, mul_add, mul_one, eA, eD, sub_add_eq_sub_sub]
  have hcoeff : ∀ K, PowerSeries.coeff K (S n * (1 - PowerSeries.C (α n) * PowerSeries.X -
        PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 * S (n + 1)))
      = Jcoeff α β n K - α n * PowerSeries.coeff K (PowerSeries.X * S n)
        - β (n + 1) * PowerSeries.coeff K (PowerSeries.X ^ 2 * (S n * S (n + 1))) := by
    intro K
    rw [eMain, map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
    nth_rewrite 1 [hS n]
    rw [PowerSeries.coeff_mk]
  rw [PowerSeries.ext_iff]
  intro K
  rw [hcoeff K]
  cases K with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul]
    have hX20 : PowerSeries.coeff 0 (PowerSeries.X ^ 2 * (S n * S (n + 1))) = 0 := by
      have eX2 : PowerSeries.X ^ 2 * (S n * S (n + 1))
          = PowerSeries.X * (PowerSeries.X * (S n * S (n + 1))) := by ring
      rw [eX2, PowerSeries.coeff_zero_X_mul]
    rw [hX20, hJ0]
    simp
  | succ K =>
    cases K with
    | zero =>
      have hJn0 : PowerSeries.coeff 0 (S n) = Jcoeff α β n 0 := by
        rw [hS n, PowerSeries.coeff_mk]
      have hX10 : PowerSeries.coeff (0 + 1) (PowerSeries.X ^ 2 * (S n * S (n + 1))) = 0 := by
        have eX2 : PowerSeries.X ^ 2 * (S n * S (n + 1))
            = PowerSeries.X * (PowerSeries.X * (S n * S (n + 1))) := by ring
        rw [eX2, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul]
      rw [PowerSeries.coeff_succ_X_mul, hJn0, hX10, hJsucc α β n 0]
      simp [hJ0]
    | succ j =>
      have eX2 : PowerSeries.X ^ 2 * (S n * S (n + 1))
          = PowerSeries.X * (PowerSeries.X * (S n * S (n + 1))) := by ring
      have hJn1 : PowerSeries.coeff (j + 1) (S n) = Jcoeff α β n (j + 1) := by
        rw [hS n, PowerSeries.coeff_mk]
      rw [PowerSeries.coeff_succ_X_mul, hJn1, eX2,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
        hSS α β S hS n j, hJsucc α β n (j + 1)]
      have e : ∀ i : Fin (j + 1), (j + 1) - 1 - ↑i = j - ↑i := by
        intro i
        have := i.isLt
        omega
      simp only [e]
      have hne : ((j + 1) + 1 : ℕ) ≠ 0 := by omega
      simp only [PowerSeries.coeff_one, hne, ↓reduceIte]
      ring

private lemma hCsmul (L : Polynomial ℝ →ₗ[ℝ] ℝ) (a : ℝ) (q : Polynomial ℝ) :
    L (Polynomial.C a * q) = a * L q := by
  rw [← Polynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

private lemma hXp0 (p : ℕ → Polynomial ℝ) (α : ℕ → ℝ)
    (h0 : p 0 = 1) (h1 : p 1 = Polynomial.X - Polynomial.C (α 0)) :
    Polynomial.X * p 0 = p 1 + Polynomial.C (α 0) * p 0 := by
  rw [h1, h0]
  ring

private lemma hXpn (p : ℕ → Polynomial ℝ) (α β : ℕ → ℝ)
    (hrec : ∀ n : ℕ, 1 ≤ n → p (n + 1) = (Polynomial.X - Polynomial.C (α n)) * p n
      - Polynomial.C (β n) * p (n - 1))
    (n : ℕ) (hn : 1 ≤ n) :
    Polynomial.X * p n = p (n + 1) + Polynomial.C (α n) * p n
      + Polynomial.C (β n) * p (n - 1) := by
  rw [hrec n hn]
  ring

private lemma hXk0 (p : ℕ → Polynomial ℝ) (α : ℕ → ℝ)
    (hX : Polynomial.X * p 0 = p 1 + Polynomial.C (α 0) * p 0)
    (k : ℕ) :
    Polynomial.X ^ (k + 1) * p 0
      = Polynomial.X ^ k * p 1 + Polynomial.C (α 0) * (Polynomial.X ^ k * p 0) := by
  have e1 : Polynomial.X ^ (k + 1) * p 0
      = Polynomial.X ^ k * (Polynomial.X * p 0) := by ring
  rw [e1, hX]
  ring

private lemma hXkn (p : ℕ → Polynomial ℝ) (α β : ℕ → ℝ)
    (hX : ∀ n : ℕ, 1 ≤ n → Polynomial.X * p n = p (n + 1) + Polynomial.C (α n) * p n
      + Polynomial.C (β n) * p (n - 1))
    (n k : ℕ) (hn : 1 ≤ n) :
    Polynomial.X ^ (k + 1) * p n
      = Polynomial.X ^ k * p (n + 1) + Polynomial.C (α n) * (Polynomial.X ^ k * p n)
        + Polynomial.C (β n) * (Polynomial.X ^ k * p (n - 1)) := by
  have e1 : Polynomial.X ^ (k + 1) * p n
      = Polynomial.X ^ k * (Polynomial.X * p n) := by ring
  rw [e1, hX n hn]
  ring

private lemma hFeq (L : Polynomial ℝ →ₗ[ℝ] ℝ) (p : ℕ → Polynomial ℝ) (α β : ℕ → ℝ)
    (F : ℕ → PowerSeries ℝ)
    (hF : ∀ n k, PowerSeries.coeff k (F n) = L (Polynomial.X ^ k * p n))
    (hC : ∀ (a : ℝ) (q : Polynomial ℝ), L (Polynomial.C a * q) = a * L q)
    (hX0 : ∀ k, Polynomial.X ^ (k + 1) * p 0
      = Polynomial.X ^ k * p 1 + Polynomial.C (α 0) * (Polynomial.X ^ k * p 0))
    (hXn : ∀ n k, 1 ≤ n → Polynomial.X ^ (k + 1) * p n
      = Polynomial.X ^ k * p (n + 1) + Polynomial.C (α n) * (Polynomial.X ^ k * p n)
        + Polynomial.C (β n) * (Polynomial.X ^ k * p (n - 1))) :
    (F 0 - PowerSeries.C (L (p 0))
      = PowerSeries.X * (F 1 + PowerSeries.C (α 0) * F 0))
    ∧ (∀ n, 1 ≤ n → F n - PowerSeries.C (L (p n))
      = PowerSeries.X * (F (n + 1) + PowerSeries.C (α n) * F n
        + PowerSeries.C (β n) * F (n - 1))) := by
  refine ⟨?_, ?_⟩
  · rw [PowerSeries.ext_iff]
    intro K
    cases K with
    | zero =>
      rw [map_sub, hF 0 0, PowerSeries.coeff_C, PowerSeries.coeff_zero_X_mul]
      simp only [↓reduceIte]
      have hL0 : L (Polynomial.X ^ 0 * p 0) = L (p 0) := by rw [pow_zero, one_mul]
      rw [hL0, sub_self]
    | succ K =>
      rw [map_sub, hF 0 (K + 1), PowerSeries.coeff_C]
      have hne : K + 1 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      rw [sub_zero, PowerSeries.coeff_succ_X_mul, map_add, PowerSeries.coeff_C_mul,
        hX0 K, map_add, hC, hF 1 K, hF 0 K]
  · intro n hn
    rw [PowerSeries.ext_iff]
    intro K
    cases K with
    | zero =>
      rw [map_sub, hF n 0, PowerSeries.coeff_C, PowerSeries.coeff_zero_X_mul]
      simp only [↓reduceIte]
      have hLn : L (Polynomial.X ^ 0 * p n) = L (p n) := by rw [pow_zero, one_mul]
      rw [hLn, sub_self]
    | succ K =>
      rw [map_sub, hF n (K + 1), PowerSeries.coeff_C]
      have hne : K + 1 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      rw [sub_zero, PowerSeries.coeff_succ_X_mul, map_add, map_add,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
        hXn n K hn, map_add, map_add, hC, hC, hF (n + 1) K, hF n K, hF (n - 1) K]

private lemma coeff_step (H J : PowerSeries ℝ) (c : ℝ) (K : ℕ)
    (h : H - PowerSeries.C c = PowerSeries.X * J) :
    PowerSeries.coeff (K + 1) H = PowerSeries.coeff K J := by
  have h2 := congrArg (PowerSeries.coeff (K + 1)) h
  simp only [map_sub, PowerSeries.coeff_C, PowerSeries.coeff_succ_X_mul] at h2
  have hne : K + 1 ≠ 0 := by omega
  simp only [hne, ↓reduceIte, sub_zero] at h2
  exact h2

private lemma hPeq (α β : ℕ → ℝ) (S P : ℕ → PowerSeries ℝ)
    (hPsucc : ∀ n, P (n + 1) = P n * S (n + 1))
    (e : ∀ n, S n * (1 - PowerSeries.C (α n) * PowerSeries.X
      - PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 * S (n + 1)) = 1)
    (n : ℕ) (hn : 1 ≤ n) :
    P n - PowerSeries.C (α n) * PowerSeries.X * P n
      - PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 * (P n * S (n + 1)) = P (n - 1) := by
  have hPn : P n = P (n - 1) * S n := by
    have h := hPsucc (n - 1)
    rwa [Nat.sub_add_cancel hn] at h
  have key : P (n - 1) * (S n * (1 - PowerSeries.C (α n) * PowerSeries.X
      - PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 * S (n + 1))) = P (n - 1) := by
    rw [e n, mul_one]
  rw [hPn]
  linear_combination key

private lemma hGeq0 (α0 : ℝ) (b : ℝ) (S0 T : PowerSeries ℝ) (μ0 : ℝ)
    (G0 G1 : PowerSeries ℝ)
    (hG0 : G0 = PowerSeries.C μ0 * S0)
    (hG1 : G1 = PowerSeries.C μ0 * PowerSeries.C b * PowerSeries.X * (S0 * T))
    (e : S0 * (1 - PowerSeries.C α0 * PowerSeries.X
      - PowerSeries.C b * PowerSeries.X ^ 2 * T) = 1) :
    G0 - PowerSeries.C μ0
      = PowerSeries.X * (G1 + PowerSeries.C α0 * G0) := by
  rw [hG0, hG1]
  linear_combination PowerSeries.C μ0 * e

private lemma hGeq (α β : ℕ → ℝ) (S : ℕ → PowerSeries ℝ) (μ0 : ℝ)
    (W : ℕ → PowerSeries ℝ) (P G : ℕ → PowerSeries ℝ)
    (hWsucc : ∀ n, W (n + 1) = W n * PowerSeries.C (β (n + 1)))
    (hPsucc : ∀ n, P (n + 1) = P n * S (n + 1))
    (hG : ∀ n, G n = PowerSeries.C μ0 * W n * PowerSeries.X ^ n * P n)
    (hPeq : ∀ n, 1 ≤ n → P n - PowerSeries.C (α n) * PowerSeries.X * P n
      - PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 * (P n * S (n + 1)) = P (n - 1))
    (n : ℕ) (hn : 1 ≤ n) :
    G n = PowerSeries.X * G (n + 1) + PowerSeries.C (α n) * PowerSeries.X * G n
      + PowerSeries.C (β n) * PowerSeries.X * G (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hn ⊢
  have eP := hPeq (m + 1) (by omega)
  simp only [Nat.add_sub_cancel] at eP
  rw [hPsucc m] at eP
  rw [hG (m + 1), hG ((m + 1) + 1), hG m, hWsucc (m + 1), hWsucc m,
    hPsucc (m + 1), hPsucc m]
  linear_combination
    (PowerSeries.C μ0 * W m * PowerSeries.C (β (m + 1)) * PowerSeries.X ^ (m + 1)) * eP

/-! # Moment generating function as J-fraction for orthogonal polynomials (Favard)
-/

/-- **Moment generating function as a J-fraction, general form.** Let $p_0, p_1, \dots$ be real
polynomials, let $L$ be an $\mathbb{R}$-linear functional on $\mathbb{R}[x]$, and let
$(\alpha_n)$, $(\beta_n)$ and $(\mu_k)$ be real sequences such that $p_0 = 1$,
$p_1 = x - \alpha_0$, $p_{n+1} = (x - \alpha_n) p_n - \beta_n p_{n-1}$ for $n \ge 1$,
$\mu_k = L(x^k)$ for every $k$, and $L(p_n) = 0$ for $n \ge 1$. Then there are formal power
series $S_0, S_1, \dots$ over $\mathbb{R}$, each with constant term $1$, giving $\mu$ a Jacobi
fraction with coefficients $\alpha$ and $\beta$, numerator $\mu_0$ and tails $S_n$: that is,
$\sum_{k \ge 0} \mu_k x^k = \mu_0 S_0$ and $(1 - \alpha_n x - \beta_{n+1} x^2 S_{n+1}) S_n = 1$
for every $n \ge 0$.

No monicity, degree or $\beta_n \ne 0$ hypothesis is needed, and orthogonality enters only
through $L(p_n) = 0$ for $n \ge 1$. -/
theorem moment_generating_function_as_J_fraction_general
    (p : ℕ → Polynomial ℝ) (L : Polynomial ℝ →ₗ[ℝ] ℝ) (α β μ : ℕ → ℝ)
    (h0 : p 0 = 1) (h1 : p 1 = Polynomial.X - Polynomial.C (α 0))
    (hrec : ∀ n : ℕ, 1 ≤ n → p (n + 1) =
      (Polynomial.X - Polynomial.C (α n)) * p n - Polynomial.C (β n) * p (n - 1))
    (hμ : ∀ k : ℕ, μ k = L (Polynomial.X ^ k))
    (hLp : ∀ n : ℕ, 1 ≤ n → L (p n) = 0) :
    ∃ S : ℕ → PowerSeries ℝ,
      (∀ n : ℕ, PowerSeries.constantCoeff (S n) = 1) ∧ HasJacobiFraction μ α β (μ 0) S := by
  set S : ℕ → PowerSeries ℝ := fun n => PowerSeries.mk (Jcoeff α β n) with hSdef
  set F : ℕ → PowerSeries ℝ :=
    fun n => PowerSeries.mk (fun k => L (Polynomial.X ^ k * p n)) with hFdef
  set W : ℕ → PowerSeries ℝ :=
    fun n => ∏ i ∈ Finset.range n, PowerSeries.C (β (i + 1)) with hWdef
  set P : ℕ → PowerSeries ℝ := fun n => ∏ i ∈ Finset.range (n + 1), S i with hPdef
  set G : ℕ → PowerSeries ℝ :=
    fun n => PowerSeries.C (μ 0) * W n * PowerSeries.X ^ n * P n with hGdef
  have hS : ∀ m, S m = PowerSeries.mk (Jcoeff α β m) := fun m => by simp only [hSdef]
  have hF : ∀ n k, PowerSeries.coeff k (F n) = L (Polynomial.X ^ k * p n) := by
    intro n k
    simp only [hFdef, PowerSeries.coeff_mk]
  have hW : ∀ n, W n = ∏ i ∈ Finset.range n, PowerSeries.C (β (i + 1)) := by
    intro n
    simp only [hWdef]
  have hP : ∀ n, P n = ∏ i ∈ Finset.range (n + 1), S i := by
    intro n
    simp only [hPdef]
  have hG : ∀ n, G n = PowerSeries.C (μ 0) * W n * PowerSeries.X ^ n * P n := by
    intro n
    simp only [hGdef]
  have hWsucc : ∀ n, W (n + 1) = W n * PowerSeries.C (β (n + 1)) := by
    intro n
    rw [hW (n + 1), hW n, Finset.prod_range_succ]
  have hPsucc : ∀ n, P (n + 1) = P n * S (n + 1) := by
    intro n
    rw [hP (n + 1), hP n, Finset.prod_range_succ]
  have hW0 : W 0 = 1 := by
    rw [hW 0]
    simp
  have hP0 : P 0 = S 0 := by
    rw [hP 0]
    simp
  have hS0 : ∀ n, PowerSeries.constantCoeff (S n) = 1 := by
    intro n
    rw [hS n, PowerSeries.constantCoeff_mk, hJ0 α β n]
  have hPc1 : ∀ n, PowerSeries.constantCoeff (P n) = 1 := by
    intro n
    rw [hP n, map_prod]
    simp [hS0]
  have hCsmul' : ∀ (a : ℝ) (q : Polynomial ℝ), L (Polynomial.C a * q) = a * L q :=
    fun a q => hCsmul L a q
  have hXp0' : Polynomial.X * p 0 = p 1 + Polynomial.C (α 0) * p 0 := hXp0 p α h0 h1
  have hXpn' : ∀ n, 1 ≤ n → Polynomial.X * p n
      = p (n + 1) + Polynomial.C (α n) * p n + Polynomial.C (β n) * p (n - 1) :=
    fun n hn => hXpn p α β hrec n hn
  have hX0' : ∀ k, Polynomial.X ^ (k + 1) * p 0
      = Polynomial.X ^ k * p 1 + Polynomial.C (α 0) * (Polynomial.X ^ k * p 0) :=
    fun k => hXk0 p α hXp0' k
  have hXn' : ∀ n k, 1 ≤ n → Polynomial.X ^ (k + 1) * p n
      = Polynomial.X ^ k * p (n + 1) + Polynomial.C (α n) * (Polynomial.X ^ k * p n)
        + Polynomial.C (β n) * (Polynomial.X ^ k * p (n - 1)) :=
    fun n k hn => hXkn p α β hXpn' n k hn
  obtain ⟨hFeq0eq, hFeq2⟩ := hFeq L p α β F hF hCsmul' hX0' hXn'
  have hbridge : ∀ φ : PowerSeries ℝ,
      PowerSeries.coeff 0 φ = PowerSeries.constantCoeff φ :=
    fun φ => congrFun PowerSeries.coeff_zero_eq_constantCoeff φ
  have hFc0 : ∀ n, PowerSeries.constantCoeff (F n) = L (p n) := by
    intro n
    rw [← hbridge, hF n 0]
    have h0pow : Polynomial.X ^ 0 * p n = p n := by rw [pow_zero, one_mul]
    rw [h0pow]
  have hLp0 : L (p 0) = μ 0 := by rw [h0, hμ 0, pow_zero]
  have hW1 : W 1 = W 0 * PowerSeries.C (β 1) := by simpa using hWsucc 0
  have hP1 : P 1 = P 0 * S 1 := by simpa using hPsucc 0
  have hG0eq : G 0 = PowerSeries.C (μ 0) * S 0 := by
    rw [hG 0, hW0, hP0]
    ring
  have hG1 : G 1
      = PowerSeries.C (μ 0) * PowerSeries.C (β 1) * PowerSeries.X * (S 0 * S 1) := by
    rw [hG 1, hW1, hW0, hP1, hP0]
    ring
  have e0 : S 0 * (1 - PowerSeries.C (α 0) * PowerSeries.X
      - PowerSeries.C (β 1) * PowerSeries.X ^ 2 * S 1) = 1 := by
    simpa using hSeq α β S hS 0
  have hGeq0eq : G 0 - PowerSeries.C (μ 0)
      = PowerSeries.X * (G 1 + PowerSeries.C (α 0) * G 0) :=
    hGeq0 (α 0) (β 1) (S 0) (S 1) (μ 0) (G 0) (G 1) hG0eq hG1 e0
  have hPeq' : ∀ n, 1 ≤ n → P n - PowerSeries.C (α n) * PowerSeries.X * P n
      - PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 * (P n * S (n + 1)) = P (n - 1) :=
    fun n hn => hPeq α β S P hPsucc (fun m => hSeq α β S hS m) n hn
  have hGeq2 : ∀ n, 1 ≤ n → G n = PowerSeries.X * G (n + 1)
      + PowerSeries.C (α n) * PowerSeries.X * G n
      + PowerSeries.C (β n) * PowerSeries.X * G (n - 1) :=
    fun n hn => hGeq α β S (μ 0) W P G hWsucc hPsucc hG hPeq' n hn
  have hGconst : ∀ n, 1 ≤ n → PowerSeries.constantCoeff (G n) = 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hXc : PowerSeries.constantCoeff (PowerSeries.X ^ (m + 1) : PowerSeries ℝ) = (0 : ℝ) := by
      rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega : m + 1 ≠ 0)]
    rw [hG (m + 1), map_mul, map_mul, map_mul, PowerSeries.constantCoeff_C, hXc, mul_zero,
      zero_mul]
  have hGconst0 : PowerSeries.constantCoeff (G 0) = μ 0 := by
    rw [hG0eq, map_mul, PowerSeries.constantCoeff_C, hS0 0, mul_one]
  have ih : ∀ K n, PowerSeries.coeff K (F n) = PowerSeries.coeff K (G n) := by
    intro K
    induction K with
    | zero =>
      intro n
      rw [hbridge, hbridge]
      cases n with
      | zero => rw [hFc0 0, hLp0, hGconst0]
      | succ m => rw [hFc0 (m + 1), hLp (m + 1) (by omega), hGconst (m + 1) (by omega)]
    | succ K ihK =>
      intro n
      cases n with
      | zero =>
        have sF := coeff_step (F 0) (F 1 + PowerSeries.C (α 0) * F 0) (L (p 0)) K hFeq0eq
        have sG := coeff_step (G 0) (G 1 + PowerSeries.C (α 0) * G 0) (μ 0) K hGeq0eq
        rw [sF, sG, map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          ihK 1, ihK 0]
      | succ m =>
        have hFm := hFeq2 (m + 1) (by omega : 1 ≤ m + 1)
        have hGm0 : G (m + 1) - PowerSeries.C 0 = PowerSeries.X *
            (G ((m + 1) + 1) + PowerSeries.C (α (m + 1)) * G (m + 1)
              + PowerSeries.C (β (m + 1)) * G m) := by
          have hGm := hGeq2 (m + 1) (by omega : 1 ≤ m + 1)
          simp only [Nat.add_sub_cancel] at hGm
          rw [map_zero, sub_zero]
          linear_combination hGm
        simp only [Nat.add_sub_cancel] at hFm
        have sF := coeff_step (F (m + 1))
          (F ((m + 1) + 1) + PowerSeries.C (α (m + 1)) * F (m + 1)
            + PowerSeries.C (β (m + 1)) * F m) (L (p (m + 1))) K hFm
        have sG := coeff_step (G (m + 1))
          (G ((m + 1) + 1) + PowerSeries.C (α (m + 1)) * G (m + 1)
            + PowerSeries.C (β (m + 1)) * G m) 0 K hGm0
        rw [sF, sG, map_add, map_add, map_add, map_add, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
          ihK ((m + 1) + 1), ihK (m + 1), ihK m]
  have hF0eq : F 0 = PowerSeries.mk μ := by
    rw [PowerSeries.ext_iff]
    intro K
    rw [hF 0 K, PowerSeries.coeff_mk, h0, mul_one]
    exact (hμ K).symm
  have hFG0 : F 0 = G 0 := PowerSeries.ext_iff.mpr (fun K => ih K 0)
  have hGfinal : PowerSeries.mk μ = PowerSeries.C (μ 0) * S 0 := by
    rw [← hF0eq, hFG0, hG0eq]
  exact ⟨S, hS0, hGfinal, fun n => (mul_comm _ _).trans (hSeq α β S hS n)⟩

/--
**Moment generating function as a J-fraction.** Let $p_0, p_1, \dots$ be real polynomials, each
$p_n$ monic of degree $n$, let $L$ be an $\mathbb{R}$-linear functional on $\mathbb{R}[x]$, and
let $(\alpha_n)$, $(\beta_n)$ and $(\mu_k)$ be real sequences. Suppose that $p_0 = 1$,
$p_1 = x - \alpha_0$ and $p_{n+1} = (x - \alpha_n) p_n - \beta_n p_{n-1}$ for $n \ge 1$, that
$\beta_n \ne 0$ for $n \ge 1$, that the $p_n$ are orthogonal for $L$, meaning $L(p_m p_n) = 0$
for $m \ne n$ and $L(p_n^2) \ne 0$ for every $n$, that $\mu_k = L(x^k)$ for every $k$, and that
$\mu_0 \ne 0$. Let $g = \sum_{k \ge 0} \mu_k x^k$ be the moment generating function. Then there
are formal power series $S_0, S_1, \dots$ over $\mathbb{R}$, each with constant term $1$, such
that $g = \mu_0 S_0$ and $S_n (1 - \alpha_n x - \beta_{n+1} x^2 S_{n+1}) = 1$ for every
$n \ge 0$.

These equations present $g$ as the J-fraction
$\mu_0 / (1 - \alpha_0 x - \beta_1 x^2 / (1 - \alpha_1 x - \beta_2 x^2 / \cdots))$ with tails
$S_n$. The hypotheses that each $p_n$ is monic of degree $n$, that $\beta_n \ne 0$, that
$L(p_n^2) \ne 0$ and that $\mu_0 \ne 0$ are not needed, and orthogonality is used only through
$L(p_n) = 0$ for $n \ge 1$.

The source's recurrence line reads $\beta_n(x)$; it is read as $\beta_n p_{n-1}$, as in the
surrounding lines 315–317 and 364–366 of the source.

Proves `Wanted` entry `moment_generating_function_as_J_fraction`.

Source: Paul Barry and Aoife Hennessy, "Meixner-Type Results for Riordan
Arrays and Associated Integer Sequences," Journal of Integer Sequences 13
(2010), Article 10.9.4, J-fraction theorem citing C. Krattenthaler (cf.
Viennot Proposition 1, (7), p. V-5; Wall Theorem 51.1), lines 353–362,
https://cs.uwaterloo.ca/journals/JIS/VOL13/Barry5/barry96s.tex
-/
theorem moment_generating_function_as_J_fraction
    (p : ℕ → Polynomial ℝ)
    (L : Polynomial ℝ →ₗ[ℝ] ℝ)
    (α β : ℕ → ℝ)
    (μ : ℕ → ℝ)
    (g : PowerSeries ℝ) :
    (∀ n : ℕ, (p n).Monic ∧ (p n).natDegree = n) →
    (p 0 = 1) →
    (p 1 = Polynomial.X - Polynomial.C (α 0)) →
    (∀ n : ℕ, 1 ≤ n → p (n + 1) = (Polynomial.X - Polynomial.C (α n)) * p n - Polynomial.C (β n) * p
      (n - 1)) →
    (∀ n : ℕ, 1 ≤ n → β n ≠ 0) →
    (∀ m n : ℕ, m ≠ n → L (p m * p n) = 0) →
    (∀ n : ℕ, L (p n * p n) ≠ 0) →
    (∀ k : ℕ, μ k = L (Polynomial.X ^ k)) →
    (μ 0 ≠ 0) →
    (g = PowerSeries.mk μ) →
    ∃ S : ℕ → PowerSeries ℝ,
      (∀ n : ℕ, PowerSeries.constantCoeff (S n) = 1) ∧
      (g = PowerSeries.C (μ 0) * S 0) ∧
      ∀ n : ℕ, S n *
        (1 - PowerSeries.C (α n) * PowerSeries.X - PowerSeries.C (β (n + 1)) * PowerSeries.X ^ 2 * S
        (n + 1)) = 1 := by
  intro _ h0 h1 hrec _ horth _ hμ _ hg
  subst hg
  have hLp : ∀ n : ℕ, 1 ≤ n → L (p n) = 0 := fun n hn => by
    simpa [h0] using horth n 0 (by omega)
  obtain ⟨S, hS0, hhead, htail⟩ :=
    moment_generating_function_as_J_fraction_general p L α β μ h0 h1 hrec hμ hLp
  exact ⟨S, hS0, hhead, fun n => (mul_comm _ _).trans (htail n)⟩

end MetaMathlibExt
