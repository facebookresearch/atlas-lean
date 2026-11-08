/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# a-points of derivatives of functions in the Selberg class

Statements from M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui,
*On the a-Points of the kth Derivative of an L-Function in the Selberg Class*,
INTEGERS 24 (2024), Article A11.

`SelbergClassFunction` records the axioms of Section 2 of the paper together with the data
`Q_F`, `λ_j`, `μ_j`, `ω` of a functional equation. The derivative `F^(k)` is
`iteratedDeriv k F.toFun`; a-points are counted with multiplicity
(`analyticOrderNatAt` of `F^(k) - a`).

Lemmas 1, 3 and 4 fail as printed for `F = 1` and `a = 0` (then `F^(k)` vanishes
identically and every point is a `0`-point); they are stated under the hypothesis that
`a ≠ 0` or `F` has a nonzero Dirichlet coefficient `a(n)` with `n ≥ 2`, the setting of the
proofs (the paper's own proof of Lemma 1 treats `a ≠ 0` and cites Šimenas, who works with
nonconstant `F`, for `a = 0`).
-/

namespace MetaMathlibExt

open Filter Asymptotics

@[expose] public section

/-- A function in the Selberg class (Section 2 of the paper): a Dirichlet series
`F(s) = ∑ a(n) n^(-s)` (absolutely convergent for `Re s > 1`) satisfying the Ramanujan
hypothesis `a(n) = O(n^ε)`; an Euler product `F(s) = exp (∑ b(n) n^(-s))` for large `Re s`,
with `b` supported on prime powers and `b(n) = O(n^θ)` for some `θ < 1/2`; analytic
continuation (`(s - 1)^m F(s)` extends to an entire function of finite order); and the
functional equation `φ(s) = ω · conj (φ(1 - conj s))` for
`φ(s) = F(s) Q^s ∏ Γ(λ_j s + μ_j)` with `Q > 0`, `λ_j > 0`, `Re μ_j ≥ 0`, `|ω| = 1`, required
away from `s = 0, 1` and the poles of the Gamma factors on either side.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Section 2. -/
structure SelbergClassFunction where
  /-- The Dirichlet coefficients `a(n)`. -/
  coeff : ℕ → ℂ
  /-- The function `F` (its value at the possible pole `s = 1` is irrelevant). -/
  toFun : ℂ → ℂ
  coeff_one : coeff 1 = 1
  lseries : ∀ s : ℂ, 1 < s.re → LSeriesSummable coeff s ∧ LSeries coeff s = toFun s
  ramanujan : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ, ‖coeff n‖ ≤ C * (n : ℝ) ^ ε
  eulerProduct : ∃ b : ℕ → ℂ, (∀ n, b n ≠ 0 → IsPrimePow n) ∧
    (∃ θ : ℝ, θ < 1 / 2 ∧ ∃ C : ℝ, ∀ n : ℕ, ‖b n‖ ≤ C * (n : ℝ) ^ θ) ∧
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → LSeriesSummable b s ∧ toFun s = Complex.exp (LSeries b s)
  analyticContinuation : ∃ m : ℕ, ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
    (∃ ρ A : ℝ, ∀ s : ℂ, ‖g s‖ ≤ A * Real.exp (‖s‖ ^ ρ)) ∧
    ∀ s : ℂ, s ≠ 1 → g s = (s - 1) ^ m * toFun s
  /-- The number `r` of Gamma factors. -/
  r : ℕ
  /-- The conductor `Q_F`. -/
  Q : ℝ
  Q_pos : 0 < Q
  /-- The Gamma-factor scalings `λ_j`. -/
  lam : Fin r → ℝ
  lam_pos : ∀ j, 0 < lam j
  /-- The Gamma-factor shifts `μ_j`. -/
  mu : Fin r → ℂ
  mu_re_nonneg : ∀ j, 0 ≤ (mu j).re
  /-- The root number `ω`. -/
  omega : ℂ
  norm_omega : ‖omega‖ = 1
  functionalEquation : ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
    (∀ j (n : ℕ), (lam j : ℂ) * s + mu j ≠ -(n : ℂ) ∧
      (lam j : ℂ) * (1 - (starRingEnd ℂ) s) + mu j ≠ -(n : ℂ)) →
    toFun s * (Q : ℂ) ^ s * ∏ j, Complex.Gamma ((lam j : ℂ) * s + mu j) =
      omega * (starRingEnd ℂ) (toFun (1 - (starRingEnd ℂ) s) *
        (Q : ℂ) ^ (1 - (starRingEnd ℂ) s) *
        ∏ j, Complex.Gamma ((lam j : ℂ) * (1 - (starRingEnd ℂ) s) + mu j))

namespace SelbergClassFunction

/-- The degree `d_F = 2 ∑ λ_j`.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Section 2. -/
noncomputable def degree (F : SelbergClassFunction) : ℝ :=
  2 * ∑ j, F.lam j

/-- The degree is nonnegative.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Section 2. -/
theorem degree_nonneg (F : SelbergClassFunction) : 0 ≤ F.degree := by
  unfold degree
  have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ (F.lam_pos j).le
  linarith

/-- A function in the Selberg class is holomorphic away from `s = 1`.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Section 2. -/
theorem differentiableAt_toFun (F : SelbergClassFunction) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ F.toFun s := by
  obtain ⟨m, g, hg, -, hgeq⟩ := F.analyticContinuation
  have hne : (s - 1) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs)
  have hev : F.toFun =ᶠ[nhds s] fun w ↦ g w / (w - 1) ^ m := by
    filter_upwards [isOpen_ne.mem_nhds hs] with w hw
    rw [hgeq w hw, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.mpr hw))]
  exact ((hg s).div ((differentiableAt_id.sub_const 1).pow m) hne).congr_of_eventuallyEq hev

/-- The number `N_k(a; T, F)` of a-points of `F^(k)`, counted with multiplicity, in the
rectangle `E₂ < Re s < E₁`, `0 < Im s < T`.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Theorem 1 and Section 2. -/
noncomputable def aPointCount (F : SelbergClassFunction) (k : ℕ) (a : ℂ) (E₂ E₁ T : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | E₂ < ρ.re ∧ ρ.re < E₁ ∧ 0 < ρ.im ∧ ρ.im < T ∧
      iteratedDeriv k F.toFun ρ = a},
    analyticOrderNatAt (fun z ↦ iteratedDeriv k F.toFun z - a) ρ

/-- `N_k(a; T, F) = 0` for `T ≤ 0`.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Theorem 1. -/
theorem aPointCount_of_nonpos (F : SelbergClassFunction) (k : ℕ) (a : ℂ) (E₂ E₁ : ℝ) {T : ℝ}
    (hT : T ≤ 0) : F.aPointCount k a E₂ E₁ T = 0 := by
  have hempty : {ρ : ℂ | E₂ < ρ.re ∧ ρ.re < E₁ ∧ 0 < ρ.im ∧ ρ.im < T ∧
      iteratedDeriv k F.toFun ρ = a} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun ρ hρ ↦ ?_
    obtain ⟨-, -, h1, h2, -⟩ := hρ
    linarith
  rw [aPointCount, hempty, finsum_mem_empty]

end SelbergClassFunction

open SelbergClassFunction

/-- **Lemma 1.** For `F` in the Selberg class, `k ≥ 1` and `a ∈ ℂ` there is `E₁ ≥ 1` such that
`F^(k)` has no a-point in `Re s ≥ E₁`. Stated under `a ≠ 0` or `a(n) ≠ 0` for some `n ≥ 2`
(for `F = 1`, `a = 0` every point is a `0`-point).

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 1 (`integers-2024-A11-lem-1`). -/
public theorem_wanted SelbergClassFunction.exists_no_aPoint_right (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (hF : a ≠ 0 ∨ ∃ n, 2 ≤ n ∧ F.coeff n ≠ 0) :
    ∃ E₁ : ℝ, 1 ≤ E₁ ∧ ∀ s : ℂ, E₁ ≤ s.re → iteratedDeriv k F.toFun s ≠ a

/-- **Lemma 2.** For `k ≥ 1` and `c > 1` there is `τ_k` such that in `Re s > c`, `|Im s| ≥ τ_k`,
`(conj F(1 - conj s))^(k) = (d_F^k / (π^r ω)) Q^(2s-1) ∏ Γ(λ_j s + μ_j) Γ(λ_j s + 1 - λ_j - conj μ_j)
× ∏ sin π(-λ_j s + λ_j + conj μ_j) · log^k s · F(s) · (1 + O(1 / |log s|))`, the error read as
`|LHS - M(s)| ≤ C |M(s)| / |log s|` for the main term `M(s)`.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 2 (`integers-2024-A11-lem-2`). -/
public theorem_wanted SelbergClassFunction.iteratedDeriv_reflected_asymptotic
    (F : SelbergClassFunction) (k : ℕ) (hk : 1 ≤ k) (c : ℝ) (hc : 1 < c) :
    let M : ℂ → ℂ := fun s ↦
      (F.degree : ℂ) ^ k / ((Real.pi : ℂ) ^ F.r * F.omega) * (F.Q : ℂ) ^ (2 * s - 1) *
        (∏ j, Complex.Gamma ((F.lam j : ℂ) * s + F.mu j) *
          Complex.Gamma ((F.lam j : ℂ) * s + 1 - F.lam j - (starRingEnd ℂ) (F.mu j))) *
        (∏ j, Complex.sin (Real.pi * (-(F.lam j : ℂ) * s + F.lam j + (starRingEnd ℂ) (F.mu j)))) *
        Complex.log s ^ k * F.toFun s
    ∃ τ C : ℝ, ∀ s : ℂ, c < s.re → τ ≤ |s.im| →
      ‖iteratedDeriv k (fun w ↦ (starRingEnd ℂ) (F.toFun (1 - (starRingEnd ℂ) w))) s - M s‖ ≤
        C * ‖M s‖ / ‖Complex.log s‖

/-- **Lemma 3.** For `k ≥ 1` and `a ∈ ℂ` there are `E₂ ≤ 0` and `τ_k` such that `F^(k)` has no
a-point in `Re s ≤ E₂`, `|Im s| ≥ τ_k`. Stated under `a ≠ 0` or `a(n) ≠ 0` for some `n ≥ 2`.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 3 (`integers-2024-A11-lem-3`). -/
public theorem_wanted SelbergClassFunction.exists_no_aPoint_left (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (hF : a ≠ 0 ∨ ∃ n, 2 ≤ n ∧ F.coeff n ≠ 0) :
    ∃ E₂ : ℝ, E₂ ≤ 0 ∧ ∃ τ : ℝ, ∀ s : ℂ, s.re ≤ E₂ → τ ≤ |s.im| →
      iteratedDeriv k F.toFun s ≠ a

/-- **Lemma 4.** `N_k(a; T + 1, F) - N_k(a; T, F) = O(log T)` as `T → ∞`. Stated for every
strip `E₂ < Re s < E₁` (the paper uses the `E₁`, `E₂` of Lemmas 1 and 3) and under `a ≠ 0` or
`a(n) ≠ 0` for some `n ≥ 2`.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 4 (`integers-2024-A11-lem-4`). -/
public theorem_wanted SelbergClassFunction.aPointCount_unit_window (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (hF : a ≠ 0 ∨ ∃ n, 2 ≤ n ∧ F.coeff n ≠ 0) (E₂ E₁ : ℝ) :
    (fun T : ℝ ↦ (F.aPointCount k a E₂ E₁ (T + 1) : ℝ) - F.aPointCount k a E₂ E₁ T)
      =O[atTop] Real.log

/-- **Lemma 5.** For `σ₁ < Re s < σ₂` and large `t = Im s` (with `s` not an a-point),
`F^(k+1)(s) / (F^(k)(s) - a) = ∑_{|γ - t| ≤ 1} 1 / (s - ρ) + O(log t)`, the sum over the
a-points `ρ = β + iγ` of `F^(k)` with multiplicity.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 5 (`integers-2024-A11-lem-5`). -/
public theorem_wanted SelbergClassFunction.logDeriv_aPoint_partialFraction
    (F : SelbergClassFunction) (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (σ₁ σ₂ : ℝ) :
    ∃ t₀ C : ℝ, ∀ s : ℂ, σ₁ < s.re → s.re < σ₂ → t₀ ≤ s.im → iteratedDeriv k F.toFun s ≠ a →
      ‖iteratedDeriv (k + 1) F.toFun s / (iteratedDeriv k F.toFun s - a) -
          ∑ᶠ ρ ∈ {ρ : ℂ | |ρ.im - s.im| ≤ 1 ∧ iteratedDeriv k F.toFun ρ = a},
            (analyticOrderNatAt (fun z ↦ iteratedDeriv k F.toFun z - a) ρ : ℂ) / (s - ρ)‖ ≤
        C * Real.log s.im

/-- **Lemma 6, case `a ≠ 0`.** For `Re s` large,
`F^(k+1)(s) / (F^(k)(s) - a) = ∑_{l ≥ 0} ∑_{n₀, …, n_l} (-1)^(k(l+1)) / a^(l+1) · (log n₀)^(k+1)
(log n₁ ⋯ log n_l)^k a(n₀) ⋯ a(n_l) / (n₀ ⋯ n_l)^s`, as an absolutely convergent sum over
`l` and `(n₀, …, n_l)`. The paper's range `n_i ≥ ℓ` is written `n_i ≥ 1`: the added terms
vanish (`log 1 = 0`, and `a(n) = 0` for `2 ≤ n < ℓ`).

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 6 (`integers-2024-A11-lem-6`). -/
public theorem_wanted SelbergClassFunction.hasSum_logDeriv_aPoint_of_ne_zero
    (F : SelbergClassFunction) (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (ha : a ≠ 0) :
    ∃ E : ℝ, ∀ s : ℂ, E ≤ s.re →
      HasSum (fun p : (Σ l : ℕ, Fin (l + 1) → ℕ) ↦
          if ∀ i, 1 ≤ p.2 i then
            (-1) ^ (k * (p.1 + 1)) / a ^ (p.1 + 1) * (Real.log (p.2 0 : ℝ) : ℂ) ^ (k + 1) *
              (∏ i : Fin p.1, (Real.log (p.2 i.succ : ℝ) : ℂ) ^ k) *
              (∏ i, F.coeff (p.2 i)) / ∏ i, ((p.2 i : ℕ) : ℂ) ^ s
          else 0)
        (iteratedDeriv (k + 1) F.toFun s / (iteratedDeriv k F.toFun s - a))

/-- **Lemma 6, case `a = 0`.** Let `ℓ ≥ 2` be least with `a(ℓ) ≠ 0` (the least index of a
nonzero Dirichlet coefficient of `F^(k)`). For `Re s` large,
`F^(k+1)(s) / F^(k)(s) = ∑_{l ≥ 0} ∑_{n₀ ≥ ℓ, n₁, …, n_l ≥ ℓ + 1} (-1 / (a(ℓ) log^k ℓ))^(l+1)
(log n₀)^(k+1) (log n₁ ⋯ log n_l)^k ℓ^((l+1)s) a(n₀) ⋯ a(n_l) / (n₀ ⋯ n_l)^s`.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Lemma 6 (`integers-2024-A11-lem-6`). -/
public theorem_wanted SelbergClassFunction.hasSum_logDeriv_zero (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hℓF : F.coeff ℓ ≠ 0)
    (hmin : ∀ n, 2 ≤ n → n < ℓ → F.coeff n = 0) :
    ∃ E : ℝ, ∀ s : ℂ, E ≤ s.re →
      HasSum (fun p : (Σ l : ℕ, Fin (l + 1) → ℕ) ↦
          if ℓ ≤ p.2 0 ∧ ∀ i : Fin p.1, ℓ + 1 ≤ p.2 i.succ then
            (-1 / (F.coeff ℓ * (Real.log ℓ : ℂ) ^ k)) ^ (p.1 + 1) *
              (Real.log (p.2 0 : ℝ) : ℂ) ^ (k + 1) *
              (∏ i : Fin p.1, (Real.log (p.2 i.succ : ℝ) : ℂ) ^ k) *
              (ℓ : ℂ) ^ (((p.1 + 1 : ℕ) : ℂ) * s) *
              (∏ i, F.coeff (p.2 i)) / ∏ i, ((p.2 i : ℕ) : ℂ) ^ s
          else 0)
        (iteratedDeriv (k + 1) F.toFun s / iteratedDeriv k F.toFun s)

/-- **Theorem 1.** For `k ≥ 1` and `a ≠ 0`,
`N_k(a; T, F) = (d_F T / 2π) log T + (T / 2π) log (λ Q²) - d_F T / 2π + O(log T)` with
`λ = ∏ λ_j^(2λ_j)`, where `N_k` counts a-points in `E₂ < Re s < E₁`, `0 < Im s < T` for any
`E₁`, `E₂`, `τ` with the properties of Lemmas 1 and 3 (the bounds `E₁ ≥ 1`, `E₂ ≤ 0` of those
lemmas are not needed and are dropped).

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Theorem 1 (`integers-2024-A11-thm-1`). -/
public theorem_wanted SelbergClassFunction.aPointCount_asymptotic (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (ha : a ≠ 0) (E₂ E₁ τ : ℝ)
    (h₁ : ∀ s : ℂ, E₁ ≤ s.re → iteratedDeriv k F.toFun s ≠ a)
    (h₂ : ∀ s : ℂ, s.re ≤ E₂ → τ ≤ |s.im| → iteratedDeriv k F.toFun s ≠ a) :
    (fun T : ℝ ↦ (F.aPointCount k a E₂ E₁ T : ℝ) -
        (F.degree * T / (2 * Real.pi) * Real.log T +
          T / (2 * Real.pi) * Real.log ((∏ j, F.lam j ^ (2 * F.lam j)) * F.Q ^ 2) -
          F.degree * T / (2 * Real.pi)))
      =O[atTop] Real.log

/-- **Theorem 2, case `a ≠ 0`.** For `k ≥ 1` and `x > 1`, the sum of `x^ρ` over the a-points
`ρ = β + iγ` of `F^(k)` (with multiplicity) in `E₂ < β < E₁`, `0 < γ < T` is
`(T / 2π) ∑_{l ≥ 0} ∑_{n₀ ⋯ n_l = x} (-1)^(k(l+1)) / a^(l+1) · (log n₀)^(k+1)
(log n₁ ⋯ log n_l)^k a(n₀) ⋯ a(n_l) + O(log T)`, for `E₁`, `E₂`, `τ` as in Lemmas 1 and 3.
The range `n_i ≥ ℓ` is written `n_i ≥ 1` (the added terms vanish); the closing remark that
the sum is empty for `x ∉ ℤ` is immediate from the index condition and not stated separately.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Theorem 2 (`integers-2024-A11-thm-2`). -/
public theorem_wanted SelbergClassFunction.sum_aPoint_pow_of_ne_zero (F : SelbergClassFunction)
    (k : ℕ) (hk : 1 ≤ k) (a : ℂ) (ha : a ≠ 0) (x : ℝ) (hx : 1 < x) (E₂ E₁ τ : ℝ)
    (h₁ : ∀ s : ℂ, E₁ ≤ s.re → iteratedDeriv k F.toFun s ≠ a)
    (h₂ : ∀ s : ℂ, s.re ≤ E₂ → τ ≤ |s.im| → iteratedDeriv k F.toFun s ≠ a) :
    let c : ℂ := ∑' p : (Σ l : ℕ, Fin (l + 1) → ℕ),
      if (∀ i, 1 ≤ p.2 i) ∧ ((∏ i, p.2 i : ℕ) : ℝ) = x then
        (-1) ^ (k * (p.1 + 1)) / a ^ (p.1 + 1) * (Real.log (p.2 0 : ℝ) : ℂ) ^ (k + 1) *
          (∏ i : Fin p.1, (Real.log (p.2 i.succ : ℝ) : ℂ) ^ k) * ∏ i, F.coeff (p.2 i)
      else 0
    (fun T : ℝ ↦ (∑ᶠ ρ ∈ {ρ : ℂ | E₂ < ρ.re ∧ ρ.re < E₁ ∧ 0 < ρ.im ∧ ρ.im < T ∧
          iteratedDeriv k F.toFun ρ = a},
        (analyticOrderNatAt (fun z ↦ iteratedDeriv k F.toFun z - a) ρ : ℂ) * (x : ℂ) ^ ρ) -
        ((T / (2 * Real.pi) : ℝ) : ℂ) * c)
      =O[atTop] Real.log

/-- **Theorem 2, case `a = 0`.** With `ℓ ≥ 2` least such that `a(ℓ) ≠ 0`, for `k ≥ 1` and
`x > 1` the sum of `x^ρ` over the zeros `ρ` of `F^(k)` (with multiplicity) in `E₂ < β < E₁`,
`0 < γ < T` is `(T / 2π) ∑_{l ≥ 0} ∑ (-1 / (a(ℓ) log^k ℓ))^(l+1) (log n₀)^(k+1)
(log n₁ ⋯ log n_l)^k a(n₀) ⋯ a(n_l) + O(log T)`, the inner sum over `n₀ ≥ ℓ`,
`n₁, …, n_l ≥ ℓ + 1` with `x = n₀ ⋯ n_l / ℓ^(l+1)`, for `E₁`, `E₂`, `τ` as in Lemmas 1 and 3.
The closing remark that the sum is empty when `ℓ^n x ∉ ℤ` for all `n` is not stated
separately.

Source: M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points
of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11,
Theorem 2 (`integers-2024-A11-thm-2`). -/
public theorem_wanted SelbergClassFunction.sum_zero_pow (F : SelbergClassFunction) (k : ℕ)
    (hk : 1 ≤ k) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (hℓF : F.coeff ℓ ≠ 0)
    (hmin : ∀ n, 2 ≤ n → n < ℓ → F.coeff n = 0) (x : ℝ) (hx : 1 < x) (E₂ E₁ τ : ℝ)
    (h₁ : ∀ s : ℂ, E₁ ≤ s.re → iteratedDeriv k F.toFun s ≠ 0)
    (h₂ : ∀ s : ℂ, s.re ≤ E₂ → τ ≤ |s.im| → iteratedDeriv k F.toFun s ≠ 0) :
    let c : ℂ := ∑' p : (Σ l : ℕ, Fin (l + 1) → ℕ),
      if ℓ ≤ p.2 0 ∧ (∀ i : Fin p.1, ℓ + 1 ≤ p.2 i.succ) ∧
          ((∏ i, p.2 i : ℕ) : ℝ) = x * (ℓ : ℝ) ^ (p.1 + 1) then
        (-1 / (F.coeff ℓ * (Real.log ℓ : ℂ) ^ k)) ^ (p.1 + 1) *
          (Real.log (p.2 0 : ℝ) : ℂ) ^ (k + 1) *
          (∏ i : Fin p.1, (Real.log (p.2 i.succ : ℝ) : ℂ) ^ k) * ∏ i, F.coeff (p.2 i)
      else 0
    (fun T : ℝ ↦ (∑ᶠ ρ ∈ {ρ : ℂ | E₂ < ρ.re ∧ ρ.re < E₁ ∧ 0 < ρ.im ∧ ρ.im < T ∧
          iteratedDeriv k F.toFun ρ = 0},
        (analyticOrderNatAt (fun z ↦ iteratedDeriv k F.toFun z - 0) ρ : ℂ) * (x : ℂ) ^ ρ) -
        ((T / (2 * Real.pi) : ℝ) : ℂ) * c)
      =O[atTop] Real.log

end

end MetaMathlibExt
