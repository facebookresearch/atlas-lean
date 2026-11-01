/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import MathlibExt.NumberTheory.ArithmeticFunction.CompletelyMultiplicative
public import MathlibExt.NumberTheory.ArithmeticFunction.SigmaR
public import MathlibExt.NumberTheory.LSeries.Operations
import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Ramanujan's formula for the Dirichlet series of `σ_a σ_b` and its character twists

Ramanujan's formula evaluates the Dirichlet series of a product of two divisor functions:
for complex `a, b` and `s` in the half-plane of absolute convergence,
`∑ σ_a(n) σ_b(n) n^{-s} = ζ(s) ζ(s - a) ζ(s - b) ζ(s - a - b) / ζ(2s - a - b)`.
More generally, with twisted divisor sums `σ_{a,χ}(n) = ∑_{d ∣ n} χ(d) d^a`,
`∑ σ_{a,χ₁}(n) σ_{b,χ₂}(n) n^{-s}
  = ζ(s) L(s - a, χ₁) L(s - b, χ₂) L(s - a - b, χ₁χ₂) / L(2s - a - b, χ₁χ₂)`.

Both follow from one identity of arithmetic functions. For completely multiplicative `F` and
`G`, with `ζ * F` and `ζ * G` their divisor sums,
`squareLift (F · G) * ((ζ * F) · (ζ * G)) = ζ * F * G * (F · G)`,
where `·` is the pointwise product and `*` is Dirichlet convolution. At a prime power this is a
finite geometric-sum identity; its generating-function form is the classical four-parameter
identity `hasSum_ramanujan_four_param`.

## Main statements

* `MetaMathlibExt.hasSum_ramanujan_four_param`: the four-parameter power series identity.
* `ArithmeticFunction.mul_apply_prime_pow`: Dirichlet convolution at a prime power.
* `ArithmeticFunction.squareLift_pmul_mul_pmul_zeta_mul`: the convolution identity.
* `ArithmeticFunction.LSeriesSummable_pmul_zeta_mul`: absolute convergence of the Dirichlet
  series of `(ζ * F) · (ζ * G)`.
* `ArithmeticFunction.LSeries_pmul_zeta_mul_mul_LSeries_pmul`: the L-series identity for general
  completely multiplicative `F` and `G`.
* `DirichletCharacter.LSeries_sigmaR_mul_sigmaR`: the twisted formula.
* `DirichletCharacter.LSeries_normSq_sigmaR`: the formula for `∑ |σ_{a,χ}(n)|² n^{-s}`.
* `ArithmeticFunction.LSeries_sigmaR_mul_sigmaR`: Ramanujan's formula.
* `ArithmeticFunction.LSeries_sigma_zero_sq`: `∑ d(n)² n^{-s} = ζ(s)⁴ / ζ(2s)`.
-/

@[expose] public section

/-! ### The four-parameter identity -/

namespace MetaMathlibExt

/-- **Ramanujan's four-parameter identity.** If `α ≠ β`, `γ ≠ δ` and the four products
`α γ T`, `α δ T`, `β γ T`, `β δ T` have norm less than one, then
`∑_{n ≥ 0} ((α^{n+1} - β^{n+1}) / (α - β)) ((γ^{n+1} - δ^{n+1}) / (γ - δ)) T^n
  = (1 - α β γ δ T²) / ((1 - α γ T) (1 - α δ T) (1 - β γ T) (1 - β δ T))`.

With `α = 1`, `β = p^a`, `γ = 1`, `δ = p^b` and `T = p^{-s}` this is the Euler factor at `p` of
Ramanujan's formula for `∑ σ_a(n) σ_b(n) n^{-s}`. -/
theorem hasSum_ramanujan_four_param {K : Type*} [NormedField K] {α β γ δ T : K} (hαβ : α ≠ β)
    (hγδ : γ ≠ δ) (hαγ : ‖α * γ * T‖ < 1) (hαδ : ‖α * δ * T‖ < 1) (hβγ : ‖β * γ * T‖ < 1)
    (hβδ : ‖β * δ * T‖ < 1) :
    HasSum (fun n : ℕ ↦
        ((α ^ (n + 1) - β ^ (n + 1)) / (α - β)) * ((γ ^ (n + 1) - δ ^ (n + 1)) / (γ - δ)) * T ^ n)
      ((1 - α * β * γ * δ * T ^ 2) /
        ((1 - α * γ * T) * (1 - α * δ * T) * (1 - β * γ * T) * (1 - β * δ * T))) := by
  have hab : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  have hcd : γ - δ ≠ 0 := sub_ne_zero.mpr hγδ
  have hne : ∀ x : K, ‖x‖ < 1 → 1 - x ≠ 0 := fun x hx h ↦ by
    rw [← sub_eq_zero.mp h, norm_one] at hx
    exact lt_irrefl 1 hx
  have e₁ := hne _ hαγ
  have e₂ := hne _ hαδ
  have e₃ := hne _ hβγ
  have e₄ := hne _ hβδ
  have H := (((((hasSum_geometric_of_norm_lt_one hαγ).mul_left (α * γ)).sub
    ((hasSum_geometric_of_norm_lt_one hαδ).mul_left (α * δ))).sub
    ((hasSum_geometric_of_norm_lt_one hβγ).mul_left (β * γ))).add
    ((hasSum_geometric_of_norm_lt_one hβδ).mul_left (β * δ))).div_const ((α - β) * (γ - δ))
  convert H using 1
  · funext n
    field_simp
    ring
  · field_simp
    ring

end MetaMathlibExt

open scoped LSeries.notation ArithmeticFunction.zeta ArithmeticFunction.sigma

namespace ArithmeticFunction

/-! ### Dirichlet convolution at prime powers -/

/-- Dirichlet convolution at a prime power:
`(f * g) (p ^ a) = ∑_{i ≤ a} f (p ^ i) * g (p ^ (a - i))`. -/
theorem mul_apply_prime_pow {R : Type*} [Semiring R] (f g : ArithmeticFunction R) {p : ℕ}
    (hp : p.Prime) (a : ℕ) :
    (f * g) (p ^ a) = ∑ i ∈ Finset.range (a + 1), f (p ^ i) * g (p ^ (a - i)) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun i j ↦ f i * g j),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rw [Nat.pow_div (by omega) hp.pos]

/-! ### The convolution identity -/

/-- A prime power `p ^ i` is a square exactly when `i` is even. -/
private theorem isSquare_prime_pow_iff {p : ℕ} (hp : p.Prime) (i : ℕ) :
    IsSquare (p ^ i) ↔ Even i := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ ⟨p ^ k, by rw [hk, pow_add]⟩⟩
  rw [isSquare_iff_exists_sq] at h
  obtain ⟨c, hc⟩ := h
  have hfac := congrArg (fun m ↦ Nat.factorization m p) hc
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_self,
    mul_one] at hfac
  exact ⟨c.factorization p, by omega⟩

/-- The finite geometric-sum identity behind `squareLift_pmul_mul_pmul_zeta_mul`, at the prime
power `p ^ n`, with local parameters `x = F p` and `y = G p`. -/
private theorem local_identity {R : Type*} [CommRing R] (x y : R) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (if Even i then (x * y) ^ (i / 2) else 0) *
        ((∑ j ∈ Finset.range (n - i + 1), x ^ j) * (∑ j ∈ Finset.range (n - i + 1), y ^ j)) =
      ∑ i ∈ Finset.range (n + 1), (∑ k ∈ Finset.range (i + 1),
        (∑ j ∈ Finset.range (k + 1), x ^ j) * y ^ (i - k)) * (x * y) ^ (n - i) := by
  set S : ℕ → R := fun m ↦ ∑ j ∈ Finset.range (m + 1), x ^ j with hS
  set T : ℕ → R := fun m ↦ ∑ j ∈ Finset.range (m + 1), y ^ j with hT
  set A : ℕ → R := fun m ↦ ∑ k ∈ Finset.range (m + 1), S k * y ^ (m - k) with hA
  set Rr : ℕ → R := fun n ↦ ∑ i ∈ Finset.range (n + 1), A i * (x * y) ^ (n - i) with hR
  set Lh : ℕ → R := fun n ↦ ∑ i ∈ Finset.range (n + 1),
    (if Even i then (x * y) ^ (i / 2) else 0) * (S (n - i) * T (n - i)) with hLh
  change Lh n = Rr n
  have hS0 : S 0 = 1 := by simp [hS]
  have hT0 : T 0 = 1 := by simp [hT]
  have hSrec : ∀ m, S (m + 1) = x * S m + 1 := fun m ↦ by simp only [hS, geom_sum_succ]
  have hTrec : ∀ m, T (m + 1) = y * T m + 1 := fun m ↦ by simp only [hT, geom_sum_succ]
  have hA0 : A 0 = 1 := by simp [hA, hS0]
  have hArec : ∀ m, A (m + 1) = S (m + 1) + y * A m := by
    intro m
    simp only [hA]
    rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Finset.mem_range] at hk
    rw [show m + 1 - k = (m - k) + 1 by omega, pow_succ]
    ring
  have hR0 : Rr 0 = 1 := by simp [hR, hA0]
  have hRrec : ∀ n, Rr (n + 1) = A (n + 1) + (x * y) * Rr n := by
    intro n
    simp only [hR]
    rw [Finset.sum_range_succ, Finset.mul_sum, Nat.sub_self, pow_zero, mul_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
    ring
  have hLhrec : ∀ n, Lh (n + 2) = S (n + 2) * T (n + 2) + (x * y) * Lh n := by
    intro n
    simp only [hLh]
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (if Even (i + 1 + 1) then (x * y) ^ ((i + 1 + 1) / 2) else 0) *
            (S (n + 2 - (i + 1 + 1)) * T (n + 2 - (i + 1 + 1)))
          = (x * y) * ((if Even i then (x * y) ^ (i / 2) else 0) * (S (n - i) * T (n - i))) := by
      intro i _
      rw [show n + 2 - (i + 1 + 1) = n - i by omega]
      by_cases he : Even i
      · rw [ite_eq_left he, ite_eq_left (by simpa [Nat.even_add_one] using he),
          show (i + 1 + 1) / 2 = i / 2 + 1 by omega, pow_succ]
        ring
      · rw [ite_eq_right he, ite_eq_right (by simpa [Nat.even_add_one] using he)]
        ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ite_eq_right (by simp : ¬ Even (0 + 1)),
      ite_eq_left (by simp : Even 0)]
    simp only [Nat.zero_div, pow_zero, Nat.sub_zero, zero_mul, add_zero, one_mul]
    ring
  have hC1 : ∀ m, S (m + 1) + (y - x) * A m = T (m + 1) := by
    intro m
    induction m with
    | zero => rw [hSrec, hTrec, hA0, hS0, hT0]; ring
    | succ k ih =>
      rw [hArec k, hSrec (k + 1), hTrec (k + 1)]
      linear_combination y * ih
  have hC2 : ∀ m, S (m + 1) * T (m + 1) = S (m + 1) + T (m + 1) - 1 + (x * y) * (S m * T m) := by
    intro m
    rw [hSrec, hTrec]
    ring
  have hC3 : ∀ m, A (m + 2) = (x * y) * A m + (S (m + 2) + T (m + 2) - 1) := by
    intro m
    rw [hArec (m + 1), hArec m, hTrec (m + 1)]
    linear_combination y * hC1 m
  have hC4 : ∀ n, Rr (n + 2) = S (n + 2) * T (n + 2) + (x * y) * Rr n := by
    intro n
    induction n with
    | zero =>
      rw [hRrec 1, hRrec 0, hArec 1, hArec 0, hSrec 1, hSrec 0, hTrec 1, hTrec 0, hA0, hR0,
        hS0, hT0]
      ring
    | succ n ih =>
      rw [hRrec (n + 2), hC3 (n + 1), ih, hC2 (n + 2), hRrec n]
      ring
  induction n using Nat.twoStepInduction with
  | zero => simp [hLh, hR0, hS0, hT0]
  | one =>
    have hLh1 : Lh 1 = S 1 * T 1 := by simp [hLh, Finset.sum_range_succ, hS0, hT0]
    rw [hLh1, hRrec 0, hArec 0, hSrec 0, hTrec 0, hA0, hR0, hS0, hT0]
    ring
  | more k ih _ => rw [hLhrec k, ih, hC4 k]

/-- **The convolution form of Ramanujan's identity.** For completely multiplicative arithmetic
functions `F` and `G`,
`squareLift (F · G) * ((ζ * F) · (ζ * G)) = ζ * F * G * (F · G)`,
where `·` is the pointwise product and `*` is Dirichlet convolution. -/
theorem squareLift_pmul_mul_pmul_zeta_mul {R : Type*} [CommRing R] {F G : ArithmeticFunction R}
    (hF : F.IsCompletelyMultiplicative) (hF1 : F 1 = 1) (hG : G.IsCompletelyMultiplicative)
    (hG1 : G 1 = 1) :
    (F.pmul G).squareLift * ((↑ζ * F).pmul (↑ζ * G)) = ↑ζ * F * G * F.pmul G := by
  have hFm := hF.isMultiplicative hF1
  have hGm := hG.isMultiplicative hG1
  have hζm : (↑ζ : ArithmeticFunction R).IsMultiplicative := isMultiplicative_zeta.natCast
  rw [IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((hFm.pmul hGm).squareLift.mul ((hζm.mul hFm).pmul (hζm.mul hGm))) _
    (((hζm.mul hFm).mul hGm).mul (hFm.pmul hGm))]
  intro p n hp
  have hFp : ∀ i : ℕ, F (p ^ i) = F p ^ i := fun i ↦ by
    induction i with
    | zero => simpa using hF1
    | succ k ih => rw [pow_succ, hF.map_mul, ih, pow_succ]
  have hGp : ∀ i : ℕ, G (p ^ i) = G p ^ i := fun i ↦ by
    induction i with
    | zero => simpa using hG1
    | succ k ih => rw [pow_succ, hG.map_mul, ih, pow_succ]
  have hHp : ∀ i : ℕ, (F.pmul G) (p ^ i) = (F p * G p) ^ i := fun i ↦ by
    rw [pmul_apply, hFp, hGp, mul_pow]
  have hζF : ∀ m : ℕ, (↑ζ * F) (p ^ m) = ∑ j ∈ Finset.range (m + 1), F p ^ j := fun m ↦ by
    rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    exact Finset.sum_congr rfl fun i _ ↦ hFp i
  have hζG : ∀ m : ℕ, (↑ζ * G) (p ^ m) = ∑ j ∈ Finset.range (m + 1), G p ^ j := fun m ↦ by
    rw [coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    exact Finset.sum_congr rfl fun i _ ↦ hGp i
  rw [mul_apply_prime_pow _ _ hp, mul_apply_prime_pow _ _ hp]
  convert local_identity (F p) (G p) n using 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pmul_apply, hζF, hζG, squareLift_apply]
    simp only [isSquare_prime_pow_iff hp i]
    by_cases he : Even i
    · obtain ⟨t, ht⟩ := he
      have hpi : p ^ i = (p ^ t) ^ 2 := by rw [← pow_mul]; congr 1; omega
      rw [ite_eq_left ⟨t, ht⟩, ite_eq_left ⟨t, ht⟩, hpi, Nat.sqrt_eq', hHp,
        show i / 2 = t by omega]
    · rw [ite_eq_right he, ite_eq_right he]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_apply_prime_pow _ _ hp, hHp]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ by rw [hζF, hGp]

/-! ### Absolute convergence -/

private theorem LSeriesSummable_sum_divisors_mul_sum_divisors {f g : ℕ → ℂ} {s : ℂ}
    (hfmul : ∀ m n : ℕ, f (m * n) = f m * f n) (hgmul : ∀ m n : ℕ, g (m * n) = g m * g n)
    (hone : LSeriesSummable (fun _ ↦ (1 : ℂ)) s) (hf : LSeriesSummable f s)
    (hg : LSeriesSummable g s) (hfg : LSeriesSummable (fun n ↦ f n * g n) s) :
    LSeriesSummable (fun n ↦ (∑ d ∈ n.divisors, f d) * (∑ d ∈ n.divisors, g d)) s := by
  classical
  -- Passing to absolute values preserves each of the four summability hypotheses.
  have habs : ∀ u : ℕ → ℂ, LSeriesSummable u s →
      LSeriesSummable (fun n ↦ ((‖u n‖ : ℝ) : ℂ)) s := by
    intro u hu
    refine Summable.of_norm ((hu.norm).congr fun n ↦ ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [LSeries.term_of_ne_zero hn]
  -- A real-valued convolution, cast into `ℂ`, is the convolution of the casts.
  have hconv : ∀ u v : ℕ → ℝ,
      ((fun k ↦ ((u k : ℝ) : ℂ)) ⍟ (fun k ↦ ((v k : ℝ) : ℂ)))
        = (fun k ↦ (((u ⍟ v) k : ℝ) : ℂ)) := by
    intro u v
    funext n
    simp only [LSeries.convolution_def]
    push_cast
    rfl
  -- The four-factor majorant `1 ⍟ |f| ⍟ |g| ⍟ |f * g|`.
  obtain ⟨Mr, hMr⟩ : ∃ M : ℕ → ℝ, M =
      ((fun _ : ℕ ↦ (1 : ℝ)) ⍟ (fun n ↦ ‖f n‖)) ⍟
        ((fun n ↦ ‖g n‖) ⍟ (fun n ↦ ‖f n * g n‖)) := ⟨_, rfl⟩
  have hMsum : LSeriesSummable (fun n ↦ ((Mr n : ℝ) : ℂ)) s := by
    have e0 : LSeriesSummable (fun n : ℕ ↦ (((fun _ : ℕ ↦ (1 : ℝ)) n : ℝ) : ℂ)) s := by
      simpa using hone
    have := (e0.convolution (habs f hf)).convolution ((habs g hg).convolution (habs _ hfg))
    rwa [hconv, hconv, hconv, ← hMr] at this
  -- The majorant dominates the coefficients pointwise.
  have hFmul : ∀ a b : ℕ, ‖f (a * b)‖ = ‖f a‖ * ‖f b‖ := fun a b ↦ by rw [hfmul, norm_mul]
  have hGmul : ∀ a b : ℕ, ‖g (a * b)‖ = ‖g a‖ * ‖g b‖ := fun a b ↦ by rw [hgmul, norm_mul]
  have hbound : ∀ n : ℕ, ‖(∑ d ∈ n.divisors, f d) * (∑ d ∈ n.divisors, g d)‖ ≤ Mr n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hMr, LSeries.convolution_def]
    have h1 : ‖(∑ d ∈ n.divisors, f d) * (∑ d ∈ n.divisors, g d)‖
        ≤ (∑ d ∈ n.divisors, ‖f d‖) * (∑ d ∈ n.divisors, ‖g d‖) := by
      rw [norm_mul]
      exact mul_le_mul (norm_sum_le _ _) (norm_sum_le _ _) (norm_nonneg _)
        (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)
    refine h1.trans ?_
    have hMrn : Mr n = ∑ e ∈ n.divisors,
        (∑ i ∈ (n / e).divisors, ‖f i‖) * (∑ i ∈ e.divisors, ‖g (e / i)‖ * ‖f i * g i‖) := by
      have hA : ∀ m : ℕ, ∑ x ∈ m.divisorsAntidiagonal, ‖f x.2‖ = ∑ i ∈ m.divisors, ‖f i‖ :=
        fun m ↦ Nat.sum_divisorsAntidiagonal' (fun _ b ↦ ‖f b‖)
      have hB : ∀ m : ℕ, ∑ x ∈ m.divisorsAntidiagonal, ‖g x.1‖ * ‖f x.2 * g x.2‖
          = ∑ i ∈ m.divisors, ‖g (m / i)‖ * ‖f i * g i‖ :=
        fun m ↦ Nat.sum_divisorsAntidiagonal' (fun a b ↦ ‖g a‖ * ‖f b * g b‖)
      simp only [hMr, LSeries.convolution_def, one_mul, hA, hB]
      exact Nat.sum_divisorsAntidiagonal'
        (fun a b ↦ (∑ i ∈ a.divisors, ‖f i‖) * ∑ i ∈ b.divisors, ‖g (b / i)‖ * ‖f i * g i‖)
    rw [hMrn, Finset.mul_sum]
    refine Finset.sum_le_sum fun e he ↦ ?_
    obtain ⟨hen, -⟩ := Nat.mem_divisors.mp he
    have he0 : e ≠ 0 := by
      rintro rfl
      exact hn (Nat.eq_zero_of_zero_dvd hen)
    have hne0 : n / e ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hen) (Nat.pos_of_ne_zero he0)).ne'
    -- Send a divisor `d` of `n` to the pair `(d / gcd d e, gcd d e)`.
    have hinj : Set.InjOn (fun d : ℕ ↦ (d / Nat.gcd d e, Nat.gcd d e)) (n.divisors : Set ℕ) := by
      intro a _ b _ hab
      simp only [Prod.mk.injEq] at hab
      calc a = a / Nat.gcd a e * Nat.gcd a e := (Nat.div_mul_cancel (Nat.gcd_dvd_left a e)).symm
        _ = b / Nat.gcd b e * Nat.gcd b e := by rw [hab.1, hab.2]
        _ = b := Nat.div_mul_cancel (Nat.gcd_dvd_left b e)
    have hstep : ∑ d ∈ n.divisors, ‖f d‖ * ‖g e‖
        = ∑ p ∈ n.divisors.image (fun d : ℕ ↦ (d / Nat.gcd d e, Nat.gcd d e)),
            ‖f p.1‖ * (‖g (e / p.2)‖ * ‖f p.2 * g p.2‖) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      have e1 : ‖f (d / Nat.gcd d e)‖ * ‖f (Nat.gcd d e)‖ = ‖f d‖ := by
        rw [← hFmul, Nat.div_mul_cancel (Nat.gcd_dvd_left d e)]
      have e2 : ‖g (e / Nat.gcd d e)‖ * ‖g (Nat.gcd d e)‖ = ‖g e‖ := by
        rw [← hGmul, Nat.div_mul_cancel (Nat.gcd_dvd_right d e)]
      rw [← e1, ← e2, norm_mul]
      ring
    have hsub : n.divisors.image (fun d : ℕ ↦ (d / Nat.gcd d e, Nat.gcd d e))
        ⊆ (n / e).divisors ×ˢ e.divisors := by
      intro p hp
      simp only [Finset.mem_image] at hp
      obtain ⟨d, hd, rfl⟩ := hp
      obtain ⟨hdn, -⟩ := Nat.mem_divisors.mp hd
      have hd0 : d ≠ 0 := by
        rintro rfl
        exact hn (Nat.eq_zero_of_zero_dvd hdn)
      have hc0 : Nat.gcd d e ≠ 0 := Nat.gcd_ne_zero_left hd0
      refine Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hne0⟩,
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right d e, he0⟩⟩
      rw [Nat.dvd_div_iff_mul_dvd hen]
      have key : Nat.gcd d e * (e * (d / Nat.gcd d e)) = Nat.gcd d e * Nat.lcm d e := by
        rw [Nat.gcd_mul_lcm, ← mul_assoc, mul_comm (Nat.gcd d e) e, mul_assoc,
          Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)]
        ring
      rw [Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc0) key]
      exact Nat.lcm_dvd hdn hen
    rw [Finset.sum_mul, hstep, Finset.sum_mul_sum, ← Finset.sum_product']
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ ↦ by positivity
  -- Comparison finishes the proof.
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) ?_ hMsum.norm
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hb := hbound n
  have hMn : ‖((Mr n : ℝ) : ℂ)‖ = Mr n := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans (norm_nonneg _) hb)]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div, hMn,
    div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hb (by positivity)

/-- **Absolute convergence of products of divisor sums.** For completely multiplicative `F` and
`G`, the Dirichlet series of `n ↦ (∑_{d ∣ n} F d) (∑_{d ∣ n} G d)` converges absolutely at `s`
as soon as `1 < re s` and the Dirichlet series of `F`, `G` and `F · G` converge absolutely
at `s`. -/
theorem LSeriesSummable_pmul_zeta_mul {F G : ArithmeticFunction ℂ}
    (hF : F.IsCompletelyMultiplicative) (hG : G.IsCompletelyMultiplicative) {s : ℂ}
    (hs : 1 < s.re) (hFs : LSeriesSummable (↗F) s) (hGs : LSeriesSummable (↗G) s)
    (hFGs : LSeriesSummable (↗(F.pmul G)) s) :
    LSeriesSummable (↗((↑ζ * F).pmul (↑ζ * G))) s := by
  have h := LSeriesSummable_sum_divisors_mul_sum_divisors (f := ⇑F) (g := ⇑G) hF hG
    (LSeriesSummable_one_iff.mpr hs) hFs hGs (by simpa only [pmul_apply] using hFGs)
  simpa only [pmul_apply, coe_zeta_mul_apply] using h

/-! ### The L-series identity -/

/-- **Ramanujan's identity for completely multiplicative functions.** For completely
multiplicative `F` and `G` whose Dirichlet series, and that of `F · G`, converge absolutely at
`s` with `1 < re s`,
`L((ζ * F) · (ζ * G), s) · L(F · G, 2s) = ζ(s) L(F, s) L(G, s) L(F · G, s)`. -/
theorem LSeries_pmul_zeta_mul_mul_LSeries_pmul {F G : ArithmeticFunction ℂ}
    (hF : F.IsCompletelyMultiplicative) (hF1 : F 1 = 1) (hG : G.IsCompletelyMultiplicative)
    (hG1 : G 1 = 1) {s : ℂ} (hs : 1 < s.re) (hFs : LSeriesSummable (↗F) s)
    (hGs : LSeriesSummable (↗G) s) (hFGs : LSeriesSummable (↗(F.pmul G)) s) :
    LSeries (↗((↑ζ * F).pmul (↑ζ * G))) s * LSeries (↗(F.pmul G)) (2 * s) =
      riemannZeta s * LSeries (↗F) s * LSeries (↗G) s * LSeries (↗(F.pmul G)) s := by
  have hζ : (↗(↑ζ : ArithmeticFunction ℂ)) = ↗ζ := funext fun n ↦ natCoe_apply
  have hZS : LSeriesSummable (↗(↑ζ : ArithmeticFunction ℂ)) s := by
    rw [hζ]
    exact LSeriesSummable_zeta_iff.mpr hs
  have hSqS : LSeriesSummable (↗(F.pmul G).squareLift) s :=
    (LSeriesSummable_squareLift_iff _ _).mpr <| hFGs.of_re_le_re <| by simp; linarith
  have hPS := LSeriesSummable_pmul_zeta_mul hF hG hs hFs hGs hFGs
  rw [← LSeries_squareLift, mul_comm, ← LSeries_mul' hSqS hPS,
    squareLift_pmul_mul_pmul_zeta_mul hF hF1 hG hG1,
    LSeries_mul' (LSeriesSummable_mul (LSeriesSummable_mul hZS hFs) hGs) hFGs,
    LSeries_mul' (LSeriesSummable_mul hZS hFs) hGs, LSeries_mul' hZS hFs, hζ,
    LSeries_zeta_eq_riemannZeta hs]

end ArithmeticFunction

/-! ### Twisted divisor sums -/

namespace DirichletCharacter

open ArithmeticFunction

variable {q : ℕ}

/-- The completely multiplicative function `n ↦ χ n * n ^ a`. -/
private noncomputable def cpowTwist (χ : DirichletCharacter ℂ q) (a : ℂ) :
    ArithmeticFunction ℂ :=
  toArithmeticFunction fun n ↦ χ n * (n : ℂ) ^ a

private theorem cpowTwist_apply (χ : DirichletCharacter ℂ q) (a : ℂ) {n : ℕ} (hn : n ≠ 0) :
    cpowTwist χ a n = χ n * (n : ℂ) ^ a := by
  simp [cpowTwist, toArithmeticFunction, hn]

private theorem cpowTwist_one (χ : DirichletCharacter ℂ q) (a : ℂ) : cpowTwist χ a 1 = 1 := by
  simp [cpowTwist_apply]

private theorem isCompletelyMultiplicative_cpowTwist (χ : DirichletCharacter ℂ q) (a : ℂ) :
    (cpowTwist χ a).IsCompletelyMultiplicative := by
  intro m n
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [cpowTwist_apply _ _ hm, cpowTwist_apply _ _ hn, cpowTwist_apply _ _ (mul_ne_zero hm hn),
    Nat.cast_mul, Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
  ring

private theorem cpowTwist_pmul (χ₁ χ₂ : DirichletCharacter ℂ q) (a b : ℂ) :
    (cpowTwist χ₁ a).pmul (cpowTwist χ₂ b) = cpowTwist (χ₁ * χ₂) (a + b) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [pmul_apply, cpowTwist_apply _ _ hn, cpowTwist_apply _ _ hn, cpowTwist_apply _ _ hn,
    MulChar.mul_apply, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  ring

private theorem zeta_mul_cpowTwist (χ : DirichletCharacter ℂ q) (a : ℂ) :
    ↑ζ * cpowTwist χ a = χ.sigmaR a := by
  ext n
  rw [coe_zeta_mul_apply, sigmaR_apply]
  exact Finset.sum_congr rfl fun d hd ↦ cpowTwist_apply _ _ (Nat.pos_of_mem_divisors hd).ne'

private theorem LSeries_cpowTwist (χ : DirichletCharacter ℂ q) (a s : ℂ) :
    LSeries (↗(cpowTwist χ a)) s = LSeries (↗χ) (s - a) :=
  (LSeries_congr (fun hn ↦ cpowTwist_apply χ a hn) s).trans (LSeries_mul_cpow _ a s)

private theorem LSeriesSummable_cpowTwist (χ : DirichletCharacter ℂ q) {a s : ℂ}
    (h : 1 < (s - a).re) : LSeriesSummable (↗(cpowTwist χ a)) s :=
  (LSeriesSummable_congr s (fun hn ↦ cpowTwist_apply χ a hn)).mpr <|
    (LSeriesSummable_mul_cpow_iff _ a s).mpr (χ.LSeriesSummable_of_one_lt_re h)

/-- **Ramanujan's formula, twisted by Dirichlet characters.** For Dirichlet characters `χ₁, χ₂`
modulo `q` and complex `a, b`, the Dirichlet series of `σ_{a,χ₁} σ_{b,χ₂}` is
`ζ(s) L(s - a, χ₁) L(s - b, χ₂) L(s - a - b, χ₁χ₂) / L(2s - a - b, χ₁χ₂)`
on the half-plane `re s > 1 + max (0, re a) + max (0, re b)` of absolute convergence. -/
theorem LSeries_sigmaR_mul_sigmaR (χ₁ χ₂ : DirichletCharacter ℂ q) {a b s : ℂ}
    (hs : 1 < s.re) (hsa : 1 < (s - a).re) (hsb : 1 < (s - b).re)
    (hsab : 1 < (s - a - b).re) :
    LSeries (fun n ↦ χ₁.sigmaR a n * χ₂.sigmaR b n) s =
      riemannZeta s * LSeries (↗χ₁) (s - a) * LSeries (↗χ₂) (s - b) *
          LSeries (↗(χ₁ * χ₂)) (s - a - b) / LSeries (↗(χ₁ * χ₂)) (2 * s - a - b) := by
  have hab : 1 < (s - (a + b)).re := by rwa [← sub_sub]
  have h2s : 1 < (2 * s - a - b).re := by
    rw [show 2 * s - a - b = s + (s - a - b) by ring, Complex.add_re]
    linarith
  have key := LSeries_pmul_zeta_mul_mul_LSeries_pmul (isCompletelyMultiplicative_cpowTwist χ₁ a)
    (cpowTwist_one χ₁ a) (isCompletelyMultiplicative_cpowTwist χ₂ b) (cpowTwist_one χ₂ b) hs
    (LSeriesSummable_cpowTwist χ₁ hsa) (LSeriesSummable_cpowTwist χ₂ hsb)
    (cpowTwist_pmul χ₁ χ₂ a b ▸ LSeriesSummable_cpowTwist (χ₁ * χ₂) hab)
  rw [zeta_mul_cpowTwist, zeta_mul_cpowTwist, cpowTwist_pmul, LSeries_cpowTwist,
    LSeries_cpowTwist, LSeries_cpowTwist, LSeries_cpowTwist, ← sub_sub, ← sub_sub] at key
  rw [eq_div_iff (LSeries_ne_zero_of_one_lt_re _ h2s), ← key]
  rfl

/-- The Dirichlet series of `|σ_{a,χ}|²`: for a Dirichlet character `χ` modulo `q` with
principal character `χ₀ = 1` and a complex `a`,
`∑ |σ_{a,χ}(n)|² n^{-s}
  = ζ(s) L(s - a, χ) L(s - ā, χ⁻¹) L(s - 2 re a, χ₀) / L(2s - 2 re a, χ₀)`
on the half-plane `re s > 1 + 2 max (0, re a)` of absolute convergence. -/
theorem LSeries_normSq_sigmaR (χ : DirichletCharacter ℂ q) {a s : ℂ} (hs : 1 < s.re)
    (ha : 1 < s.re - 2 * a.re) :
    LSeries (fun n ↦ (Complex.normSq (χ.sigmaR a n) : ℂ)) s =
      riemannZeta s * LSeries (↗χ) (s - a) * LSeries (↗χ⁻¹) (s - starRingEnd ℂ a) *
          LSeries (↗(1 : DirichletCharacter ℂ q)) (s - 2 * a.re) /
        LSeries (↗(1 : DirichletCharacter ℂ q)) (2 * s - 2 * a.re) := by
  have hconj : ∀ n : ℕ, starRingEnd ℂ (χ.sigmaR a n) = χ⁻¹.sigmaR (starRingEnd ℂ a) n := by
    intro n
    simp only [sigmaR_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    have harg : (d : ℂ).arg ≠ Real.pi := by simp [Complex.natCast_arg, Real.pi_ne_zero.symm]
    have hc : starRingEnd ℂ ((d : ℂ) ^ a) = (d : ℂ) ^ starRingEnd ℂ a := by
      have h := Complex.conj_cpow (d : ℂ) (starRingEnd ℂ a) harg
      rw [Complex.conj_natCast, Complex.conj_conj] at h
      exact h.symm
    rw [hc, ← MulChar.star_apply']
    rfl
  have hns : (fun n ↦ (Complex.normSq (χ.sigmaR a n) : ℂ)) =
      fun n ↦ χ.sigmaR a n * χ⁻¹.sigmaR (starRingEnd ℂ a) n := by
    funext n
    rw [← hconj, Complex.mul_conj]
  have h1 : s - a - starRingEnd ℂ a = s - 2 * a.re := by
    exact Complex.ext (by simp; ring) (by simp)
  have h2 : 2 * s - a - starRingEnd ℂ a = 2 * s - 2 * a.re := by
    exact Complex.ext (by simp; ring) (by simp)
  rw [hns, LSeries_sigmaR_mul_sigmaR χ χ⁻¹ hs (by simp; linarith) (by simp; linarith)
    (by rw [h1]; simpa using ha), mul_inv_cancel, h1, h2]

end DirichletCharacter

/-! ### Ramanujan's formula -/

namespace ArithmeticFunction

/-- **Ramanujan's formula.** For complex `a, b`, the Dirichlet series of `σ_a σ_b` is
`ζ(s) ζ(s - a) ζ(s - b) ζ(s - a - b) / ζ(2s - a - b)` on the half-plane
`re s > 1 + max (0, re a) + max (0, re b)` of absolute convergence. -/
theorem LSeries_sigmaR_mul_sigmaR {a b s : ℂ} (hs : 1 < s.re) (hsa : 1 < (s - a).re)
    (hsb : 1 < (s - b).re) (hsab : 1 < (s - a - b).re) :
    LSeries (fun n ↦ sigmaR a n * sigmaR b n) s =
      riemannZeta s * riemannZeta (s - a) * riemannZeta (s - b) * riemannZeta (s - a - b) /
        riemannZeta (2 * s - a - b) := by
  have h2s : 1 < (2 * s - a - b).re := by
    rw [show 2 * s - a - b = s + (s - a - b) by ring, Complex.add_re]
    linarith
  have h := DirichletCharacter.LSeries_sigmaR_mul_sigmaR (1 : DirichletCharacter ℂ 1)
    (1 : DirichletCharacter ℂ 1) hs hsa hsb hsab
  simp only [DirichletCharacter.sigmaR_modOne, mul_one, DirichletCharacter.LSeries_modOne_eq]
    at h
  rw [h, LSeries_one_eq_riemannZeta hsa, LSeries_one_eq_riemannZeta hsb,
    LSeries_one_eq_riemannZeta hsab, LSeries_one_eq_riemannZeta h2s]

/-- **Ramanujan's formula for the divisor function.** For `1 < re s`, the Dirichlet series of
`d(n)² = σ₀(n)²` is `ζ(s)⁴ / ζ(2s)`. -/
theorem LSeries_sigma_zero_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ ((σ 0 n : ℕ) : ℂ) ^ 2) s = riemannZeta s ^ 4 / riemannZeta (2 * s) := by
  have h := LSeries_sigmaR_mul_sigmaR (a := 0) (b := 0) hs (by simpa using hs) (by simpa using hs)
    (by simpa using hs)
  simp only [sigmaR_zero_apply, sub_zero] at h
  simp only [sigma_zero_apply, sq, h]
  ring

end ArithmeticFunction
