/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Growth of completed `L`-functions

The entire completed `L`-functions attached to Hurwitz zeta functions and to functions on `ZMod N`
are Mellin transforms of exponentially decaying theta kernels. Splitting the Mellin integral at
`1` and bounding `x ^ (N - 1) ≤ N! b⁻ᴺ eᵇˣ` shows that they are of *factorial type*:
`‖F s‖ ≤ A Bᴺ N!` whenever `‖s‖ + 1 ≤ N`. This gives `‖F s‖ ≤ ‖s‖ ^ (4 ‖s‖)` for large `‖s‖`, so
these functions have order of growth at most `1`.

## Main statements

* `WeakFEPair.exists_norm_Λ₀_le_mul_pow_mul_factorial`: the entire completion `Λ₀` of a weak
  FE-pair with exponentially decaying kernels is of factorial type.
* `HurwitzZeta.exists_norm_completedHurwitzZetaEven₀_le_mul_pow_mul_factorial`,
  `HurwitzZeta.exists_norm_completedHurwitzZetaOdd_le_mul_pow_mul_factorial`,
  `ZMod.exists_norm_completedLFunction₀_le_mul_pow_mul_factorial`: the completed Hurwitz zeta
  functions and the completed `L`-function of `Φ : ZMod N → ℂ` are of factorial type.
* `eventually_norm_le_rpow_of_le_mul_pow_mul_factorial`: a function of factorial type satisfies
  `‖F s‖ ≤ ‖s‖ ^ (4 ‖s‖)` for large `‖s‖`.
-/

@[expose] public section

open Filter Asymptotics Bornology MeasureTheory Set

/-- A one-sided Mellin integral `∫₁^∞ x ^ (t - 1) (h x - c) dx` of an exponentially decaying
kernel is of factorial type in `Re t`. -/
private lemma exists_norm_integral_Ioi_one_le (h : ℝ → ℂ) (c : ℂ) (hc : ContinuousOn h (Ioi 0))
    (hO : ∃ p : ℝ, 0 < p ∧ (fun x => h x - c) =O[atTop] fun x => Real.exp (-p * x)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 1 ≤ B ∧ ∀ (t : ℂ) (N : ℕ), t.re ≤ N →
      ‖∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (t - 1) * (h x - c)‖ ≤ A * B ^ N * N.factorial := by
  obtain ⟨p, hp, hO⟩ := hO
  set w : ℝ → ℝ := fun x => Real.exp (p / 2 * x) * ‖h x - c‖ with hw
  have hwint : IntegrableOn w (Ioi 1) := by
    refine integrable_of_isBigO_exp_neg (b := p / 2) (by positivity) ?_ ?_
    · refine (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul ?_
      refine ((hc.sub continuousOn_const).norm).mono ?_
      intro x (hx : (1 : ℝ) ≤ x); exact mem_Ioi.mpr (by linarith)
    · have := (isBigO_refl (fun x : ℝ => Real.exp (p / 2 * x)) atTop).mul hO.norm_left
      refine this.congr_right (fun x => ?_)
      rw [← Real.exp_add]; ring_nf
  refine ⟨∫ x in Ioi (1 : ℝ), w x, max 1 (2 / p),
    setIntegral_nonneg measurableSet_Ioi (fun x _ => by positivity),
    le_max_left _ _, fun t N htN => ?_⟩
  have hpt : ∀ x : ℝ, 1 < x → ‖(x : ℂ) ^ (t - 1) * (h x - c)‖ ≤
      (max 1 (2 / p)) ^ N * N.factorial * w x := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have h1 : ‖(x : ℂ) ^ (t - 1)‖ ≤ x ^ N := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0, ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hx.le (by simp; linarith)
    have hfac : x ^ N ≤ (max 1 (2 / p)) ^ N * N.factorial * Real.exp (p / 2 * x) := by
      have := Real.pow_div_factorial_le_exp (p / 2 * x) (by positivity) N
      rw [div_le_iff₀ (by positivity), mul_pow] at this
      have h2 : x ^ N = (2 / p) ^ N * ((p / 2) ^ N * x ^ N) := by
        rw [← mul_assoc, ← mul_pow]; field_simp; simp
      have h3 : (2 / p) ^ N ≤ (max 1 (2 / p)) ^ N :=
        pow_le_pow_left₀ (by positivity) (le_max_right _ _) N
      rw [h2]
      calc (2 / p) ^ N * ((p / 2) ^ N * x ^ N)
          ≤ (2 / p) ^ N * (Real.exp (p / 2 * x) * N.factorial) := by gcongr
        _ ≤ (max 1 (2 / p)) ^ N * (Real.exp (p / 2 * x) * N.factorial) := by gcongr
        _ = _ := by ring
    rw [norm_mul, hw]
    calc ‖(x : ℂ) ^ (t - 1)‖ * ‖h x - c‖ ≤ ((max 1 (2 / p)) ^ N * N.factorial *
          Real.exp (p / 2 * x)) * ‖h x - c‖ := by gcongr; exact h1.trans hfac
      _ = _ := by ring
  calc _ ≤ ∫ x in Ioi (1 : ℝ), (max 1 (2 / p)) ^ N * N.factorial * w x := by
        refine norm_integral_le_of_norm_le (hwint.const_mul _) ?_
        exact (ae_restrict_mem measurableSet_Ioi).mono fun x hx => hpt x hx
    _ = _ := by rw [integral_const_mul]; ring

namespace WeakFEPair

/-- **The entire completion of a weak FE-pair is of factorial type.** If the kernels `f`, `g` are
continuous on `(0, ∞)` and `f - f₀`, `g - g₀` decay exponentially at infinity, then there are
`A ≥ 0`, `B ≥ 1` with `‖Λ₀ t‖ ≤ A Bᴺ N!` whenever `Re t ≤ N` and `k - Re t ≤ N`. -/
theorem exists_norm_Λ₀_le_mul_pow_mul_factorial (P : WeakFEPair ℂ)
    (hfc : ContinuousOn P.f (Ioi 0)) (hgc : ContinuousOn P.g (Ioi 0))
    (hfO : ∃ p : ℝ, 0 < p ∧ (fun x => P.f x - P.f₀) =O[atTop] fun x => Real.exp (-p * x))
    (hgO : ∃ p : ℝ, 0 < p ∧ (fun x => P.g x - P.g₀) =O[atTop] fun x => Real.exp (-p * x)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 1 ≤ B ∧ ∀ (t : ℂ) (N : ℕ), t.re ≤ N → P.k - t.re ≤ N →
      ‖P.Λ₀ t‖ ≤ A * B ^ N * N.factorial := by
  obtain ⟨A₁, B₁, hA₁, hB₁, h₁⟩ := exists_norm_integral_Ioi_one_le P.f P.f₀ hfc hfO
  obtain ⟨A₂, B₂, hA₂, hB₂, h₂⟩ := exists_norm_integral_Ioi_one_le P.g P.g₀ hgc hgO
  set F := P.f_modif with hFdef
  set G : ℝ → ℂ := (Ioi 1).indicator (fun x => P.f x - P.f₀) with hGdef
  set H : ℝ → ℂ := (Ioi 1).indicator (fun x => P.g x - P.g₀) with hHdef
  have hFGH : ∀ x : ℝ, 0 < x →
      F x = G x + P.ε • ((x : ℂ) ^ (-(P.k : ℂ)) • H x⁻¹) := by
    intro x hx
    rcases lt_trichotomy x 1 with h | rfl | h
    · have hxinv : 1 < x⁻¹ := (one_lt_inv₀ hx).mpr h
      have hx1 : x ∉ Ioi 1 := fun h' => (lt_asymm h h').elim
      have hfe := P.h_feq x⁻¹ (inv_pos.mpr hx)
      rw [one_div, inv_inv] at hfe
      simp only [hGdef, hHdef, hFdef, WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem
        (show x ∈ Ioo 0 1 from ⟨hx, h⟩), indicator_of_notMem hx1,
        indicator_of_mem (show x⁻¹ ∈ Ioi 1 from hxinv), hfe]
      have hc : ((x⁻¹ ^ P.k : ℝ) : ℂ) = (x : ℂ) ^ (-(P.k : ℂ)) := by
        rw [Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, Complex.ofReal_cpow hx.le]
        push_cast; ring_nf
      have hc' : ((x ^ (-P.k) : ℝ) : ℂ) = (x : ℂ) ^ (-(P.k : ℂ)) := by
        rw [Complex.ofReal_cpow hx.le]; push_cast; ring_nf
      simp only [smul_eq_mul, hc, hc', zero_add]
      ring
    · simp [hGdef, hHdef, hFdef, WeakFEPair.f_modif]
    · have hxinv : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ h
      have hx1 : x⁻¹ ∉ Ioi 1 := fun h' => (lt_asymm hxinv h').elim
      have hx2 : x ∉ Ioo 0 1 := fun h' => (lt_asymm h h'.2).elim
      simp [hGdef, hHdef, hFdef, WeakFEPair.f_modif, indicator_of_mem
        (show x ∈ Ioi 1 from h), indicator_of_notMem hx1, indicator_of_notMem hx2]
  have hconv : ∀ t : ℂ, MellinConvergent F t :=
    fun t => (P.isStrongFEPair_toStrongFEPair.hasMellin t).1
  have hGconv : ∀ t : ℂ, MellinConvergent G t := by
    intro t
    refine ((hconv t).indicator (measurableSet_Ioi (a := (1 : ℝ)))).congr_fun
      (fun x _ => ?_) measurableSet_Ioi
    by_cases h : 1 < x
    · simp [hGdef, hFdef, WeakFEPair.f_modif, h,
        indicator_of_notMem (show x ∉ Ioo 0 1 from fun h' => (lt_asymm h h'.2).elim)]
    · simp [hGdef, h]
  have hmellin : ∀ (h : ℝ → ℂ) (c : ℂ) (t : ℂ),
      mellin ((Ioi 1).indicator (fun x => h x - c)) t =
      ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (t - 1) * (h x - c) := by
    intro h c t
    rw [mellin, setIntegral_congr_fun measurableSet_Ioi
      (g := (Ioi 1).indicator (fun x : ℝ => (x : ℂ) ^ (t - 1) * (h x - c)))
      (fun x _ => ?_), setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi,
      sup_of_le_right zero_le_one]
    by_cases hx : 1 < x
    · simp [indicator_of_mem (show x ∈ Ioi 1 from hx)]
    · simp [indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from hx)]
  have hsplit : ∀ t : ℂ, P.Λ₀ t = mellin G t + P.ε • mellin H (P.k - t) := by
    intro t
    have hH : IntegrableOn (fun x : ℝ =>
        (x : ℂ) ^ (t - 1) • (P.ε • ((x : ℂ) ^ (-(P.k : ℂ)) • H x⁻¹))) (Ioi 0) := by
      refine ((hconv t).sub (hGconv t)).congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp only [Pi.sub_apply, hFGH x hx, smul_add, add_sub_cancel_left]
    have e1 : P.Λ₀ t = mellin G t +
        mellin (fun x : ℝ => P.ε • ((x : ℂ) ^ (-(P.k : ℂ)) • H x⁻¹)) t := by
      rw [WeakFEPair.Λ₀, mellin, mellin, mellin, ← integral_add (hGconv _) hH]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      simp only [← hFdef, hFGH x hx, smul_add]
    rw [e1, mellin_const_smul, mellin_cpow_smul, mellin_comp_inv]
    congr 3
    ring
  refine ⟨A₁ + ‖P.ε‖ * A₂, B₁ + B₂, by positivity, by linarith, fun t N ht1 ht2 => ?_⟩
  rw [hsplit, hGdef, hHdef, hmellin, hmellin]
  have e1 := h₁ t N ht1
  have e2 := h₂ (P.k - t) N (by simpa using ht2)
  have p1 : B₁ ^ N ≤ (B₁ + B₂) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
  have p2 : B₂ ^ N ≤ (B₁ + B₂) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
  have hf : (0 : ℝ) ≤ N.factorial := by positivity
  calc _ ≤ ‖∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (t - 1) * (P.f x - P.f₀)‖ + ‖P.ε‖ *
        ‖∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (P.k - t - 1) * (P.g x - P.g₀)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul]
    _ ≤ A₁ * B₁ ^ N * N.factorial + ‖P.ε‖ * (A₂ * B₂ ^ N * N.factorial) := by gcongr
    _ ≤ A₁ * (B₁ + B₂) ^ N * N.factorial + ‖P.ε‖ * (A₂ * (B₁ + B₂) ^ N * N.factorial) := by
        gcongr
    _ = _ := by ring

end WeakFEPair

namespace HurwitzZeta

/-- The even completed Hurwitz zeta function `Λ₀(a, s)` is of factorial type. -/
theorem exists_norm_completedHurwitzZetaEven₀_le_mul_pow_mul_factorial (a : UnitAddCircle) :
    ∃ A B : ℝ, 0 ≤ A ∧ 1 ≤ B ∧ ∀ (s : ℂ) (N : ℕ),
      ‖s‖ + 1 ≤ N → ‖completedHurwitzZetaEven₀ a s‖ ≤ A * B ^ N * N.factorial := by
  obtain ⟨A, B, hA, hB, h⟩ := (hurwitzEvenFEPair a).exists_norm_Λ₀_le_mul_pow_mul_factorial
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_evenKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_cosKernel a))
    (by
      obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub a
      refine ⟨p, hp, (Complex.isBigO_ofReal_left.mpr hO).congr_left (fun x => ?_)⟩
      by_cases ha : a = 0 <;> simp [hurwitzEvenFEPair, ha])
    (by
      obtain ⟨p, hp, hO⟩ := isBigO_atTop_cosKernel_sub a
      refine ⟨p, hp, (Complex.isBigO_ofReal_left.mpr hO).congr_left (fun x => ?_)⟩
      simp [hurwitzEvenFEPair])
  refine ⟨A, B, hA, hB, fun s N hN => ?_⟩
  have hre := abs_le.1 (Complex.abs_re_le_norm s)
  have h1 := h (s / 2) N (by simp; linarith) (by simp [hurwitzEvenFEPair]; linarith)
  rw [completedHurwitzZetaEven₀, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
  have : 0 ≤ A * B ^ N * N.factorial := by positivity
  linarith [norm_nonneg ((hurwitzEvenFEPair a).Λ₀ (s / 2))]

/-- The odd completed Hurwitz zeta function `Λ(a, s)` is of factorial type. -/
theorem exists_norm_completedHurwitzZetaOdd_le_mul_pow_mul_factorial (a : UnitAddCircle) :
    ∃ A B : ℝ, 0 ≤ A ∧ 1 ≤ B ∧ ∀ (s : ℂ) (N : ℕ),
      ‖s‖ + 1 ≤ N → ‖completedHurwitzZetaOdd a s‖ ≤ A * B ^ N * N.factorial := by
  obtain ⟨A, B, hA, hB, h⟩ := (hurwitzOddFEPair a).exists_norm_Λ₀_le_mul_pow_mul_factorial
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_oddKernel a))
    (Complex.continuous_ofReal.comp_continuousOn (continuousOn_sinKernel a))
    (by
      obtain ⟨p, hp, hO⟩ := isBigO_atTop_oddKernel a
      refine ⟨p, hp, (Complex.isBigO_ofReal_left.mpr hO).congr_left (fun x => ?_)⟩
      simp [hurwitzOddFEPair])
    (by
      obtain ⟨p, hp, hO⟩ := isBigO_atTop_sinKernel a
      refine ⟨p, hp, (Complex.isBigO_ofReal_left.mpr hO).congr_left (fun x => ?_)⟩
      simp [hurwitzOddFEPair])
  refine ⟨A, B, hA, hB, fun s N hN => ?_⟩
  have hre := abs_le.1 (Complex.abs_re_le_norm s)
  have h1 := h ((s + 1) / 2) N (by simp; linarith) (by simp [hurwitzOddFEPair]; linarith)
  have hΛ : (hurwitzOddFEPair a).Λ ((s + 1) / 2) = (hurwitzOddFEPair a).Λ₀ ((s + 1) / 2) := by
    simp [WeakFEPair.Λ, hurwitzOddFEPair]
  rw [completedHurwitzZetaOdd, hΛ, norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
  have : 0 ≤ A * B ^ N * N.factorial := by positivity
  linarith [norm_nonneg ((hurwitzOddFEPair a).Λ₀ ((s + 1) / 2))]

end HurwitzZeta

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- The entire completed `L`-function `Λ₀(Φ, s)` of `Φ : ZMod N → ℂ` is of factorial type. -/
theorem exists_norm_completedLFunction₀_le_mul_pow_mul_factorial (Φ : ZMod N → ℂ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 1 ≤ B ∧ ∀ (s : ℂ) (M : ℕ),
      ‖s‖ + 1 ≤ M → ‖completedLFunction₀ Φ s‖ ≤ A * B ^ M * M.factorial := by
  choose AE BE hAE hBE hE using fun j : ZMod N =>
    HurwitzZeta.exists_norm_completedHurwitzZetaEven₀_le_mul_pow_mul_factorial (toAddCircle j)
  choose AO BO hAO hBO hO using fun j : ZMod N =>
    HurwitzZeta.exists_norm_completedHurwitzZetaOdd_le_mul_pow_mul_factorial (toAddCircle j)
  set A : ℝ := ∑ j, ‖Φ j‖ * (AE j + AO j) with hAdef
  set B : ℝ := (N : ℝ) * ∑ j, (BE j + BO j) with hBdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hB' : ∀ j, BE j + BO j ≤ ∑ j, (BE j + BO j) := fun j =>
    Finset.single_le_sum (f := fun j => BE j + BO j)
      (fun i _ => by linarith [hBE i, hBO i]) (Finset.mem_univ j)
  have hBE' : ∀ j, BE j ≤ ∑ j, (BE j + BO j) := fun j => by linarith [hB' j, hBO j]
  have hBO' : ∀ j, BO j ≤ ∑ j, (BE j + BO j) := fun j => by linarith [hB' j, hBE j]
  have hS1 : 1 ≤ ∑ j, (BE j + BO j) := (hBE 0).trans (hBE' 0)
  refine ⟨A, B, Finset.sum_nonneg fun j _ => by have := hAE j; have := hAO j; positivity,
    one_le_mul_of_one_le_of_one_le hN1 hS1, fun s M hM => ?_⟩
  set S := ∑ j, (BE j + BO j) with hS
  have hre := abs_le.1 (Complex.abs_re_le_norm s)
  have hNs : ‖(N : ℂ) ^ (-s)‖ ≤ (N : ℝ) ^ M := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (NeZero.ne N)), ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by simp; linarith)
  have hfac0 : (0 : ℝ) ≤ M.factorial := by positivity
  have hsum : ‖∑ j, Φ j * HurwitzZeta.completedHurwitzZetaEven₀ (toAddCircle j) s +
      ∑ j, Φ j * HurwitzZeta.completedHurwitzZetaOdd (toAddCircle j) s‖ ≤
      A * S ^ M * M.factorial := by
    rw [← Finset.sum_add_distrib, hAdef, Finset.sum_mul, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← mul_add, norm_mul]
    have h1 := hE j s M hM
    have h2 := hO j s M hM
    have e1 : BE j ^ M ≤ S ^ M := pow_le_pow_left₀ (by linarith [hBE j]) (hBE' j) M
    have e2 : BO j ^ M ≤ S ^ M := pow_le_pow_left₀ (by linarith [hBO j]) (hBO' j) M
    have := hAE j
    have := hAO j
    calc ‖Φ j‖ * ‖_ + _‖ ≤ ‖Φ j‖ * (AE j * BE j ^ M * M.factorial +
          AO j * BO j ^ M * M.factorial) := by
          gcongr; exact (norm_add_le _ _).trans (add_le_add h1 h2)
      _ ≤ ‖Φ j‖ * (AE j * S ^ M * M.factorial + AO j * S ^ M * M.factorial) := by gcongr
      _ = _ := by ring
  rw [completedLFunction₀, ← mul_add, norm_mul, hBdef, mul_pow]
  calc _ ≤ (N : ℝ) ^ M * (A * S ^ M * M.factorial) :=
        mul_le_mul hNs hsum (norm_nonneg _) (by positivity)
    _ = _ := by ring

end ZMod

/-- **Factorial type gives order at most `1`.** If `‖F s‖ ≤ A Bᴺ N!` whenever `‖s‖ + 1 ≤ N`, then
`‖F s‖ ≤ ‖s‖ ^ (4 ‖s‖)` for all large `‖s‖`. -/
theorem eventually_norm_le_rpow_of_le_mul_pow_mul_factorial {E : Type*} [Norm E] {F : ℂ → E}
    {A B : ℝ} (hB : 0 ≤ B)
    (h : ∀ (s : ℂ) (N : ℕ), ‖s‖ + 1 ≤ N → ‖F s‖ ≤ A * B ^ N * N.factorial) :
    ∀ᶠ s in cobounded ℂ, ‖F s‖ ≤ ‖s‖ ^ (4 * ‖s‖) := by
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop (max 7 (max A B))] with s hs
  set r := ‖s‖ with hr
  have hr7 : 7 ≤ r := le_of_max_le_left hs
  have hAr : A ≤ r := le_of_max_le_left (le_of_max_le_right hs)
  have hBr : B ≤ r := le_of_max_le_right (le_of_max_le_right hs)
  set N := ⌈r⌉₊ + 1 with hNdef
  have hN1 : r + 1 ≤ N := by
    have := Nat.le_ceil r; rw [hNdef]; push_cast; linarith
  have hN2 : (N : ℝ) ≤ r + 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ r by linarith); rw [hNdef]; push_cast; linarith
  have hr1 : 1 ≤ r := by linarith
  refine (h s N hN1).trans ?_
  have hfac : (N.factorial : ℝ) ≤ (r ^ 2) ^ N := by
    calc (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by exact_mod_cast Nat.factorial_le_pow N
      _ ≤ (r ^ 2) ^ N := pow_le_pow_left₀ (Nat.cast_nonneg _) (by nlinarith) N
  calc A * B ^ N * N.factorial ≤ r * r ^ N * (r ^ 2) ^ N := by
        gcongr
    _ = r ^ (3 * N + 1) := by ring
    _ = r ^ (((3 * N + 1 : ℕ) : ℝ)) := (Real.rpow_natCast r _).symm
    _ ≤ r ^ (4 * r) := Real.rpow_le_rpow_of_exponent_le hr1 (by push_cast; linarith)
