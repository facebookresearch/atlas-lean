/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.LSeries.Linearity
import MathlibExt.NumberTheory.ArithmeticFunction.DivisorBounds
import MathlibExt.NumberTheory.SelbergClass.CompletedFunction
import MathlibExt.NumberTheory.SelbergClass.ZeroCounting

/-!
# The degree of a function in the Selberg class

The Selberg class is closed under products: the functional equation of `F₁ F₂` is
`FunctionalEquation.mul`, which concatenates the Gamma factors. The degree `2 ∑ α_i` of a
functional equation is additive: `deg (F₁ F₂) = deg F₁ + deg F₂` for *every* functional equation
of `F₁ F₂`, not only the one built from those of `F₁` and `F₂`. This follows from Selberg's
zero-counting theorem, since the zeros of `F₁ F₂` are those of `F₁` and of `F₂`.

## Main statements

* `SelbergClass.mul_mem`: the Selberg class is closed under products.
* `SelbergClass.FunctionalEquation.degree_eq_add_of_mul`: the degree is additive.
-/

open ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClass


/-- The continuation of `L(a₁ * a₂, s)` is `F₁ F₂` off `1`. -/
private lemma isLSeriesContinuation_mul {a₁ a₂ : ArithmeticFunction ℂ} (ha₁ : a₁ ∈ selbergClass)
    (ha₂ : a₂ ∈ selbergClass) {F₁ F₂ F : ℂ → ℂ} (hF₁ : IsLSeriesContinuation a₁ F₁)
    (hF₂ : IsLSeriesContinuation a₂ F₂) (hF : IsLSeriesContinuation (a₁ * a₂) F) :
    ∀ s : ℂ, s ≠ 1 → F s = F₁ s * F₂ s := by
  have hP : IsLSeriesContinuation (a₁ * a₂) (fun s => F₁ s * F₂ s) := by
    refine ⟨fun s hs => ?_, hF₁.2.mul hF₂.2⟩
    change F₁ s * F₂ s = _
    rw [hF₁.1 s hs, hF₂.1 s hs, ArithmeticFunction.LSeries_mul'
      (LSeriesSummable.of_forall_norm_le_mul_rpow ha₁.2.2.2 hs)
          (LSeriesSummable.of_forall_norm_le_mul_rpow ha₂.2.2.2 hs)]
  exact IsLSeriesContinuation.eqOn_compl_one hF hP

/-- The convolution of two coefficient sequences with subpolynomial growth has subpolynomial
growth. -/
private lemma forall_norm_mul_le_rpow {a₁ a₂ : ArithmeticFunction ℂ}
    (h₁ : ∀ ε > (0 : ℝ), ∃ C, ∀ n, ‖a₁ n‖ ≤ C * (n : ℝ) ^ ε)
    (h₂ : ∀ ε > (0 : ℝ), ∃ C, ∀ n, ‖a₂ n‖ ≤ C * (n : ℝ) ^ ε) :
    ∀ ε > (0 : ℝ), ∃ C, ∀ n, ‖(a₁ * a₂) n‖ ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨C₁, hC₁⟩ := h₁ (ε / 2) (by positivity)
  obtain ⟨C₂, hC₂⟩ := h₂ (ε / 2) (by positivity)
  obtain ⟨Cd, -, hCd'⟩ := exists_sigma_zero_le_mul_rpow (ε := ε / 2) (by positivity)
  have hCd : ∀ n : ℕ, (n.divisors.card : ℝ) ≤ Cd * (n : ℝ) ^ (ε / 2) := fun n => by
    simpa [sigma_zero_apply] using hCd' n
  refine ⟨Cd * (|C₁| * |C₂|), fun n => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow hε.ne']
  have hb : ∀ x ∈ n.divisorsAntidiagonal, ‖a₁ x.1 * a₂ x.2‖ ≤ |C₁| * |C₂| * (n : ℝ) ^ (ε / 2) := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    have e1 : ‖a₁ x.1‖ ≤ |C₁| * (x.1 : ℝ) ^ (ε / 2) :=
      (hC₁ x.1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have e2 : ‖a₂ x.2‖ ≤ |C₂| * (x.2 : ℝ) ^ (ε / 2) :=
      (hC₂ x.2).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have hn' : (n : ℝ) ^ (ε / 2) = (x.1 : ℝ) ^ (ε / 2) * (x.2 : ℝ) ^ (ε / 2) := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      rw [← hx.1]; push_cast; ring_nf
    rw [norm_mul, hn']
    calc ‖a₁ x.1‖ * ‖a₂ x.2‖ ≤ (|C₁| * (x.1 : ℝ) ^ (ε / 2)) * (|C₂| * (x.2 : ℝ) ^ (ε / 2)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [ArithmeticFunction.mul_apply]
  calc ‖∑ x ∈ n.divisorsAntidiagonal, a₁ x.1 * a₂ x.2‖
      ≤ ∑ x ∈ n.divisorsAntidiagonal, ‖a₁ x.1 * a₂ x.2‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ n.divisorsAntidiagonal, |C₁| * |C₂| * (n : ℝ) ^ (ε / 2) := Finset.sum_le_sum hb
    _ = (n.divisors.card : ℝ) * (|C₁| * |C₂| * (n : ℝ) ^ (ε / 2)) := by
      rw [Finset.sum_const, ← Nat.map_div_right_divisors, Finset.card_map, nsmul_eq_mul]
    _ ≤ (Cd * (n : ℝ) ^ (ε / 2)) * (|C₁| * |C₂| * (n : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right (hCd n) (by positivity)
    _ = Cd * (|C₁| * |C₂|) * ((n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (ε / 2)) := by ring
    _ = Cd * (|C₁| * |C₂|) * (n : ℝ) ^ ε := by
      rw [← Real.rpow_add (by positivity)]; ring_nf

/-- **Products in the Selberg class.** The Selberg class is closed under products: if `a₁, a₂`
are in the Selberg class, so is `a₁ * a₂`, whose `L`-function is the product of their
`L`-functions. -/
theorem mul_mem {a₁ a₂ : ArithmeticFunction ℂ} (ha₁ : a₁ ∈ selbergClass)
    (ha₂ : a₂ ∈ selbergClass) : a₁ * a₂ ∈ selbergClass := by
  obtain ⟨h1₁, ⟨F₁, hF₁, ⟨m₁, G₁, β₁, hG₁d, hG₁o, hG₁F⟩, ⟨D₁⟩⟩, ⟨b₁, θ₁, hθ₁, hlog₁, C₁, hb₁⟩,
    hram₁⟩ := ha₁
  obtain ⟨h1₂, ⟨F₂, hF₂, ⟨m₂, G₂, β₂, hG₂d, hG₂o, hG₂F⟩, ⟨D₂⟩⟩, ⟨b₂, θ₂, hθ₂, hlog₂, C₂, hb₂⟩,
    hram₂⟩ := ha₂
  have hF : IsLSeriesContinuation (a₁ * a₂) (fun s => F₁ s * F₂ s) := by
    refine ⟨fun s hs => ?_, hF₁.2.mul hF₂.2⟩
    change F₁ s * F₂ s = _
    rw [hF₁.1 s hs, hF₂.1 s hs, ArithmeticFunction.LSeries_mul'
      (LSeriesSummable.of_forall_norm_le_mul_rpow hram₁ hs)
          (LSeriesSummable.of_forall_norm_le_mul_rpow hram₂ hs)]
  refine ⟨by rw [ArithmeticFunction.mul_apply_one, h1₁, h1₂, one_mul],
    ⟨_, hF, ⟨m₁ + m₂, fun z => G₁ z * G₂ z, max β₁ β₂, hG₁d.mul hG₂d, (hG₁o.mono (le_max_left _
        _)).mul (hG₂o.mono (le_max_right _ _)), ?_⟩,
      ⟨D₁.mul D₂⟩⟩, ⟨b₁ + b₂, max θ₁ θ₂, max_lt hθ₁ hθ₂, ⟨?_, ?_⟩, |C₁| + |C₂|, ?_⟩,
    forall_norm_mul_le_rpow hram₁ hram₂⟩
  · intro s hs
    change G₁ s * G₂ s = _
    rw [hG₁F s hs, hG₂F s hs]
    ring
  · intro n hn
    have : b₁ n ≠ 0 ∨ b₂ n ≠ 0 := by
      by_contra h
      push Not at h
      simp [h.1, h.2] at hn
    rcases this with h | h
    · exact hlog₁.1 n h
    · exact hlog₂.1 n h
  · intro s hs
    obtain ⟨hs₁, he₁⟩ := hlog₁.2 s hs
    obtain ⟨hs₂, he₂⟩ := hlog₂.2 s hs
    refine ⟨hs₁.add hs₂, ?_⟩
    rw [LSeries_add hs₁ hs₂, Complex.exp_add, ← he₁, ← he₂, ArithmeticFunction.LSeries_mul'
      (LSeriesSummable.of_forall_norm_le_mul_rpow hram₁ hs)
          (LSeriesSummable.of_forall_norm_le_mul_rpow hram₂ hs)]
  · intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have z1 : b₁ 0 = 0 := by
        by_contra h; exact not_isPrimePow_zero (hlog₁.1 0 h)
      have z2 : b₂ 0 = 0 := by
        by_contra h; exact not_isPrimePow_zero (hlog₂.1 0 h)
      simp only [Pi.add_apply, z1, z2, add_zero, norm_zero]
      have : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ max θ₁ θ₂ := Real.rpow_nonneg (by simp) _
      positivity
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have k1 : (n : ℝ) ^ θ₁ ≤ (n : ℝ) ^ max θ₁ θ₂ :=
      Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _)
    have k2 : (n : ℝ) ^ θ₂ ≤ (n : ℝ) ^ max θ₁ θ₂ :=
      Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right _ _)
    have p1 : 0 ≤ (n : ℝ) ^ θ₁ := by positivity
    have p2 : 0 ≤ (n : ℝ) ^ θ₂ := by positivity
    have e1 : ‖b₁ n‖ ≤ |C₁| * (n : ℝ) ^ θ₁ :=
      (hb₁ n).trans (mul_le_mul_of_nonneg_right (le_abs_self _) p1)
    have e2 : ‖b₂ n‖ ≤ |C₂| * (n : ℝ) ^ θ₂ :=
      (hb₂ n).trans (mul_le_mul_of_nonneg_right (le_abs_self _) p2)
    calc ‖(b₁ + b₂) n‖ ≤ ‖b₁ n‖ + ‖b₂ n‖ := norm_add_le _ _
      _ ≤ |C₁| * (n : ℝ) ^ θ₁ + |C₂| * (n : ℝ) ^ θ₂ := add_le_add e1 e2
      _ ≤ |C₁| * (n : ℝ) ^ max θ₁ θ₂ + |C₂| * (n : ℝ) ^ max θ₁ θ₂ :=
        add_le_add (mul_le_mul_of_nonneg_left k1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left k2 (abs_nonneg _))
      _ = _ := by ring

/-- The continuation of a member of the Selberg class does not vanish at `2`, and is not locally
    zero
anywhere off `1`. -/
private lemma analyticOrderAt_ne_top_of_mem {a : ArithmeticFunction ℂ} (ha : a ∈ selbergClass) {F :
    ℂ → ℂ}
    (hF : IsLSeriesContinuation a F) {ρ : ℂ} (hρ : ρ ≠ 1) : analyticOrderAt F ρ ≠ ⊤ := by
  obtain ⟨-, -, ⟨b, θ, -, hlog, -⟩, -⟩ := ha
  have h2 : F 2 ≠ 0 := by
    rw [hF.1 2 (by norm_num), (hlog.2 2 (by norm_num)).2]; exact Complex.exp_ne_zero _
  intro h
  rw [analyticOrderAt_eq_top] at h
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  exact h2 ((hF.2.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc
    (show ρ ∈ ({1}ᶜ : Set ℂ) from hρ) h (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num))

/-- The zeros of the continuation of a member of the Selberg class in `0 ≤ Re ρ`, `0 ≤ Im ρ ≤ T` are
    finite. -/
private lemma finite_setOf_zeros_of_mem {a : ArithmeticFunction ℂ} (ha : a ∈ selbergClass) {F : ℂ →
    ℂ}
    (hF : IsLSeriesContinuation a F) (T : ℝ) :
    {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T}.Finite := by
  obtain ⟨-, ⟨F₀, hF₀, ⟨m, G, β, hGd, -, hGF₀⟩, -⟩, ⟨b, θ, -, hlog, -⟩, -⟩ := ha
  have hne : ∀ s : ℂ, 1 < s.re → F s ≠ 0 := fun s hs => by
    rw [hF.1 s hs, (hlog.2 s hs).2]; exact Complex.exp_ne_zero _
  have hG2 : G 2 ≠ 0 := by
    rw [hGF₀ 2 (by norm_num), ← IsLSeriesContinuation.eqOn_compl_one hF hF₀ 2 (by norm_num)]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (hne 2 (by norm_num))
  refine ((Complex.finite_setOf_eq_zero_norm_le hGd hG2 (1 + |T|)).union (Set.finite_singleton
      1)).subset ?_
  rintro ρ ⟨h0, h1, h2, h3⟩
  by_cases hρ : ρ = 1
  · exact Or.inr hρ
  refine Or.inl ⟨by rw [hGF₀ ρ hρ, ← IsLSeriesContinuation.eqOn_compl_one hF hF₀ ρ hρ, h0,
      mul_zero], ?_⟩
  have hre : ρ.re ≤ 1 := by
    by_contra h
    exact hne ρ (by linarith) h0
  have := Complex.norm_le_abs_re_add_abs_im ρ
  rw [abs_of_nonneg h1, abs_of_nonneg h2] at this
  linarith [le_abs_self T]

/-- A nonzero value gives order `0`. -/
private lemma analyticOrderNatAt_eq_zero_of_ne_zero {X : ℂ → ℂ} {ρ : ℂ} (h : X ρ ≠ 0) :
    analyticOrderNatAt X ρ = 0 := by
  by_cases han : AnalyticAt ℂ X ρ
  · simp [analyticOrderNatAt, han.analyticOrderAt_eq_zero.2 h]
  · simp [analyticOrderNatAt, analyticOrderAt, han]

/-- Up to a constant, the zero count of `F₁ F₂` is the sum of the zero counts. -/
private lemma zeroCount_mul {a₁ a₂ : ArithmeticFunction ℂ} (ha₁ : a₁ ∈ selbergClass)
    (ha₂ : a₂ ∈ selbergClass) {F₁ F₂ F : ℂ → ℂ} (hF₁ : IsLSeriesContinuation a₁ F₁)
    (hF₂ : IsLSeriesContinuation a₂ F₂) (hF : IsLSeriesContinuation (a₁ * a₂) F) (ha : a₁ * a₂ ∈
        selbergClass) :
    ∃ c : ℝ, ∀ T : ℝ, 0 ≤ T →
      ((∑ᶠ ρ ∈ {ρ : ℂ | F ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T},
        analyticOrderNatAt F ρ : ℕ) : ℝ) =
      ((∑ᶠ ρ ∈ {ρ : ℂ | F₁ ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T},
        analyticOrderNatAt F₁ ρ : ℕ) : ℝ) +
      ((∑ᶠ ρ ∈ {ρ : ℂ | F₂ ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T},
        analyticOrderNatAt F₂ ρ : ℕ) : ℝ) + c := by
  classical
  have hmul := isLSeriesContinuation_mul ha₁ ha₂ hF₁ hF₂ hF
  have hadd : ∀ ρ : ℂ, ρ ≠ 1 →
      analyticOrderNatAt F ρ = analyticOrderNatAt F₁ ρ + analyticOrderNatAt F₂ ρ := by
    intro ρ hρ
    have hn : ({1}ᶜ : Set ℂ) ∈ nhds ρ := isOpen_compl_singleton.mem_nhds hρ
    have hev : F =ᶠ[nhds ρ] F₁ * F₂ := by
      filter_upwards [hn] with s hs
      exact hmul s hs
    have an₁ : AnalyticAt ℂ F₁ ρ := hF₁.2.analyticAt hn
    have an₂ : AnalyticAt ℂ F₂ ρ := hF₂.2.analyticAt hn
    simp only [analyticOrderNatAt]
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul an₁ an₂,
      ENat.toNat_add (analyticOrderAt_ne_top_of_mem ha₁ hF₁ hρ) (analyticOrderAt_ne_top_of_mem ha₂
          hF₂ hρ)]
  refine ⟨(analyticOrderNatAt F 1 : ℝ) - analyticOrderNatAt F₁ 1 - analyticOrderNatAt F₂ 1,
    fun T hT => ?_⟩
  set Z : (ℂ → ℂ) → Set ℂ := fun X => {ρ : ℂ | X ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T}
    with hZ
  have hf : (Z F ∪ Z F₁ ∪ Z F₂).Finite :=
    ((finite_setOf_zeros_of_mem ha hF T).union (finite_setOf_zeros_of_mem ha₁ hF₁ T)).union
        (finite_setOf_zeros_of_mem ha₂ hF₂ T)
  set E := hf.toFinset with hE
  have hsum : ∀ X : ℂ → ℂ, (Z X).Finite → Z X ⊆ Z F ∪ Z F₁ ∪ Z F₂ →
      (∑ᶠ ρ ∈ Z X, analyticOrderNatAt X ρ) = ∑ ρ ∈ E, analyticOrderNatAt X ρ := by
    intro X hX hsub
    rw [finsum_mem_eq_finite_toFinset_sum _ hX]
    refine Finset.sum_subset (fun ρ hρ => ?_) (fun ρ hρE hρX => ?_)
    · rw [Set.Finite.mem_toFinset] at hρ
      rw [hE, Set.Finite.mem_toFinset]; exact hsub hρ
    · rw [hE, Set.Finite.mem_toFinset] at hρE
      rw [Set.Finite.mem_toFinset] at hρX
      have hS : 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T := by
        rcases hρE with (h | h) | h <;> exact h.2
      exact analyticOrderNatAt_eq_zero_of_ne_zero fun h0 => hρX ⟨h0, hS⟩
  have eF := hsum F (finite_setOf_zeros_of_mem ha hF T) (fun ρ h => Or.inl (Or.inl h))
  have e1 := hsum F₁ (finite_setOf_zeros_of_mem ha₁ hF₁ T) (fun ρ h => Or.inl (Or.inr h))
  have e2 := hsum F₂ (finite_setOf_zeros_of_mem ha₂ hF₂ T) (fun ρ h => Or.inr h)
  simp only [hZ] at eF e1 e2
  rw [eF, e1, e2]
  push_cast
  have key : ∑ ρ ∈ E, ((analyticOrderNatAt F ρ : ℝ) - analyticOrderNatAt F₁ ρ -
      analyticOrderNatAt F₂ ρ) =
      (analyticOrderNatAt F 1 : ℝ) - analyticOrderNatAt F₁ 1 - analyticOrderNatAt F₂ 1 := by
    refine Finset.sum_eq_single 1 (fun ρ _ hρ => ?_) (fun h1 => ?_)
    · rw [hadd ρ hρ]; push_cast; ring
    · rw [hE, Set.Finite.mem_toFinset] at h1
      have hS : 0 ≤ (1 : ℂ).re ∧ 0 ≤ (1 : ℂ).im ∧ (1 : ℂ).im ≤ T := by simp [hT]
      rw [analyticOrderNatAt_eq_zero_of_ne_zero (X := F) fun h0 => h1 (Or.inl (Or.inl ⟨h0, hS⟩)),
        analyticOrderNatAt_eq_zero_of_ne_zero (X := F₁) fun h0 => h1 (Or.inl (Or.inr ⟨h0, hS⟩)),
        analyticOrderNatAt_eq_zero_of_ne_zero (X := F₂) fun h0 => h1 (Or.inr ⟨h0, hS⟩)]
      simp
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at key
  linarith

/-- From `N ~ k T log T / 2π`, the error `N - k g` is `o(g)` with `g T = T log T / 2π`. -/
private lemma isLittleO_of_isEquivalent {N : ℝ → ℝ} {k : ℝ}
    (h : Asymptotics.IsEquivalent Filter.atTop N (fun T : ℝ => k * T * Real.log T / (2 * Real.pi)))
        :
    (fun T => N T - k * (T * Real.log T / (2 * Real.pi))) =o[Filter.atTop]
      (fun T : ℝ => T * Real.log T / (2 * Real.pi)) := by
  have e : (fun T : ℝ => k * T * Real.log T / (2 * Real.pi)) =
      fun T => k * (T * Real.log T / (2 * Real.pi)) := by
    funext T; ring
  rw [e] at h
  exact h.isLittleO.trans_isBigO (Asymptotics.isBigO_const_mul_self k _ _)

/-- **The degree is additive.** For `a₁, a₂` in the Selberg class with continuations `F₁`, `F₂`,
and `F` the continuation of `L(a₁ * a₂, s) = F₁ F₂`, every functional equation of `F` has degree
the sum of the degrees of any functional equations of `F₁` and `F₂`. In particular the degree of
a function in the Selberg class does not depend on the choice of functional equation. -/
theorem FunctionalEquation.degree_eq_add_of_mul (a₁ a₂ : ArithmeticFunction ℂ) (ha₁ : a₁ ∈
    selbergClass)
    (ha₂ : a₂ ∈ selbergClass) (F₁ F₂ F : ℂ → ℂ) (hF₁ : IsLSeriesContinuation a₁ F₁)
    (hF₂ : IsLSeriesContinuation a₂ F₂) (hF : IsLSeriesContinuation (a₁ * a₂) F)
    (D₁ : FunctionalEquation F₁) (D₂ : FunctionalEquation F₂) (D : FunctionalEquation F) :
    D.degree = D₁.degree + D₂.degree := by
  have ha := mul_mem ha₁ ha₂
  have l := isLittleO_of_isEquivalent (isEquivalent_zeroCount _ ha F hF D)
  have l₁ := isLittleO_of_isEquivalent (isEquivalent_zeroCount _ ha₁ F₁ hF₁ D₁)
  have l₂ := isLittleO_of_isEquivalent (isEquivalent_zeroCount _ ha₂ F₂ hF₂ D₂)
  obtain ⟨c, hc⟩ := zeroCount_mul ha₁ ha₂ hF₁ hF₂ hF ha
  set g : ℝ → ℝ := fun T => T * Real.log T / (2 * Real.pi) with hg
  have hgt : Filter.Tendsto g Filter.atTop Filter.atTop := by
    refine Filter.Tendsto.atTop_div_const (by positivity) ?_
    exact Filter.tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hc0 : (fun _ : ℝ => c) =o[Filter.atTop] g :=
    Asymptotics.isLittleO_const_left.2 (Or.inr (Filter.tendsto_abs_atTop_atTop.comp hgt))
  have hk : (fun T => (D.degree - D₁.degree - D₂.degree) * g T) =o[Filter.atTop] g := by
    refine ((((l.sub l₁).sub l₂).neg_left).add hc0).congr' ?_ (Filter.EventuallyEq.refl _ _)
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
    have h := hc T hT
    simp only [Set.mem_ofPred_eq] at h
    simp only [hg]
    linear_combination (-1 : ℝ) * h
  by_contra hne
  have hne' : D.degree - D₁.degree - D₂.degree ≠ 0 := fun h => hne (by linarith)
  have hgg := (Asymptotics.isLittleO_const_mul_left_iff hne').1 hk
  refine Asymptotics.isLittleO_irrefl' ?_ hgg
  refine Filter.Eventually.frequently ?_
  filter_upwards [hgt.eventually_ge_atTop 1] with T hT
  rw [Real.norm_eq_abs]
  exact (abs_pos.2 (by linarith : g T ≠ 0)).ne'

end SelbergClass
