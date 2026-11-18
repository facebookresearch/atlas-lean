/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.MirrorDescent
public import MathlibExt.InformationTheory.Pinsker
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The entropy setup of mirror descent on the simplex

The `ℓ₁` setup of mirror descent on the probability simplex `Δₙ ⊂ ℝⁿ` uses the norm `‖·‖₁`
(here the space `PiLp 1`), whose dual norm is `‖·‖_∞`, and the entropy
`ω(x) = ∑ xᵢ log xᵢ` as distance-generating function, with derivative
`ω'(x) = ∑ (log xᵢ + 1) eᵢ*` on the relative interior (all `xᵢ > 0`). Its Bregman divergence is
the Kullback–Leibler divergence, it is `1`-strongly convex with respect to `‖·‖₁` there by
Pinsker's inequality, and its `ω`-diameter from the uniform point is at most `log n`. This makes
the mirror descent rate `L∞ √(2 log n) / √N` depend on the dimension only through `log n`
(A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale
optimization, I: general purpose methods*, in *Optimization for Machine Learning*, MIT Press
(2011), Section 5.7.1, setup 2(c); A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust
stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19 (2009),
Section 2.3, the `ℓ₁`-setup of the Example with (2.58)). Its prox step is the multiplicative-weights
update `x⁺ᵢ ∝ xᵢ exp (-γ gᵢ)` of the Hedge algorithm.

Main results:

* `bregman_entropy_eq`: `V_x(u) = ∑ uᵢ log (uᵢ / xᵢ)` (Kullback–Leibler divergence).
* `bregman_entropy_ge`: `V_x(u) ≥ ‖u - x‖₁² / 2` for `x` in the relative interior and `u` in the
  simplex (Pinsker).
* `bregman_entropy_uniform_le`: `V_{uniform}(u) ≤ log n` on the simplex.
* `norm_le_of_abs_apply_single_le`: the dual norm of a linear form is at most the largest absolute
  value of its coordinates.
* `entropy_prox_multiplicative`: the multiplicative-weights update satisfies the prox optimality
  condition with equality.
* `entropic_mirror_descent_exists_le`: the rate `L √(2 log n) / √N` of entropic mirror descent.
* `multiplicative_weights_regret_le`: the mirror descent regret bound `log n / γ + γ N / 2` for
  experts, against every vertex of the simplex.
-/

@[expose] public section

open Finset Real MathlibExt.Analysis.Convex.MirrorDescent

namespace MathlibExt.Analysis.Convex.MirrorDescentEntropy

variable {n : ℕ}

/-- **The space `ℝⁿ` with the `ℓ₁` norm** `‖x‖ = ∑ |xᵢ|`, whose dual norm is `‖·‖_∞`. -/
abbrev L1 (n : ℕ) : Type := PiLp 1 (fun _ : Fin n => ℝ)

/-- **The entropy distance-generating function** `ω(x) = ∑ xᵢ log xᵢ` (Juditsky and Nemirovski,
*First order methods for nonsmooth convex large-scale optimization, I* (2011), Section 5.7.1,
setup 2(c), equation (5.38)). -/
noncomputable def entropy (x : L1 n) : ℝ := ∑ i, x i * log (x i)

/-- **Derivative of the entropy**, `ω'(x) = ∑ (log xᵢ + 1) eᵢ*`, the gradient of
`∑ xᵢ log xᵢ` at points with all `xᵢ > 0`. -/
noncomputable def entropyDeriv (x : L1 n) : L1 n →L[ℝ] ℝ :=
  ∑ i, (log (x i) + 1) • PiLp.proj 1 (fun _ : Fin n => ℝ) i

/-- **The linear form with coordinates `c`**, `v ↦ ∑ cᵢ vᵢ`. -/
noncomputable def linearForm (c : Fin n → ℝ) : L1 n →L[ℝ] ℝ :=
  ∑ i, c i • PiLp.proj 1 (fun _ : Fin n => ℝ) i

theorem linearForm_apply (c : Fin n → ℝ) (v : L1 n) : linearForm c v = ∑ i, c i * v i := by
  simp [linearForm]

theorem entropyDeriv_apply (x v : L1 n) :
    entropyDeriv x v = ∑ i, (log (x i) + 1) * v i := by
  simp [entropyDeriv]

/-- **The probability simplex** `{x : xᵢ ≥ 0, ∑ xᵢ = 1}`. -/
def simplex (n : ℕ) : Set (L1 n) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- **The relative interior of the simplex**, `{x : xᵢ > 0, ∑ xᵢ = 1}`, where the entropy is
differentiable. -/
def posSimplex (n : ℕ) : Set (L1 n) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i = 1}

theorem posSimplex_subset_simplex : posSimplex n ⊆ simplex n :=
  fun _ hx => ⟨fun i => (hx.1 i).le, hx.2⟩

/-- **The uniform point of the simplex** `(1/n, …, 1/n)`, the minimizer of the entropy on the
simplex. -/
noncomputable def uniform (n : ℕ) : L1 n := WithLp.toLp 1 (fun _ => (n : ℝ)⁻¹)

theorem uniform_apply (i : Fin n) : uniform n i = (n : ℝ)⁻¹ := rfl

theorem uniform_mem_posSimplex (hn : 0 < n) : uniform n ∈ posSimplex n := by
  refine ⟨fun i => by rw [uniform_apply]; positivity, ?_⟩
  simp only [uniform_apply, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **The Bregman divergence of the entropy is the Kullback–Leibler divergence.** For `x` in the
relative interior of the simplex and `u` with `∑ uᵢ = 1`,
`V_x(u) = ∑ uᵢ log (uᵢ / xᵢ)`, with `0 log 0 = 0` (Nemirovski, Juditsky, Lan and Shapiro,
*Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19 (2009),
Section 2.3, Example: the prox-function of the `ℓ₁`-setup is `V(x, z) = ∑ zᵢ ln (zᵢ / xᵢ)`). -/
theorem bregman_entropy_eq {x u : L1 n} (hx : x ∈ posSimplex n) (hu : ∑ i, u i = 1) :
    bregman entropy entropyDeriv x u = ∑ i, u i * log (u i / x i) := by
  have key : ∀ i, u i * log (u i) - x i * log (x i) - (log (x i) + 1) * (u i - x i) =
      u i * log (u i / x i) + (x i - u i) := by
    intro i
    rcases eq_or_ne (u i) 0 with h | h
    · simp [h]; ring
    · rw [log_div h (hx.1 i).ne']; ring
  have : bregman entropy entropyDeriv x u =
      ∑ i, (u i * log (u i) - x i * log (x i) - (log (x i) + 1) * (u i - x i)) := by
    simp only [bregman, entropy, entropyDeriv_apply, PiLp.sub_apply, sum_sub_distrib]
  rw [this, sum_congr rfl fun i _ => key i, sum_add_distrib, sum_sub_distrib, hx.2, hu]
  ring

/-- **Strong convexity of the entropy on the simplex with respect to `‖·‖₁`.** For `x` in the
relative interior of the simplex and `u` in the (closed) simplex, `V_x(u) ≥ ‖u - x‖₁² / 2`, i.e.
the entropy is `1`-strongly convex with respect to the `ℓ₁` norm in the Bregman form
(Nemirovski, Juditsky, Lan and Shapiro (2009), Section 2.3, Example, `α = 1`, proved in their
appendix from the Hessian of the entropy). Here it is derived from Pinsker's inequality
`‖u - x‖₁² ≤ 2 KL(u ‖ x)` with zero entries of `u` allowed. -/
theorem bregman_entropy_ge {x u : L1 n} (hx : x ∈ posSimplex n) (hu : u ∈ simplex n) :
    1 / 2 * ‖u - x‖ ^ 2 ≤ bregman entropy entropyDeriv x u := by
  have hn : n ≠ 0 := by
    rintro rfl
    simpa using hx.2
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  rw [bregman_entropy_eq hx hu.2, PiLp.norm_eq_of_L1]
  have := MathlibExt.InformationTheory.Pinsker.csiszar_kullback_pinsker_of_nonneg (fun i => u i)
    (fun i => x i) hu.1 hx.1 hu.2 hx.2
  simp only [PiLp.sub_apply, Real.norm_eq_abs]
  linarith

/-- **The `ω`-diameter of the simplex under the entropy is at most `log n`.** For every `u` in the
simplex, `V_{uniform}(u) ≤ log n`, where the uniform point minimizes the entropy (Nemirovski,
Juditsky, Lan and Shapiro (2009), Section 2.3, Example: `D_{ω,X} = √(ln n)` and
`x₁ = argmin_X ω = n⁻¹ (1, …, 1)`). -/
theorem bregman_entropy_uniform_le (hn : 0 < n) {u : L1 n} (hu : u ∈ simplex n) :
    bregman entropy entropyDeriv (uniform n) u ≤ log n := by
  rw [bregman_entropy_eq (uniform_mem_posSimplex hn) hu.2]
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hle : ∀ i, u i * log (u i / uniform n i) ≤ u i * log n := by
    intro i
    rw [uniform_apply, div_inv_eq_mul]
    rcases eq_or_lt_of_le (hu.1 i) with h | h
    · simp [← h]
    · apply mul_le_mul_of_nonneg_left _ (hu.1 i)
      apply log_le_log (by positivity)
      have : u i ≤ 1 := by
        rw [← hu.2]
        exact single_le_sum (fun j _ => hu.1 j) (mem_univ i)
      nlinarith
  calc ∑ i, u i * log (u i / uniform n i) ≤ ∑ i, u i * log n := sum_le_sum fun i _ => hle i
    _ = log n := by rw [← sum_mul, hu.2, one_mul]

/-- **Coordinate bound on the dual norm of a linear form on `ℓ₁`.** A linear form `g` on `ℝⁿ`
with the `ℓ₁` norm whose values on the coordinate vectors satisfy `|g(eᵢ)| ≤ L` has dual norm
`‖g‖ ≤ L` (the dual norm of `‖·‖₁` is `‖·‖_∞`, as used in Nemirovski, Juditsky, Lan and Shapiro
(2009), Section 2.3, Example). -/
theorem norm_le_of_abs_apply_single_le (g : L1 n →L[ℝ] ℝ) {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ i, |g (PiLp.single 1 i 1)| ≤ L) : ‖g‖ ≤ L := by
  classical
  refine ContinuousLinearMap.opNorm_le_bound _ hL fun v => ?_
  have hv : v = ∑ i, v i • PiLp.single 1 i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  rw [hv, map_sum, PiLp.norm_eq_of_L1]
  simp only [map_smul, smul_eq_mul, Real.norm_eq_abs]
  calc |∑ i, v i * g (PiLp.single 1 i 1)| ≤ ∑ i, |v i * g (PiLp.single 1 i 1)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, L * |v i| := sum_le_sum fun i _ => by
        rw [abs_mul, mul_comm L]
        exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
    _ = L * ∑ i, |(∑ j, v j • PiLp.single 1 j (1 : ℝ)) i| := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [← hv]

/-- **The prox step of the entropy is the multiplicative-weights update.** Let `x, x⁺` lie in the
relative interior of the simplex with `x⁺ᵢ = xᵢ exp (-γ cᵢ) / Z` for some `Z > 0` (necessarily the
normalizing constant). Then `x⁺` satisfies the optimality condition of the prox step
`x⁺ = argmin_{u ∈ Δₙ} {γ ⟨c, u⟩ + V_x(u)}` with equality:
`(γ c - ω'(x) + ω'(x⁺)) (u - x⁺) = 0` for every `u` with `∑ uᵢ = 1`. This is the optimality
behind the explicit prox-mapping `Prox_x(ξ) = [∑ xᵢ e^{-ξᵢ}]⁻¹ (xᵢ e^{-ξᵢ})ᵢ` on the flat simplex
(Juditsky and Nemirovski (2011), Section 5.7.1, (5.39), for setup 2(c); Nemirovski, Juditsky, Lan
and Shapiro (2009), Section 2.3, Example), and the update of the Hedge algorithm. -/
theorem entropy_prox_multiplicative {x xplus : L1 n} (hx : x ∈ posSimplex n)
    (hxplus : xplus ∈ posSimplex n) {γ Z : ℝ} (hZ : 0 < Z) {c : Fin n → ℝ}
    (hupd : ∀ i, xplus i = x i * exp (-γ * c i) / Z) {u : L1 n} (hu : ∑ i, u i = 1) :
    (γ • linearForm c - entropyDeriv x + entropyDeriv xplus) (u - xplus) = 0 := by
  have hlog : ∀ i, log (xplus i) = log (x i) - γ * c i - log Z := by
    intro i
    rw [hupd i, log_div (by have := hx.1 i; positivity) hZ.ne',
      log_mul (hx.1 i).ne' (exp_pos _).ne', log_exp]
    ring
  simp only [add_apply, sub_apply,
    smul_apply, smul_eq_mul, linearForm_apply, entropyDeriv_apply, hlog,
    PiLp.sub_apply, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  have : ∀ i, γ * (c i * (u i - xplus i)) - (log (x i) + 1) * (u i - xplus i) +
      (log (x i) - γ * c i - log Z + 1) * (u i - xplus i) = -log Z * (u i - xplus i) := by
    intro i; ring
  rw [sum_congr rfl fun i _ => this i, ← mul_sum, sum_sub_distrib, hu, hxplus.2]
  ring

/-- **Rate of entropic mirror descent on the simplex.** Let `n ≥ 2`, `L > 0`, `N ≥ 1`, and run
mirror descent with the entropy setup on the simplex `Δₙ` from the uniform point, with the
constant step `γ = √(2 log n) / (L √N)`: the iterates `x t` lie in the relative interior `Δ°ₙ`
and satisfy the prox optimality conditions for all `u ∈ Δₙ` (for instance, by
`entropy_prox_multiplicative`, the multiplicative-weights updates), and `g t` is a subgradient of
`f` at `x t` relative to `Δₙ` with dual norm `‖g t‖ ≤ L` (for instance all `|g_t(eᵢ)| ≤ L`, by
`norm_le_of_abs_apply_single_le`). Then for every `xstar ∈ Δₙ` some iterate `t < N` satisfies
`f (x t) - f xstar ≤ L √(2 log n) / √N`.
This is the efficiency estimate (5.11) of Juditsky and Nemirovski, *First order methods for
nonsmooth convex large-scale optimization, I* (2011), Proposition 5.1(ii), in the entropy setup
2(c) of Section 5.7.1, with `Ω ≤ ln n` (Nemirovski, Juditsky, Lan and Shapiro (2009), Section 2.3,
Example), for the best iterate. -/
theorem entropic_mirror_descent_exists_le (hn : 2 ≤ n) {f : L1 n → ℝ} {L : ℝ} (hL : 0 < L)
    {x : ℕ → L1 n} {g : ℕ → L1 n →L[ℝ] ℝ} {N : ℕ} (hN : 0 < N) (hx0 : x 0 = uniform n)
    (hx : ∀ t, x t ∈ posSimplex n)
    (hstep : ∀ t, ∀ u ∈ simplex n,
      0 ≤ ((√(2 * log n) / (L * √N)) • g t - entropyDeriv (x t) + entropyDeriv (x (t + 1)))
        (u - x (t + 1)))
    (hsub : ∀ t, ∀ y ∈ simplex n, f (x t) + g t (y - x t) ≤ f y) (hg : ∀ t, ‖g t‖ ≤ L)
    {xstar : L1 n} (hxstar : xstar ∈ simplex n) :
    ∃ t < N, f (x t) - f xstar ≤ L * √(2 * log n) / √N := by
  have hn0 : 0 < n := by omega
  have hlog : 0 < log n := log_pos (by exact_mod_cast hn)
  have hV : bregman entropy entropyDeriv (x 0) xstar ≤ log n := by
    rw [hx0]; exact bregman_entropy_uniform_le hn0 hxstar
  have := mirror_descent_exists_le_sqrt entropy entropyDeriv one_pos posSimplex_subset_simplex
    (fun x hx u hu => bregman_entropy_ge hx hu) hL hlog hN hx (by simpa only [mul_one] using hstep)
    hsub hg hxstar hV
  simpa only [one_mul] using this

/-- **Regret of entropic mirror descent for prediction with expert advice.** Let `n ≥ 1`,
`γ > 0`, and let the loss vectors `c t ∈ [-1, 1]ⁿ` be arbitrary. Run the multiplicative-weights
update from the uniform point: `x (t + 1) i = x t i exp (-γ c t i) / Z t` with `Z t > 0` and
`x t` in the relative interior of the simplex. Then for every expert `i` and every `N`,
`∑_{t<N} (⟨c t, x t⟩ - c t i) ≤ log n / γ + γ N / 2`.
This is the telescoped mirror descent bound (5.7) of Juditsky and Nemirovski (2011),
Proposition 5.1(i), in the entropy setup 2(c) of Section 5.7.1, with the comparator `u = eᵢ` (a
vertex of the simplex), `V_{uniform}(eᵢ) ≤ log n` and `‖c t‖_∞ ≤ 1`; the update is the entropic prox
step by `entropy_prox_multiplicative`. It is the mirror descent regret bound, not the Hedge bound
`L - L_i ≤ η T + log n / η` that `CSLibExt.MachineLearning.Hedge.regret_le` proves by the potential
argument for losses in `[0, 1]`. -/
theorem multiplicative_weights_regret_le (hn : 0 < n) {γ : ℝ} (hγ : 0 < γ)
    {c : ℕ → Fin n → ℝ} {x : ℕ → L1 n} {Z : ℕ → ℝ} (hx0 : x 0 = uniform n)
    (hx : ∀ t, x t ∈ posSimplex n) (hZ : ∀ t, 0 < Z t)
    (hupd : ∀ t i, x (t + 1) i = x t i * exp (-γ * c t i) / Z t) (hc : ∀ t i, |c t i| ≤ 1)
    (i : Fin n) (N : ℕ) :
    ∑ t ∈ range N, (∑ j, c t j * x t j - c t i) ≤ log n / γ + γ * N / 2 := by
  classical
  set e : L1 n := WithLp.toLp 1 (Pi.single i (1 : ℝ) : Fin n → ℝ) with he
  have he_apply : ∀ j, e j = (Pi.single i (1 : ℝ) : Fin n → ℝ) j := fun j => by rw [he]
  have heS : e ∈ simplex n := by
    refine ⟨fun j => ?_, ?_⟩
    · rw [he_apply]; by_cases h : j = i
      · subst h; simp
      · simp [h]
    · simp only [he_apply]; simp
  have hsum := mirror_descent_sum_le entropy entropyDeriv one_pos posSimplex_subset_simplex
    (fun x hx u hu => bregman_entropy_ge hx hu) (x := x) (g := fun t => linearForm (c t))
    (γ := fun _ => γ) hx
    (fun t u hu => (entropy_prox_multiplicative (hx t) (hx (t + 1)) (hZ t) (hupd t) hu.2).ge)
    heS N
  have hV : bregman entropy entropyDeriv (x 0) e ≤ log n := by
    rw [hx0]; exact bregman_entropy_uniform_le hn heS
  have hnorm : ∀ t, ‖linearForm (c t)‖ ≤ 1 := fun t =>
    norm_le_of_abs_apply_single_le _ zero_le_one fun j => by
      rw [linearForm_apply]
      simpa [PiLp.single_apply] using hc t j
  have hlin : ∀ t, linearForm (c t) (x t - e) = ∑ j, c t j * x t j - c t i := by
    intro t
    rw [linearForm_apply]
    simp only [PiLp.sub_apply, he_apply, mul_sub, sum_sub_distrib]
    simp [Pi.single_apply]
  have hsq : ∑ t ∈ range N, γ ^ 2 * ‖linearForm (c t)‖ ^ 2 ≤ γ ^ 2 * N := by
    calc ∑ t ∈ range N, γ ^ 2 * ‖linearForm (c t)‖ ^ 2 ≤ ∑ _t ∈ range N, γ ^ 2 * 1 := by
          refine sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg γ)
          have := hnorm t
          nlinarith [norm_nonneg (linearForm (c t))]
      _ = γ ^ 2 * N := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  simp only [hlin] at hsum
  rw [← mul_sum] at hsum
  rw [div_add' _ _ _ hγ.ne', le_div_iff₀ hγ]
  nlinarith [hsum, hV, hsq]

end MathlibExt.Analysis.Convex.MirrorDescentEntropy
