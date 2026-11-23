/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous
public import MathlibExt.Probability.Statistics.GillJohansenOuter
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Continuous-time product-integral differentiability and the functional delta theorem

T44 (`MathlibExt.Probability.Statistics.FunctionalDelta`) proves the functional delta theorem and
the differentiability of the product integral on a **fixed grid** only. T78
(`MathlibExt.Probability.Statistics.ContinuousProductIntegral`) and
`MathlibExt.Probability.Statistics.GillJohansenOuter` treat continuous time, but with the product
integral and its Duhamel operator as a **hypothesis bundle** (`IsStieltjesProductIntegral`): the
Lebesgue–Stieltjes construction of T77 (`MathlibExt.Analysis.StieltjesProductIntegral`) was never
connected to them. This file makes that connection for the end-point value. With no assumed
product integral, it proves that the **concrete** T77 map

`x ↦ ∏_{(0, τ]} (1 + dx)`, `ℓ^∞([0, τ]) → ℝ`

is Hadamard differentiable, and derives the continuous-time functional delta theorem for it.

## Main definitions

* `toFun x`: the path `t ↦ x t` of `x ∈ ℓ^∞([0, τ])`, extended by `0` outside `[0, τ]`.
* `tvBall τ M`: the paths with a monotone control of total increase `≤ M` on `[0, τ]`
  (total variation `≤ M`); `bvPaths τ`: the paths of bounded variation.
* `prodIntegralEnd x = productIntegral (toFun x) 0 τ`: T77's product integral of the path.
* `duhamelDerivFun A a b h`: the limit along refinement of the two-tag sums
  `∑ P(A)(a, u] (h x - h u) P(A)(x, b]` (left tag `u`, right tag `x` on each cell `(u, x]`),
  i.e. the Duhamel integral `∫_{(a, b]} P(A)(a, s) dh(s) P(A)(s, b]` of Gill–Johansen (1990);
  `duhamelDeriv θ h` is its value on paths.

## Main results

* `isControl_productIntegral_left`, `isControl_productIntegral_right`: the factors
  `u ↦ P(A)(a, u]` and `x ↦ P(A)(x, b]` have bounded variation, with explicit controls.
* `abs_productIntegral_sub_le`: **Lipschitz dependence on the integrator in the sup norm** on a
  total-variation ball, `|P(B) - P(A)| ≤ ‖B - A‖_∞ · 6 e^{2M}`.
* `tendsto_duhamelDerivFun`: the Duhamel integral **exists** for every integrator that is a
  uniform limit of functions of bounded variation (every continuous function, by Weierstrass;
  classically every regulated, in particular every càdlàg, function, which is not proved here).
* `hasHadamardDerivWithinAt_prodIntegralEnd`: **Hadamard differentiability of the continuous-time
  product integral** at every `θ` in a total-variation ball `D`, on the domain `D`, tangentially
  to the uniform closure of the bounded-variation paths, with the Duhamel derivative
  `duhamelDeriv θ`. `continuous_mem_closure_bvPaths` puts `C[0, τ]` in the tangent set.
* `hasHadamardDerivWithinAt_survivalEnd`: the same for the survival map
  `Λ ↦ ∏_{(0, τ]} (1 - dΛ)`.
* `tendstoInDistributionOuter_prodIntegralEnd`, `tendstoInDistributionOuter_survivalEnd`: the
  **functional delta theorem in continuous time**, in the outer-probability framework of
  `GillJohansenOuter` and with no measurability hypothesis on the processes: if
  `rₙ (Xₙ - θ) ⇝ L` in `ℓ^∞([0, τ])`, with `L` carried by the tangent set and
  `P*(Xₙ ∉ D) → 0`, then `rₙ (P(Xₙ) - P(θ)) ⇝ L ∘ (duhamelDeriv θ)⁻¹`. The outer framework is
  needed because `ℓ^∞([0, τ])` is not separable: Borel measurability of the estimator processes
  fails on the canonical space of the observations for every failure-time law with a non-atomic
  part (see the module docstrings of `GillJohansenOuter` and of T44's `FunctionalDelta`), so
  Mathlib's Borel `TendstoInDistribution` would make the theorem vacuous there.

## Scope

* The output is the end-point value `∏_{(0, τ]}`, a real number. Any `t ∈ (0, τ]` is covered by
  taking `τ := t` (restriction `ℓ^∞([0, τ]) → ℓ^∞([0, t])` is a continuous linear map, so a
  process-level CLT transfers). Hadamard differentiability as a map into `ℓ^∞([0, τ])`, uniformly
  in the end point, is not proved.
* The Duhamel derivative is not a continuous linear map on all of `ℓ^∞([0, τ])` (the two-tag sums
  need not converge for a non-regulated direction), which is why T78's `IsStieltjesProductIntegral`
  is **not** instantiated here. On the tangent set it is Lipschitz (`abs_duhamelDeriv_sub_le`).
* The identification of the Kaplan–Meier estimator with T77's product integral of the negated
  Nelson–Aalen path (pure-jump integrators with several jumps) is not proved, so the Kaplan–Meier
  corollary of `GillJohansenOuter` is not re-derived for the concrete map; the Nelson–Aalen
  functional CLT remains a hypothesis (`hXL`).
* The derivative is T44's one-sided directional `HasHadamardDerivWithinAt` (implied by the usual
  two-sided notion).

## Proof outline

T77's `tendsto_duhamelSum` gives `P(θ + t k) - P(θ) = t · lim T(F_θ, G_{θ + t k}; k)`, where
`T(F, G; h)` is the two-tag sum, `F_θ = P(θ)(0, ·]` and `G_B = P(B)(·, τ]`. Then
`T(F_θ, G_B; k) - T(F_θ, G_θ; h) = T(F_θ, G_B; k - h) + T(F_θ, G_B - G_θ; h - g) +
T(F_θ, G_B - G_θ; g)` for any `g` of bounded variation. The first two terms are bounded through
the uniform-norm bound `abs_twoTagSum_le_of_abs_le` of `StieltjesRSIntegralLeftContinuous` by
`‖k - h‖` and `‖h - g‖`; the third by `‖G_B - G_θ‖_∞ · V(g) = O(t)` (Lipschitz dependence). The
same decomposition with `B = θ + t g` shows that the two-tag sums for `h` are a Cauchy net.

## Source receipt (reuse search, 2026-11-14)

Mathlib v4.35.0 has no product integral and no Hadamard derivative. Reused: T77's
`productIntegral`, `IsControl`, `productIntegral_mul`, `abs_productIntegral_sub_one_add_le`,
`abs_productIntegral_le_exp`, `tendsto_duhamelSum`; `StieltjesRSIntegralLeftContinuous`'s
`twoTagSum`, `duhamelSum_eq_twoTagSum`, `abs_twoTagSum_le_of_abs_le`, `abs_sum_cells_mul_le`,
`abs_le_of_isControl`, `boundedVariationOn_polynomial_eval`; T44's `HasHadamardDerivWithinAt`;
`GillJohansenOuter.TendstoInDistributionOuter.functional_delta`; Mathlib's
`exists_polynomial_near_of_continuousOn` (Weierstrass) and `ContinuousOn.measurable_piecewise`.
Proved here: the factor controls, the Lipschitz bound, existence of the Duhamel integral for
regulated integrators, the Hadamard derivative and the delta-theorem corollaries.

## References

* R. D. Gill and S. Johansen, *A survey of product-integration with a view toward application in
  survival analysis*, Ann. Statist. 18 (1990), 1501–1555.
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Theorem 20.8, §20.3.
* A. W. van der Vaart and J. A. Wellner, *Weak Convergence and Empirical Processes* (1996),
  §3.9.4.
-/

@[expose] public section

open Filter Topology Finset MeasureTheory
open scoped ENNReal

namespace MathlibExt.Probability.Statistics.FunctionalDeltaContinuous

open MathlibExt.Analysis.StieltjesProductIntegral
open MathlibExt.Analysis.StieltjesRSIntegralLeftContinuous
open MathlibExt.Probability.Statistics.GillJohansenOuter

/-! ### Controls -/

section Controls

variable {A B V W : ℝ → ℝ} {a b : ℝ}

/-- The sum of two controlled functions is controlled by the sum of the controls. -/
theorem isControl_add (hA : IsControl A V a b) (hB : IsControl B W a b) :
    IsControl (fun x => A x + B x) (fun x => V x + W x) a b := fun x y hy hyx hx => by
  have h1 := hA x y hy hyx hx
  have h2 := hB x y hy hyx hx
  change |A x + B x - (A y + B y)| ≤ V x + W x - (V y + W y)
  rw [show A x + B x - (A y + B y) = (A x - A y) + (B x - B y) by ring]
  exact (abs_add_le _ _).trans (by linarith)

/-- The difference of two controlled functions is controlled by the sum of the controls. -/
theorem isControl_sub (hA : IsControl A V a b) (hB : IsControl B W a b) :
    IsControl (fun x => A x - B x) (fun x => V x + W x) a b := fun x y hy hyx hx => by
  have h1 := hA x y hy hyx hx
  have h2 := hB x y hy hyx hx
  change |A x - B x - (A y - B y)| ≤ V x + W x - (V y + W y)
  rw [show A x - B x - (A y - B y) = (A x - A y) - (B x - B y) by ring]
  exact (abs_sub _ _).trans (by linarith)

/-- A nonnegative multiple of a controlled function is controlled by the multiple of the
control. -/
theorem IsControl.const_mul {c : ℝ} (hc0 : 0 ≤ c) (hA : IsControl A V a b) :
    IsControl (fun x => c * A x) (fun x => c * V x) a b := fun x y hy hyx hx => by
  change |c * A x - c * A y| ≤ c * V x - c * V y
  rw [show c * A x - c * A y = c * (A x - A y) by ring, abs_mul, abs_of_nonneg hc0,
    show c * V x - c * V y = c * (V x - V y) by ring]
  exact mul_le_mul_of_nonneg_left (hA x y hy hyx hx) hc0

/-- A control only depends on the values on `[a, b]`. -/
theorem IsControl.congr (hA : IsControl A V a b) (h : ∀ x ∈ Set.Icc a b, A x = B x) :
    IsControl B V a b := fun x y hy hyx hx => by
  rw [← h x ⟨hy.trans hyx, hx⟩, ← h y ⟨hy, hyx.trans hx⟩]
  exact hA x y hy hyx hx

end Controls

/-! ### The two factors of the Duhamel kernel -/

section Factors

variable {A B V W : ℝ → ℝ} {a b : ℝ}

/-- **One-cell bound**: `|∏_{(y, x]} (1 + dA) - 1| ≤ exp (V x - V y) - 1`. -/
theorem abs_productIntegral_sub_one_le (hc : IsControl A V a b) {x y : ℝ} (hy : a ≤ y)
    (hyx : y ≤ x) (hx : x ≤ b) :
    |productIntegral A y x - 1| ≤ Real.exp (V x - V y) - 1 := by
  have hc' := hc.mono hy hx
  have h1 := abs_productIntegral_sub_one_add_le hyx hc'
  have h2 := productIntegral_le_exp hyx hc'
  have h3 := hc x y hy hyx hx
  have h4 := abs_add_le (productIntegral A y x - (1 + (A x - A y))) (A x - A y)
  rw [show productIntegral A y x - (1 + (A x - A y)) + (A x - A y) =
    productIntegral A y x - 1 by ring] at h4
  linarith

theorem abs_productIntegral_le_exp_of_le (hc : IsControl A V a b) {x y : ℝ} (hy : a ≤ y)
    (hyx : y ≤ x) (hx : x ≤ b) : |productIntegral A y x| ≤ Real.exp (V x - V y) :=
  abs_productIntegral_le_exp hyx (hc.mono hy hx)

/-- The forward factor `u ↦ ∏_{(a, u]} (1 + dA)` is bounded by `exp (V b - V a)` on `[a, b]`. -/
theorem abs_productIntegral_left_le (hc : IsControl A V a b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |productIntegral A a x| ≤ Real.exp (V b - V a) :=
  (abs_productIntegral_le_exp_of_le hc le_rfl hx.1 hx.2).trans
    (Real.exp_le_exp.2 (by linarith [hc.sub_nonneg hx.1 hx.2 le_rfl]))

/-- The backward factor `x ↦ ∏_{(x, b]} (1 + dA)` is bounded by `exp (V b - V a)` on `[a, b]`. -/
theorem abs_productIntegral_right_le (hc : IsControl A V a b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |productIntegral A x b| ≤ Real.exp (V b - V a) :=
  (abs_productIntegral_le_exp_of_le hc hx.1 hx.2 le_rfl).trans
    (Real.exp_le_exp.2 (by linarith [hc.sub_nonneg le_rfl hx.1 hx.2]))

/-- **The forward factor has bounded variation**: `u ↦ ∏_{(a, u]} (1 + dA)` is controlled by
`x ↦ exp (V x - V a)` on `[a, b]`. -/
theorem isControl_productIntegral_left (hc : IsControl A V a b) :
    IsControl (productIntegral A a) (fun x => Real.exp (V x - V a)) a b := by
  intro x y hy hyx hx
  have hmul : productIntegral A a x = productIntegral A a y * productIntegral A y x :=
    productIntegral_mul hy hyx (hc.mono le_rfl hx)
  have hF := abs_productIntegral_le_exp_of_le hc le_rfl hy (hyx.trans hx)
  have hP := abs_productIntegral_sub_one_le hc hy hyx hx
  change |productIntegral A a x - productIntegral A a y| ≤
    Real.exp (V x - V a) - Real.exp (V y - V a)
  rw [hmul, show productIntegral A a y * productIntegral A y x - productIntegral A a y =
    productIntegral A a y * (productIntegral A y x - 1) by ring, abs_mul]
  calc |productIntegral A a y| * |productIntegral A y x - 1|
      ≤ Real.exp (V y - V a) * (Real.exp (V x - V y) - 1) :=
        mul_le_mul hF hP (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (V x - V a) - Real.exp (V y - V a) := by
        rw [mul_sub, mul_one, ← Real.exp_add, show V y - V a + (V x - V y) = V x - V a by ring]

/-- **The backward factor has bounded variation**: `x ↦ ∏_{(x, b]} (1 + dA)` is controlled by
`x ↦ -exp (V b - V x)` on `[a, b]`. -/
theorem isControl_productIntegral_right (hc : IsControl A V a b) :
    IsControl (fun x => productIntegral A x b) (fun x => -Real.exp (V b - V x)) a b := by
  intro x y hy hyx hx
  have hmul : productIntegral A y b = productIntegral A y x * productIntegral A x b :=
    productIntegral_mul hyx hx (hc.mono hy le_rfl)
  have hG := abs_productIntegral_le_exp_of_le hc (hy.trans hyx) hx le_rfl
  have hP := abs_productIntegral_sub_one_le hc hy hyx hx
  change |productIntegral A x b - productIntegral A y b| ≤
    -Real.exp (V b - V x) - -Real.exp (V b - V y)
  rw [hmul, show productIntegral A x b - productIntegral A y x * productIntegral A x b =
    -(productIntegral A x b * (productIntegral A y x - 1)) by ring, abs_neg, abs_mul]
  calc |productIntegral A x b| * |productIntegral A y x - 1|
      ≤ Real.exp (V b - V x) * (Real.exp (V x - V y) - 1) :=
        mul_le_mul hG hP (abs_nonneg _) (Real.exp_pos _).le
    _ = -Real.exp (V b - V x) - -Real.exp (V b - V y) := by
        rw [mul_sub, mul_one, ← Real.exp_add, show V b - V x + (V x - V y) = V b - V y by ring]
        ring

end Factors

/-! ### Two-tag sum estimates -/

section TwoTag

variable {A B V W : ℝ → ℝ} {a b : ℝ}

theorem twoTagSum_const_mul (F G h : ℝ → ℝ) (c : ℝ) (P : Finset ℝ) :
    twoTagSum F G (fun x => c * h x) P = c * twoTagSum F G h P := by
  simp only [twoTagSum, mul_sum]
  exact sum_congr rfl fun x _ => by ring

/-- A two-tag sum with bounded weights `|F| ≤ M₁`, `|G| ≤ ε` against a controlled integrator is
at most `M₁ ε (U b - U a)`. -/
theorem abs_twoTagSum_le_of_isControl (hab : a ≤ b) {F G g U : ℝ → ℝ} (hg : IsControl g U a b)
    {M₁ ε : ℝ} (hF : ∀ x ∈ Set.Icc a b, |F x| ≤ M₁) (hG : ∀ x ∈ Set.Icc a b, |G x| ≤ ε)
    (s : Finset ℝ) :
    |twoTagSum F G g (partitionPts a b s)| ≤ M₁ * ε * (U b - U a) := by
  have key := abs_sum_cells_mul_le hab hg (fun x => F (prev (partitionPts a b s) x) * G x) s
    (M := M₁ * ε) fun x hx => by
      have hu := mem_Icc_of_mem_partitionPts hab (prev_mem hx)
      have hxI := mem_Icc_of_mem_partitionPts hab hx
      change |F (prev (partitionPts a b s) x) * G x| ≤ M₁ * ε
      rw [abs_mul]
      exact mul_le_mul (hF _ hu) (hG x hxI) (abs_nonneg _) ((abs_nonneg _).trans (hF _ hu))
  have e : twoTagSum F G g (partitionPts a b s) = ∑ x ∈ partitionPts a b s,
      (F (prev (partitionPts a b s) x) * G x) * (g x - g (prev (partitionPts a b s) x)) := by
    rw [twoTagSum]
    exact sum_congr rfl fun x _ => by ring
  rw [e]
  exact key

/-- **Uniform bound for the Duhamel kernel.** For integrators `A`, `B` with controls of total
increase `≤ M` on `[a, b]` and `|h| ≤ δ` there, every two-tag sum
`∑ P(A)(a, u] Δh P(B)(x, b]` is at most `δ · 6 e^{2M}`. -/
theorem abs_twoTagSum_productIntegral_le (hab : a ≤ b) (hA : IsControl A V a b)
    (hB : IsControl B W a b) {M : ℝ} (hV : V b - V a ≤ M) (hW : W b - W a ≤ M)
    {h : ℝ → ℝ} {δ : ℝ} (hh : ∀ x ∈ Set.Icc a b, |h x| ≤ δ) (s : Finset ℝ) :
    |twoTagSum (productIntegral A a) (fun x => productIntegral B x b) h (partitionPts a b s)|
      ≤ δ * (6 * Real.exp M ^ 2) := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hh a ⟨le_rfl, hab⟩)
  have hA1 : 1 ≤ Real.exp (V b - V a) := Real.one_le_exp (hA.sub_nonneg le_rfl hab le_rfl)
  have hB1 : 1 ≤ Real.exp (W b - W a) := Real.one_le_exp (hB.sub_nonneg le_rfl hab le_rfl)
  have hAM : Real.exp (V b - V a) ≤ Real.exp M := Real.exp_le_exp.2 hV
  have hBM : Real.exp (W b - W a) ≤ Real.exp M := Real.exp_le_exp.2 hW
  have hp := mul_le_mul hAM hBM (by linarith) (Real.exp_pos M).le
  refine (abs_twoTagSum_le_of_abs_le hab hh (fun x hx => abs_productIntegral_left_le hA hx)
    (fun x hx => abs_productIntegral_right_le hB hx) (isControl_productIntegral_left hA)
    (isControl_productIntegral_right hB) s).trans (mul_le_mul_of_nonneg_left ?_ hδ)
  simp only [sub_self, Real.exp_zero]
  nlinarith

/-- **Lipschitz dependence of the product integral on the integrator in the sup norm.** For
integrators with controls of total increase `≤ M` on `[a, b]`,
`|∏_{(a, b]} (1 + dB) - ∏_{(a, b]} (1 + dA)| ≤ sup_{[a, b]} |B - A| · 6 e^{2M}`. -/
theorem abs_productIntegral_sub_le (hab : a ≤ b) (hA : IsControl A V a b)
    (hB : IsControl B W a b) {M : ℝ} (hV : V b - V a ≤ M) (hW : W b - W a ≤ M) {δ : ℝ}
    (hδ : ∀ x ∈ Set.Icc a b, |B x - A x| ≤ δ) :
    |productIntegral B a b - productIntegral A a b| ≤ δ * (6 * Real.exp M ^ 2) := by
  refine le_of_tendsto (tendsto_duhamelSum hab hA hB).abs (Eventually.of_forall fun s => ?_)
  rw [duhamelSum_eq_twoTagSum]
  exact abs_twoTagSum_productIntegral_le hab hA hB hV hW (h := B - A) (fun x hx => hδ x hx) s

/-- The backward factors of two integrators are uniformly close when the integrators are. -/
theorem abs_productIntegral_right_sub_le (hA : IsControl A V a b) (hB : IsControl B W a b)
    {M : ℝ} (hV : V b - V a ≤ M) (hW : W b - W a ≤ M) {δ : ℝ}
    (hδ : ∀ x ∈ Set.Icc a b, |B x - A x| ≤ δ) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    |productIntegral B x b - productIntegral A x b| ≤ δ * (6 * Real.exp M ^ 2) :=
  abs_productIntegral_sub_le hx.2 (hA.mono hx.1 le_rfl) (hB.mono hx.1 le_rfl)
    (by linarith [hA.sub_nonneg le_rfl hx.1 hx.2]) (by linarith [hB.sub_nonneg le_rfl hx.1 hx.2])
    fun y hy => hδ y ⟨hx.1.trans hy.1, hy.2⟩

/-- The Duhamel sums of `A` and `A + t k` are `t` times the two-tag sums against `k`, so the
two-tag sums converge to the difference quotient `t⁻¹ (P(A + t k) - P(A))`. -/
theorem tendsto_twoTagSum_smul (hab : a ≤ b) (hA : IsControl A V a b) {k : ℝ → ℝ} {t : ℝ}
    (ht : t ≠ 0) (hB : IsControl (fun x => A x + t * k x) W a b) :
    Tendsto (fun s : Finset ℝ => twoTagSum (productIntegral A a)
      (fun x => productIntegral (fun y => A y + t * k y) x b) k (partitionPts a b s)) atTop
      (𝓝 (t⁻¹ * (productIntegral (fun x => A x + t * k x) a b - productIntegral A a b))) := by
  refine ((tendsto_duhamelSum hab hA hB).const_mul t⁻¹).congr fun s => ?_
  rw [duhamelSum_eq_twoTagSum]
  have e : (fun x => A x + t * k x) - A = fun x => t * k x := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [e, twoTagSum_const_mul, ← mul_assoc, inv_mul_cancel₀ ht, one_mul]

/-- A net of reals that is a uniform limit of Cauchy nets converges. -/
theorem tendsto_limUnder_of_uniform_approx {u : Finset ℝ → ℝ}
    (h : ∀ ε > 0, ∃ v : Finset ℝ → ℝ, CauchySeq v ∧ ∀ s, |u s - v s| ≤ ε) :
    Tendsto u atTop (𝓝 (limUnder atTop u)) := by
  refine tendsto_nhds_limUnder
    (cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_))
  obtain ⟨v, hv, huv⟩ := h (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hv (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm n hn => ?_⟩
  have e3 := hN m hm n hn
  rw [Real.dist_eq] at e3 ⊢
  have t1 := huv m
  have t2 := huv n
  have t3 := abs_sub_le (u m) (v m) (u n)
  have t4 := abs_sub_le (v m) (v n) (u n)
  rw [abs_sub_comm (v n)] at t4
  linarith

end TwoTag

/-! ### The Duhamel derivative -/

section Duhamel

variable {A V : ℝ → ℝ} {a b : ℝ}

/-- The **Duhamel integral** `∫_{(a, b]} P(A)(a, s) dh(s) P(A)(s, b]`: the limit along refinement
of the two-tag sums `∑ P(A)(a, u] (h x - h u) P(A)(x, b]` over the cells `(u, x]` of the
partitions of `[a, b]`, defined through `limUnder`, so its value is unspecified (a
`Classical.epsilon` choice) when the net does not converge. The net converges for every `h` that
is a uniform limit of functions of bounded variation (`tendsto_duhamelDerivFun`). -/
noncomputable def duhamelDerivFun (A : ℝ → ℝ) (a b : ℝ) (h : ℝ → ℝ) : ℝ :=
  limUnder atTop fun s : Finset ℝ =>
    twoTagSum (productIntegral A a) (fun x => productIntegral A x b) h (partitionPts a b s)

/-- `ε / (4 (c + 1)) · c ≤ ε / 4` for `c ≥ 0`. -/
theorem div_four_mul_le {ε c : ℝ} (hε : 0 < ε) (hc : 0 ≤ c) : ε / (4 * (c + 1)) * c ≤ ε / 4 := by
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Existence of the Duhamel integral** for every integrator `h` that is a uniform limit on
`[a, b]` of functions of bounded variation (for instance every continuous `h`; classically every
regulated `h`), when `A` has bounded variation. -/
theorem tendsto_duhamelDerivFun (hab : a ≤ b) (hA : IsControl A V a b) {h : ℝ → ℝ}
    (happrox : ∀ ε > 0, ∃ g U : ℝ → ℝ, IsControl g U a b ∧ ∀ x ∈ Set.Icc a b, |h x - g x| ≤ ε) :
    Tendsto (fun s : Finset ℝ => twoTagSum (productIntegral A a)
      (fun x => productIntegral A x b) h (partitionPts a b s)) atTop
      (𝓝 (duhamelDerivFun A a b h)) := by
  refine tendsto_limUnder_of_uniform_approx fun ε hε => ?_
  set M := V b - V a with hMdef
  have hM0 : 0 ≤ M := hA.sub_nonneg le_rfl hab le_rfl
  set K := 6 * Real.exp M ^ 2 with hKdef
  have hK : 0 ≤ K := by positivity
  obtain ⟨g, U, hg, hhg⟩ := happrox (ε / (4 * (K + 1))) (by positivity)
  set CU := U b - U a with hCUdef
  have hCU : 0 ≤ CU := hg.sub_nonneg le_rfl hab le_rfl
  set Bg := |g a| + CU with hBgdef
  have hBg : ∀ x ∈ Set.Icc a b, |g x| ≤ Bg := fun x hx => abs_le_of_isControl hg hx
  have hBg0 : 0 ≤ Bg := by positivity
  set M' := M + CU with hM'def
  set C₂ := Real.exp M' * (Bg * (6 * Real.exp M' ^ 2)) * CU with hC₂def
  have hC₂ : 0 ≤ C₂ := by positivity
  set t := min 1 (ε / (4 * (C₂ + 1))) with htdef
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htC : t * C₂ ≤ ε / 4 :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hC₂).trans (div_four_mul_le hε hC₂)
  have hBt : IsControl (fun x => A x + t * g x) (fun x => V x + t * U x) a b :=
    isControl_add hA (IsControl.const_mul ht0.le hg)
  have hVM' : V b - V a ≤ M' := by linarith
  have hWM' : (V b + t * U b) - (V a + t * U a) ≤ M' := by nlinarith
  refine ⟨fun s => twoTagSum (productIntegral A a)
    (fun x => productIntegral (fun y => A y + t * g y) x b) g (partitionPts a b s),
    (tendsto_twoTagSum_smul hab hA ht0.ne' hBt).cauchySeq, fun s => ?_⟩
  -- decomposition
  have hdec : twoTagSum (productIntegral A a) (fun x => productIntegral A x b) h
        (partitionPts a b s) -
      twoTagSum (productIntegral A a) (fun x => productIntegral (fun y => A y + t * g y) x b) g
        (partitionPts a b s) =
      twoTagSum (productIntegral A a) (fun x => productIntegral A x b) (fun x => h x - g x)
        (partitionPts a b s) +
      twoTagSum (productIntegral A a)
        (fun x => productIntegral A x b - productIntegral (fun y => A y + t * g y) x b) g
        (partitionPts a b s) := by
    simp only [twoTagSum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => by ring
  have X1 := abs_twoTagSum_productIntegral_le hab hA hA le_rfl le_rfl
    (h := fun x => h x - g x) hhg s
  have hGd : ∀ x ∈ Set.Icc a b, |productIntegral A x b -
      productIntegral (fun y => A y + t * g y) x b| ≤ (t * Bg) * (6 * Real.exp M' ^ 2) := by
    intro x hx
    rw [abs_sub_comm]
    refine abs_productIntegral_right_sub_le hA hBt hVM' hWM' (fun y hy => ?_) hx
    rw [show A y + t * g y - A y = t * g y by ring, abs_mul, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left (hBg y hy) ht0.le
  have X2 := abs_twoTagSum_le_of_isControl hab hg (M₁ := Real.exp M')
    (fun x hx => (abs_productIntegral_left_le hA hx).trans (Real.exp_le_exp.2 hVM')) hGd s
  rw [hdec]
  refine (abs_add_le _ _).trans ?_
  have hX1 : ε / (4 * (K + 1)) * K ≤ ε / 4 := div_four_mul_le hε hK
  have e2 : Real.exp M' * (t * Bg * (6 * Real.exp M' ^ 2)) * CU = t * C₂ := by
    rw [hC₂def]; ring
  linarith

/-- **Quantitative Hadamard estimate.** For `A` with a control of total increase `≤ M`, a
direction `h` for which the Duhamel integral exists, an approximation `g` of `h` of bounded
variation, `t > 0` and `k` with `A + t k` controlled with total increase `≤ M`,
`|t⁻¹ (P(A + t k) - P(A)) - Ψ_A(h)| ≤ (‖k - h‖ + 2 ‖h - g‖ + e^M t ‖k‖ V(g)) · 6 e^{2M}`, all
norms being sup norms on `[a, b]`. -/
theorem abs_div_sub_duhamelDerivFun_le (hab : a ≤ b) (hA : IsControl A V a b) {M : ℝ}
    (hV : V b - V a ≤ M) {h g k U W : ℝ → ℝ} {t δ₁ δ₂ δ₃ : ℝ} (ht : 0 < t)
    (hlim : Tendsto (fun s : Finset ℝ => twoTagSum (productIntegral A a)
      (fun x => productIntegral A x b) h (partitionPts a b s)) atTop
      (𝓝 (duhamelDerivFun A a b h)))
    (hB : IsControl (fun x => A x + t * k x) W a b) (hW : W b - W a ≤ M)
    (hg : IsControl g U a b)
    (hkh : ∀ x ∈ Set.Icc a b, |k x - h x| ≤ δ₁) (hhg : ∀ x ∈ Set.Icc a b, |h x - g x| ≤ δ₂)
    (hk : ∀ x ∈ Set.Icc a b, |k x| ≤ δ₃) :
    |t⁻¹ * (productIntegral (fun x => A x + t * k x) a b - productIntegral A a b) -
        duhamelDerivFun A a b h| ≤
      (δ₁ + 2 * δ₂ + Real.exp M * (t * δ₃) * (U b - U a)) * (6 * Real.exp M ^ 2) := by
  have hq := tendsto_twoTagSum_smul hab hA ht.ne' hB
  have hδ₂ : 0 ≤ δ₂ := (abs_nonneg _).trans (hhg a ⟨le_rfl, hab⟩)
  have hA1 : 1 ≤ Real.exp (V b - V a) := Real.one_le_exp (hA.sub_nonneg le_rfl hab le_rfl)
  have hB1 : 1 ≤ Real.exp (W b - W a) := Real.one_le_exp (hB.sub_nonneg le_rfl hab le_rfl)
  have hAM : Real.exp (V b - V a) ≤ Real.exp M := Real.exp_le_exp.2 hV
  have hBM : Real.exp (W b - W a) ≤ Real.exp M := Real.exp_le_exp.2 hW
  have hE1 : 1 ≤ Real.exp M := hA1.trans hAM
  have hBk : ∀ x ∈ Set.Icc a b, |(A x + t * k x) - A x| ≤ t * δ₃ := fun x hx => by
    rw [show A x + t * k x - A x = t * k x by ring, abs_mul, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (hk x hx) ht.le
  have hbound : ∀ s : Finset ℝ,
      |twoTagSum (productIntegral A a)
          (fun x => productIntegral (fun y => A y + t * k y) x b) k (partitionPts a b s) -
        twoTagSum (productIntegral A a) (fun x => productIntegral A x b) h
          (partitionPts a b s)| ≤
      δ₁ * (6 * Real.exp M ^ 2) + δ₂ * (12 * Real.exp M ^ 2) +
        Real.exp M * (t * δ₃ * (6 * Real.exp M ^ 2)) * (U b - U a) := by
    intro s
    have hdec : twoTagSum (productIntegral A a)
          (fun x => productIntegral (fun y => A y + t * k y) x b) k (partitionPts a b s) -
        twoTagSum (productIntegral A a) (fun x => productIntegral A x b) h
          (partitionPts a b s) =
        twoTagSum (productIntegral A a)
            (fun x => productIntegral (fun y => A y + t * k y) x b) (fun x => k x - h x)
            (partitionPts a b s) +
          twoTagSum (productIntegral A a)
            (fun x => productIntegral (fun y => A y + t * k y) x b - productIntegral A x b)
            (fun x => h x - g x) (partitionPts a b s) +
          twoTagSum (productIntegral A a)
            (fun x => productIntegral (fun y => A y + t * k y) x b - productIntegral A x b) g
            (partitionPts a b s) := by
      simp only [twoTagSum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    have X1 := abs_twoTagSum_productIntegral_le hab hA hB hV hW (h := fun x => k x - h x) hkh s
    have hGc := isControl_sub (isControl_productIntegral_right hB)
      (isControl_productIntegral_right hA)
    have hGb : ∀ x ∈ Set.Icc a b, |productIntegral (fun y => A y + t * k y) x b -
        productIntegral A x b| ≤ 2 * Real.exp M := fun x hx => by
      have := abs_sub (productIntegral (fun y => A y + t * k y) x b) (productIntegral A x b)
      have h1 := (abs_productIntegral_right_le hB hx).trans hBM
      have h2 := (abs_productIntegral_right_le hA hx).trans hAM
      linarith
    have X2 : |twoTagSum (productIntegral A a)
        (fun x => productIntegral (fun y => A y + t * k y) x b - productIntegral A x b)
        (fun x => h x - g x) (partitionPts a b s)| ≤ δ₂ * (12 * Real.exp M ^ 2) := by
      refine (abs_twoTagSum_le_of_abs_le hab hhg (fun x hx => abs_productIntegral_left_le hA hx)
        hGb (isControl_productIntegral_left hA) hGc s).trans (mul_le_mul_of_nonneg_left ?_ hδ₂)
      simp only [sub_self, Real.exp_zero]
      nlinarith [mul_le_mul hAM hBM (by linarith) (Real.exp_pos M).le,
        mul_le_mul hAM hAM (by linarith) (Real.exp_pos M).le,
        mul_le_mul hAM le_rfl (Real.exp_pos M).le (Real.exp_pos M).le]
    have hGd : ∀ x ∈ Set.Icc a b, |productIntegral (fun y => A y + t * k y) x b -
        productIntegral A x b| ≤ t * δ₃ * (6 * Real.exp M ^ 2) := fun x hx =>
      abs_productIntegral_right_sub_le hA hB hV hW hBk hx
    have X3 := abs_twoTagSum_le_of_isControl hab hg (M₁ := Real.exp M)
      (fun x hx => (abs_productIntegral_left_le hA hx).trans hAM) hGd s
    rw [hdec]
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add X1 X2)) X3)
  refine (le_of_tendsto (hq.sub hlim).abs (Eventually.of_forall hbound)).trans (le_of_eq ?_)
  ring

end Duhamel

/-! ### Paths in `ℓ^∞([0, τ])` -/

local notation "𝔻[" τ "]" => lp (fun _ : Set.Icc (0 : ℝ) τ ↦ ℝ) ∞

section Paths

variable {τ : ℝ}

/-- The path `t ↦ x t` of `x ∈ ℓ^∞([0, τ])`, extended by `0` outside `[0, τ]`. -/
noncomputable def toFun (x : 𝔻[τ]) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Icc (0 : ℝ) τ then x ⟨t, ht⟩ else 0

theorem toFun_of_mem (x : 𝔻[τ]) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) τ) :
    toFun x t = x ⟨t, ht⟩ := by
  simp [toFun, ht]

theorem toFun_add (x y : 𝔻[τ]) (t : ℝ) : toFun (x + y) t = toFun x t + toFun y t := by
  unfold toFun; split_ifs <;> simp

theorem toFun_sub (x y : 𝔻[τ]) (t : ℝ) : toFun (x - y) t = toFun x t - toFun y t := by
  unfold toFun; split_ifs <;> simp

theorem toFun_neg (x : 𝔻[τ]) (t : ℝ) : toFun (-x) t = -toFun x t := by
  unfold toFun; split_ifs <;> simp

theorem toFun_smul (c : ℝ) (x : 𝔻[τ]) (t : ℝ) : toFun (c • x) t = c * toFun x t := by
  unfold toFun; split_ifs <;> simp

theorem abs_toFun_le (x : 𝔻[τ]) (t : ℝ) : |toFun x t| ≤ ‖x‖ := by
  unfold toFun
  split_ifs with ht
  · rw [← Real.norm_eq_abs]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero x _
  · simp

theorem abs_toFun_sub_le (x y : 𝔻[τ]) (t : ℝ) : |toFun x t - toFun y t| ≤ ‖x - y‖ := by
  rw [← toFun_sub]
  exact abs_toFun_le _ _

/-- The paths of total variation at most `M` on `[0, τ]`: those with a monotone control whose
total increase on `[0, τ]` is at most `M`. -/
def tvBall (τ M : ℝ) : Set 𝔻[τ] :=
  {x | ∃ V : ℝ → ℝ, IsControl (toFun x) V 0 τ ∧ V τ - V 0 ≤ M}

/-- The paths of bounded variation on `[0, τ]`. -/
def bvPaths (τ : ℝ) : Set 𝔻[τ] :=
  {x | ∃ V : ℝ → ℝ, IsControl (toFun x) V 0 τ}

/-- The continuous-time product integral `∏_{(0, τ]} (1 + dx)` of a path (T77). -/
noncomputable def prodIntegralEnd (x : 𝔻[τ]) : ℝ :=
  productIntegral (toFun x) 0 τ

/-- The Duhamel derivative `h ↦ ∫_{(0, τ]} P(θ)(0, s) dh(s) P(θ)(s, τ]` of the product integral
at the path `θ`. -/
noncomputable def duhamelDeriv (θ h : 𝔻[τ]) : ℝ :=
  duhamelDerivFun (toFun θ) 0 τ (toFun h)

/-- A path in the uniform closure of the bounded-variation paths is uniformly approximated by
controlled functions. -/
theorem exists_approx_of_mem_closure {h : 𝔻[τ]} (hh : h ∈ closure (bvPaths τ)) {ε : ℝ}
    (hε : 0 < ε) : ∃ g U : ℝ → ℝ, IsControl g U 0 τ ∧ ∀ x, |toFun h x - g x| ≤ ε := by
  obtain ⟨y, ⟨U, hU⟩, hy⟩ := Metric.mem_closure_iff.1 hh ε hε
  refine ⟨toFun y, U, hU, fun x => (abs_toFun_sub_le h y x).trans ?_⟩
  rw [← dist_eq_norm]
  exact hy.le

/-- The two-tag sums defining `duhamelDeriv θ h` converge for `θ` of bounded variation and `h`
in the uniform closure of the bounded-variation paths. -/
theorem tendsto_duhamelDeriv (hτ : 0 ≤ τ) {θ h : 𝔻[τ]} {V : ℝ → ℝ}
    (hV : IsControl (toFun θ) V 0 τ) (hh : h ∈ closure (bvPaths τ)) :
    Tendsto (fun s : Finset ℝ => twoTagSum (productIntegral (toFun θ) 0)
      (fun x => productIntegral (toFun θ) x τ) (toFun h) (partitionPts 0 τ s)) atTop
      (𝓝 (duhamelDeriv θ h)) :=
  tendsto_duhamelDerivFun hτ hV fun ε hε => by
    obtain ⟨g, U, hU, hg⟩ := exists_approx_of_mem_closure hh hε
    exact ⟨g, U, hU, fun x _ => hg x⟩

/-- **Hadamard differentiability of the continuous-time product integral** (Gill–Johansen 1990;
van der Vaart 1998, §20.3). At every path `θ` of total variation `≤ M` on `[0, τ]`, the map
`x ↦ ∏_{(0, τ]} (1 + dx)` (T77's Lebesgue–Stieltjes product integral, no hypothesis bundle) is
Hadamard differentiable on the total-variation ball `tvBall τ M`, tangentially to the uniform
closure of the bounded-variation paths, with the Duhamel derivative `duhamelDeriv θ`. The tangent
set contains every bounded-variation path, jump paths included, and `C[0, τ]`
(`continuous_mem_closure_bvPaths`); classically it is the set of regulated paths. -/
theorem hasHadamardDerivWithinAt_prodIntegralEnd (hτ : 0 ≤ τ) {M : ℝ} {θ : 𝔻[τ]}
    (hθ : θ ∈ tvBall τ M) :
    HasHadamardDerivWithinAt prodIntegralEnd (duhamelDeriv θ) (tvBall τ M)
      (closure (bvPaths τ)) θ := by
  intro h hh
  obtain ⟨V, hV, hVM⟩ := hθ
  have hM0 : 0 ≤ M := (hV.sub_nonneg le_rfl hτ le_rfl).trans hVM
  have hlim := tendsto_duhamelDeriv hτ hV hh
  rw [Metric.tendsto_nhds]
  intro ε hε
  set K := 6 * Real.exp M ^ 2 with hKdef
  have hK : 0 ≤ K := by positivity
  obtain ⟨g, U, hU, hg⟩ := exists_approx_of_mem_closure hh
    (show 0 < ε / (4 * (2 * K + 1)) by positivity)
  set CU := U τ - U 0 with hCUdef
  have hCU : 0 ≤ CU := hU.sub_nonneg le_rfl hτ le_rfl
  set c := Real.exp M * (‖h‖ + 1) * CU * K with hcdef
  have hc : 0 ≤ c := by positivity
  set η := ε / (4 * (K + 1)) with hηdef
  have hη : 0 < η := by positivity
  set η' := ε / (4 * (c + 1)) with hη'def
  have hη' : 0 < η' := by positivity
  have hev : ∀ᶠ p : ℝ × 𝔻[τ] in (𝓝[>] 0 ×ˢ 𝓝 h) ⊓ 𝓟 {p | θ + p.1 • p.2 ∈ tvBall τ M},
      p ∈ Set.Ioo 0 η' ×ˢ Metric.ball h (min η 1) ∧ θ + p.1 • p.2 ∈ tvBall τ M := by
    filter_upwards [mem_inf_of_left (prod_mem_prod (Ioo_mem_nhdsGT hη')
      (Metric.ball_mem_nhds h (lt_min hη one_pos))), mem_inf_of_right (mem_principal_self _)]
      with p h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hev] with p hp
  obtain ⟨⟨⟨ht0, htη⟩, hkh⟩, W, hW, hWM⟩ := hp
  have hkh' : ‖p.2 - h‖ < min η 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hkh
  have hfun : toFun (θ + p.1 • p.2) = fun x => toFun θ x + p.1 * toFun p.2 x := by
    funext x
    rw [toFun_add, toFun_smul]
  rw [hfun] at hW
  have hk : ∀ x ∈ Set.Icc (0 : ℝ) τ, |toFun p.2 x| ≤ ‖h‖ + 1 := fun x _ => by
    have h1 := abs_toFun_le p.2 x
    have h2 : ‖p.2‖ ≤ ‖h‖ + ‖p.2 - h‖ := by
      calc ‖p.2‖ = ‖h + (p.2 - h)‖ := by rw [add_sub_cancel]
        _ ≤ ‖h‖ + ‖p.2 - h‖ := norm_add_le _ _
    linarith [min_le_right η 1]
  have key := abs_div_sub_duhamelDerivFun_le hτ hV hVM ht0 hlim hW hWM hU
    (fun x _ => abs_toFun_sub_le p.2 h x) (fun x _ => hg x) hk
  rw [Real.dist_eq, smul_eq_mul, prodIntegralEnd, prodIntegralEnd, hfun]
  refine lt_of_le_of_lt key ?_
  have b1 : ‖p.2 - h‖ * K ≤ ε / 4 :=
    (mul_le_mul_of_nonneg_right (hkh'.le.trans (min_le_left _ _)) hK).trans
      (div_four_mul_le hε hK)
  have b2 : ε / (4 * (2 * K + 1)) * (2 * K) ≤ ε / 4 := div_four_mul_le hε (by positivity)
  have b3 : p.1 * c ≤ ε / 4 := (mul_le_mul_of_nonneg_right htη.le hc).trans (div_four_mul_le hε hc)
  have e : (‖p.2 - h‖ + 2 * (ε / (4 * (2 * K + 1))) +
      Real.exp M * (p.1 * (‖h‖ + 1)) * (U τ - U 0)) * (6 * Real.exp M ^ 2) =
      ‖p.2 - h‖ * K + ε / (4 * (2 * K + 1)) * (2 * K) + p.1 * c := by
    rw [hcdef, hKdef, hCUdef]; ring
  rw [e]
  linarith

/-- The Duhamel derivative is Lipschitz on the tangent set: `|Ψ_θ(h) - Ψ_θ(h')| ≤
‖h - h'‖ · 6 e^{2M}`. -/
theorem abs_duhamelDeriv_sub_le (hτ : 0 ≤ τ) {M : ℝ} {θ : 𝔻[τ]} (hθ : θ ∈ tvBall τ M)
    {h h' : 𝔻[τ]} (hh : h ∈ closure (bvPaths τ)) (hh' : h' ∈ closure (bvPaths τ)) :
    |duhamelDeriv θ h - duhamelDeriv θ h'| ≤ ‖h - h'‖ * (6 * Real.exp M ^ 2) := by
  obtain ⟨V, hV, hVM⟩ := hθ
  refine le_of_tendsto ((tendsto_duhamelDeriv hτ hV hh).sub
    (tendsto_duhamelDeriv hτ hV hh')).abs (Eventually.of_forall fun s => ?_)
  rw [← twoTagSum_sub_right]
  exact abs_twoTagSum_productIntegral_le hτ hV hV hVM hVM
    (fun x _ => by rw [Pi.sub_apply]; exact abs_toFun_sub_le h h' x) s

theorem continuousOn_duhamelDeriv (hτ : 0 ≤ τ) {M : ℝ} {θ : 𝔻[τ]} (hθ : θ ∈ tvBall τ M) :
    ContinuousOn (duhamelDeriv θ) (closure (bvPaths τ)) := by
  intro h hh
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set K := 6 * Real.exp M ^ 2 with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨ε / (K + 1), by positivity, ?_⟩
  intro h' hh' hd
  rw [dist_eq_norm] at hd
  rw [Real.dist_eq]
  calc |duhamelDeriv θ h' - duhamelDeriv θ h| ≤ ‖h' - h‖ * K :=
        abs_duhamelDeriv_sub_le hτ hθ hh' hh
    _ ≤ ε / (K + 1) * K := mul_le_mul_of_nonneg_right hd.le hK
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- A function continuous on a closed set carrying the law `L` is `L`-a.e. measurable. -/
theorem aemeasurable_of_continuousOn [MeasurableSpace 𝔻[τ]] [BorelSpace 𝔻[τ]] {f : 𝔻[τ] → ℝ}
    {s : Set 𝔻[τ]} (hf : ContinuousOn f s) (hs : IsClosed s) {L : Measure 𝔻[τ]}
    (hL : ∀ᵐ h ∂L, h ∈ s) : AEMeasurable f L := by
  classical
  have hm : Measurable (s.piecewise f fun _ => 0) :=
    hf.measurable_piecewise continuousOn_const hs.measurableSet
  refine ⟨_, hm, ?_⟩
  filter_upwards [hL] with h hh
  exact (Set.piecewise_eq_of_mem _ _ _ hh).symm

/-- The tangent set is symmetric. -/
theorem neg_mem_closure_bvPaths {h : 𝔻[τ]} (hh : h ∈ closure (bvPaths τ)) :
    -h ∈ closure (bvPaths τ) := by
  rw [Metric.mem_closure_iff] at hh ⊢
  intro ε hε
  obtain ⟨y, ⟨U, hU⟩, hy⟩ := hh ε hε
  refine ⟨-y, ⟨U, IsControl.congr (IsControl.neg hU) fun t _ => (toFun_neg y t).symm⟩, ?_⟩
  rwa [dist_neg_neg]

/-- The Duhamel derivative is a.e. measurable for every Borel law carried by the tangent set. -/
theorem aemeasurable_duhamelDeriv [MeasurableSpace 𝔻[τ]] [BorelSpace 𝔻[τ]] (hτ : 0 ≤ τ)
    {M : ℝ} {θ : 𝔻[τ]} (hθ : θ ∈ tvBall τ M) {L : Measure 𝔻[τ]}
    (hL : ∀ᵐ h ∂L, h ∈ closure (bvPaths τ)) : AEMeasurable (duhamelDeriv θ) L :=
  aemeasurable_of_continuousOn (continuousOn_duhamelDeriv hτ hθ) isClosed_closure hL

/-- **The tangent set contains `C[0, τ]`** (Weierstrass: polynomials have bounded variation). -/
theorem continuous_mem_closure_bvPaths (hτ : 0 ≤ τ) {h : 𝔻[τ]} (hc : Continuous fun t => h t) :
    h ∈ closure (bvPaths τ) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hcont : ContinuousOn (toFun h) (Set.Icc 0 τ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine hc.congr fun t => ?_
    simp [Set.domRestrict, toFun_of_mem h t.2]
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 τ (toFun h) hcont (ε / 2)
    (half_pos hε)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (p.continuous (R := ℝ)).continuousOn (s := Set.Icc (0 : ℝ) τ)
  have hmem : Memℓp (fun t : Set.Icc (0 : ℝ) τ => p.eval (t : ℝ)) ∞ :=
    memℓp_infty ⟨C, by rintro _ ⟨t, rfl⟩; exact hC t t.2⟩
  set y : 𝔻[τ] := ⟨_, hmem⟩ with hydef
  have hy : ∀ t ∈ Set.Icc (0 : ℝ) τ, toFun y t = p.eval t := fun t ht => by
    rw [toFun_of_mem y ht]
  refine ⟨y, ⟨_, IsControl.congr (exists_control_of_boundedVariationOn
    (boundedVariationOn_polynomial_eval p hτ)) fun t ht => (hy t ht).symm⟩, ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (lp.norm_le_of_forall_le (half_pos hε).le fun t => ?_) (half_lt_self hε)
  rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs, ← toFun_of_mem h t.2, ← toFun_of_mem y t.2,
    hy t t.2, abs_sub_comm]
  exact (hp t t.2).le

end Paths

/-! ### The survival map -/

section Neg

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Precomposition with negation: if `φ` is Hadamard differentiable at `-θ`, then
`x ↦ φ (-x)` is Hadamard differentiable at `θ`, with derivative `h ↦ φ' (-h)`, on the domain
`-D` and tangentially to `-E₀`. -/
theorem _root_.HasHadamardDerivWithinAt.comp_neg {φ φ' : E → F} {D E₀ : Set E} {θ : E}
    (hφ : HasHadamardDerivWithinAt φ φ' D E₀ (-θ)) :
    HasHadamardDerivWithinAt (fun x => φ (-x)) (fun h => φ' (-h)) {x | -x ∈ D}
      {h | -h ∈ E₀} θ := by
  intro h hh
  have key := hφ (-h) hh
  have hmap : Tendsto (fun p : ℝ × E => (p.1, -p.2))
      ((𝓝[>] 0 ×ˢ 𝓝 h) ⊓ 𝓟 {p | θ + p.1 • p.2 ∈ {x | -x ∈ D}})
      ((𝓝[>] 0 ×ˢ 𝓝 (-h)) ⊓ 𝓟 {p | -θ + p.1 • p.2 ∈ D}) := by
    refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
    · exact (tendsto_id.prodMap (continuous_neg.tendsto h)).mono_left inf_le_left
    · filter_upwards [mem_inf_of_right (mem_principal_self _)] with p hp
      rw [smul_neg, ← neg_add]
      exact hp
  refine (key.comp hmap).congr fun p => ?_
  simp only [Function.comp_apply]
  rw [smul_neg, ← neg_add]

end Neg

section Survival

variable {τ : ℝ}

/-- **Hadamard differentiability of the continuous-time survival map** `Λ ↦ ∏_{(0, τ]} (1 - dΛ)`
at every cumulative hazard `Λ` with `-Λ` of total variation `≤ M`, with derivative
`h ↦ Ψ_{-Λ}(-h)`, tangentially to the uniform closure of the bounded-variation paths. -/
theorem hasHadamardDerivWithinAt_survivalEnd (hτ : 0 ≤ τ) {M : ℝ} {Λ : 𝔻[τ]}
    (hΛ : -Λ ∈ tvBall τ M) :
    HasHadamardDerivWithinAt (fun x : 𝔻[τ] => prodIntegralEnd (-x))
      (fun h => duhamelDeriv (-Λ) (-h)) {x | -x ∈ tvBall τ M} {h | -h ∈ closure (bvPaths τ)}
      Λ :=
  (hasHadamardDerivWithinAt_prodIntegralEnd hτ hΛ).comp_neg

/-! ### The functional delta theorem in continuous time -/

variable [MeasurableSpace 𝔻[τ]] [BorelSpace 𝔻[τ]]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Functional delta theorem for the continuous-time product integral**, outer-probability
framework (van der Vaart, Theorem 20.8; van der Vaart–Wellner, Theorem 3.9.4). Let `r n → ∞`
and `r n • (X n - θ) ⇝ L` in `ℓ^∞([0, τ])` (outer weak convergence, no measurability of `X n`),
with `L` carried by the uniform closure of the bounded-variation paths, and let
`P*(X n ∉ tvBall τ M) → 0` with `θ ∈ tvBall τ M`. Then
`r n (∏_{(0, τ]} (1 + dX n) - ∏_{(0, τ]} (1 + dθ)) ⇝ L ∘ (duhamelDeriv θ)⁻¹`. -/
theorem tendstoInDistributionOuter_prodIntegralEnd (hτ : 0 ≤ τ) {M : ℝ} {θ : 𝔻[τ]}
    (hθ : θ ∈ tvBall τ M) {X : ℕ → Ω → 𝔻[τ]} {r : ℕ → ℝ} {L : ProbabilityMeasure 𝔻[τ]}
    (hXL : TendstoInDistributionOuter (fun n ω ↦ r n • (X n ω - θ)) μ L)
    (hr : Tendsto r atTop atTop)
    (hXD : Tendsto (fun n ↦ μ {ω | X n ω ∉ tvBall τ M}) atTop (𝓝 0))
    (hL : ∀ᵐ h ∂(L : Measure 𝔻[τ]), h ∈ closure (bvPaths τ)) :
    TendstoInDistributionOuter
      (fun n ω ↦ r n • (prodIntegralEnd (X n ω) - prodIntegralEnd θ)) μ
      (L.map (duhamelDeriv θ)) :=
  hXL.functional_delta hr (hasHadamardDerivWithinAt_prodIntegralEnd hτ hθ) hXD hL
    (aemeasurable_duhamelDeriv hτ hθ hL)

/-- **Functional delta theorem for the continuous-time survival map**: if
`r n • (Λhat n - Λ) ⇝ L` in `ℓ^∞([0, τ])` (outer), with `L` carried by the uniform closure of the
bounded-variation paths, and `P*(-Λhat n ∉ tvBall τ M) → 0` with `-Λ ∈ tvBall τ M`, then
`r n (∏_{(0, τ]} (1 - dΛhat n) - ∏_{(0, τ]} (1 - dΛ)) ⇝ L ∘ (h ↦ Ψ_{-Λ}(-h))⁻¹`. -/
theorem tendstoInDistributionOuter_survivalEnd (hτ : 0 ≤ τ) {M : ℝ} {Λ : 𝔻[τ]}
    (hΛ : -Λ ∈ tvBall τ M) {Λhat : ℕ → Ω → 𝔻[τ]} {r : ℕ → ℝ} {L : ProbabilityMeasure 𝔻[τ]}
    (hXL : TendstoInDistributionOuter (fun n ω ↦ r n • (Λhat n ω - Λ)) μ L)
    (hr : Tendsto r atTop atTop)
    (hXD : Tendsto (fun n ↦ μ {ω | -Λhat n ω ∉ tvBall τ M}) atTop (𝓝 0))
    (hL : ∀ᵐ h ∂(L : Measure 𝔻[τ]), h ∈ closure (bvPaths τ)) :
    TendstoInDistributionOuter
      (fun n ω ↦ r n • (prodIntegralEnd (-Λhat n ω) - prodIntegralEnd (-Λ))) μ
      (L.map fun h ↦ duhamelDeriv (-Λ) (-h)) := by
  have hL' : ∀ᵐ h ∂(L : Measure 𝔻[τ]), h ∈ {h : 𝔻[τ] | -h ∈ closure (bvPaths τ)} := by
    filter_upwards [hL] with h hh
    exact neg_mem_closure_bvPaths hh
  have hc : ContinuousOn (fun h : 𝔻[τ] ↦ duhamelDeriv (-Λ) (-h))
      {h : 𝔻[τ] | -h ∈ closure (bvPaths τ)} :=
    (continuousOn_duhamelDeriv hτ hΛ).comp continuous_neg.continuousOn fun _ hh => hh
  have hcl : IsClosed {h : 𝔻[τ] | -h ∈ closure (bvPaths τ)} :=
    isClosed_closure.preimage continuous_neg
  have hφ' : AEMeasurable (fun h : 𝔻[τ] ↦ duhamelDeriv (-Λ) (-h)) (L : Measure 𝔻[τ]) :=
    aemeasurable_of_continuousOn hc hcl hL'
  have hXD' : Tendsto (fun n ↦ μ {ω | Λhat n ω ∉ {x : 𝔻[τ] | -x ∈ tvBall τ M}}) atTop (𝓝 0) :=
    hXD
  exact TendstoInDistributionOuter.functional_delta (φ := fun x : 𝔻[τ] ↦ prodIntegralEnd (-x))
    hXL hr (hasHadamardDerivWithinAt_survivalEnd hτ hΛ) hXD' hL' hφ'

end Survival

end MathlibExt.Probability.Statistics.FunctionalDeltaContinuous
