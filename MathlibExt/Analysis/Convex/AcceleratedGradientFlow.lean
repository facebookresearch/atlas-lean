/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Monotone.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import MathlibExt.Analysis.Convex.FirstOrderCondition

/-!
# The Euler–Lagrange flow of the Bregman Lagrangian (Euclidean case)

A. Wibisono, A. C. Wilson and M. I. Jordan (*A variational perspective on accelerated methods in
optimization*, PNAS 113 (2016); arXiv:1603.04245v1) generate accelerated methods in continuous
time from the Bregman Lagrangian
`𝓛(X, V, t) = e^{α t + γ t} (D_h(X + e^{-α t} V, X) - e^{β t} f(X))`, eq. (2.1).
Under the ideal scaling `β' ≤ e^α`, `γ' = e^α` (2.2), its Euler–Lagrange equation is (2.7):
`d/dt ∇h(X + e^{-α} X') = -e^{α + β} ∇f(X)`, and the energy (2.8)
`𝓔 t = D_h(x⋆, X t + e^{-α t} X' t) + e^{β t} (f (X t) - f x⋆)` is nonincreasing (Theorem 2.1),
so `f (X t) - f x⋆ = O(e^{-β t})`.

This file proves Theorem 2.1 in the Euclidean case `h = ‖·‖² / 2`, where `∇h` is the identity and
`D_h(x, y) = ‖x - y‖² / 2`. The curve `Z = X + e^{-α} X'` is written as a second unknown, so the
Euler–Lagrange equation becomes the first-order system `X' = e^α (Z - X)`,
`Z' = -e^{α + β} ∇f(X)`.

## Main results

* `bregmanLagrangian_energy_antitoneOn`: the energy is nonincreasing (WWJ Theorem 2.1).
* `bregmanLagrangian_rate`: the rate `f (X t) - f x⋆ ≤ 𝓔 t₀ · e^{-β t}`.
* `polynomialFamily_rate`: the `O(1 / t^p)` rate of the polynomial family (3.1)-(3.3).
* `suBoydCandes_rate`: the `O(1 / t²)` rate for `X'' + (3 / t) X' + ∇f(X) = 0`.
* `timeDilation`, `timeDilation_idealScaling`: reparametrizing time maps solutions to solutions
  for the parameters (2.10) (WWJ Theorem 2.2).
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.AcceleratedGradientFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Energy of the Euclidean Bregman-Lagrangian flow.** For curves `X Z : ℝ → E`, a time scale
`β` and a point `x⋆`, `𝓔 t = ‖Z t - x⋆‖² / 2 + e^{β t} (f (X t) - f x⋆)`: equation (2.8) of
Wibisono, Wilson and Jordan, arXiv:1603.04245v1, with `h = ‖·‖² / 2` and
`Z = X + e^{-α} X'`. -/
noncomputable def energy (f : E → ℝ) (β : ℝ → ℝ) (X Z : ℝ → E) (xstar : E) (t : ℝ) : ℝ :=
  ‖Z t - xstar‖ ^ 2 / 2 + Real.exp (β t) * (f (X t) - f xstar)

private theorem hasDerivAt_energy {f : E → ℝ} (hdiff : Differentiable ℝ f)
    {α β β' : ℝ → ℝ} {X Z : ℝ → E} {xstar : E} {t : ℝ}
    (hβ : HasDerivAt β (β' t) t)
    (hX : HasDerivAt X (Real.exp (α t) • (Z t - X t)) t)
    (hZ : HasDerivAt Z (-Real.exp (α t + β t) • gradient f (X t)) t) :
    HasDerivAt (energy f β X Z xstar)
      (-Real.exp (α t + β t) * inner ℝ (Z t - xstar) (gradient f (X t)) +
        (β' t * Real.exp (β t) * (f (X t) - f xstar) +
          Real.exp (β t) * (Real.exp (α t) * inner ℝ (gradient f (X t)) (Z t - X t)))) t := by
  have h1 : HasDerivAt (fun s => ‖Z s - xstar‖ ^ 2 / 2)
      (-Real.exp (α t + β t) * inner ℝ (Z t - xstar) (gradient f (X t))) t := by
    have := ((hZ.sub_const xstar).norm_sq).div_const 2
    convert this using 1
    rw [inner_smul_right]; ring
  have hfX : HasDerivAt (fun s => f (X s))
      (inner ℝ (gradient f (X t)) (Real.exp (α t) • (Z t - X t))) t := by
    have hf := (hdiff (X t)).hasGradientAt.hasFDerivAt
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
      (hf.comp t hX.hasFDerivAt).hasDerivAt
  have h2 : HasDerivAt (fun s => Real.exp (β s) * (f (X s) - f xstar))
      (β' t * Real.exp (β t) * (f (X t) - f xstar) +
        Real.exp (β t) * (Real.exp (α t) * inner ℝ (gradient f (X t)) (Z t - X t))) t := by
    have := (hβ.exp).mul (hfX.sub_const (f xstar))
    convert this using 1
    rw [inner_smul_right]; ring
  exact h1.add h2

/-- **The energy of the Bregman-Lagrangian flow is nonincreasing (Euclidean case).** Let `f` be
convex and differentiable on a real Hilbert space with a global minimizer `x⋆`. Let
`α β β' : ℝ → ℝ` and `X Z : ℝ → E` satisfy, at every time `t ≥ t₀`: `β' t` is the derivative of
`β`, the ideal scaling `β' t ≤ e^{α t}` (eq. (2.2a)), and the Euler–Lagrange system
`X' t = e^{α t} (Z t - X t)` (that is, `Z = X + e^{-α} X'`) and
`Z' t = -e^{α t + β t} ∇f (X t)` (eq. (2.7) with `h = ‖·‖² / 2`). Then the energy
`‖Z t - x⋆‖² / 2 + e^{β t} (f (X t) - f x⋆)` is nonincreasing on `[t₀, ∞)`.

Source: A. Wibisono, A. C. Wilson and M. I. Jordan, *A variational perspective on accelerated
methods in optimization*, arXiv:1603.04245v1 (PNAS 113 (2016) E7351-E7358), Theorem 2.1 and its
proof, with the energy (2.8), specialised to the Euclidean distance-generating function. -/
theorem bregmanLagrangian_energy_antitoneOn {f : E → ℝ} (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) {xstar : E} (hmin : ∀ x, f xstar ≤ f x)
    {α β β' : ℝ → ℝ} {X Z : ℝ → E} {t₀ : ℝ}
    (hβ : ∀ t ∈ Set.Ici t₀, HasDerivAt β (β' t) t)
    (hscale : ∀ t ∈ Set.Ici t₀, β' t ≤ Real.exp (α t))
    (hX : ∀ t ∈ Set.Ici t₀, HasDerivAt X (Real.exp (α t) • (Z t - X t)) t)
    (hZ : ∀ t ∈ Set.Ici t₀, HasDerivAt Z (-Real.exp (α t + β t) • gradient f (X t)) t) :
    AntitoneOn (energy f β X Z xstar) (Set.Ici t₀) := by
  have hD : ∀ t ∈ Set.Ici t₀, HasDerivAt (energy f β X Z xstar) _ t := fun t ht =>
    hasDerivAt_energy hdiff (hβ t ht) (hX t ht) (hZ t ht)
  apply antitoneOn_of_deriv_nonpos (convex_Ici t₀)
  · exact fun t ht => (hD t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact (hD t (Set.mem_Ici.2 (le_of_lt ht))).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have ht' : t ∈ Set.Ici t₀ := Set.mem_Ici.2 (le_of_lt ht)
    rw [(hD t ht').deriv]
    -- first-order convexity at `X t` towards `x⋆`
    have hc := MathlibExt.Analysis.Convex.FirstOrderCondition.add_fderiv_le_of_convexOn hconvex
      (Set.mem_univ (X t)) (Set.mem_univ xstar) (hdiff (X t)).hasGradientAt.hasFDerivAt
    simp only [InnerProductSpace.toDual_apply_apply] at hc
    set g := gradient f (X t)
    have hinner : inner ℝ g (Z t - X t) - inner ℝ (Z t - xstar) g = inner ℝ g (xstar - X t) := by
      rw [real_inner_comm g (Z t - xstar), ← inner_sub_right]
      congr 1; abel
    have hgap : 0 ≤ f (X t) - f xstar := sub_nonneg.2 (hmin _)
    have hea : 0 < Real.exp (α t) := Real.exp_pos _
    have heb : 0 < Real.exp (β t) := Real.exp_pos _
    have hexp : Real.exp (α t + β t) = Real.exp (α t) * Real.exp (β t) := Real.exp_add _ _
    have h1 : Real.exp (α t) * Real.exp (β t) * inner ℝ g (xstar - X t) ≤
        Real.exp (α t) * Real.exp (β t) * (f xstar - f (X t)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : β' t * Real.exp (β t) * (f (X t) - f xstar) ≤
        Real.exp (α t) * Real.exp (β t) * (f (X t) - f xstar) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hscale t ht') heb.le) hgap
    rw [hexp]
    have hrw : -(Real.exp (α t) * Real.exp (β t)) * inner ℝ (Z t - xstar) g +
        (β' t * Real.exp (β t) * (f (X t) - f xstar) +
          Real.exp (β t) * (Real.exp (α t) * inner ℝ g (Z t - X t))) =
        Real.exp (α t) * Real.exp (β t) * (inner ℝ g (Z t - X t) - inner ℝ (Z t - xstar) g) +
          β' t * Real.exp (β t) * (f (X t) - f xstar) := by ring
    rw [hrw, hinner]
    linarith

/-- **Convergence rate of the Bregman-Lagrangian flow (Euclidean case).** Under the hypotheses of
`bregmanLagrangian_energy_antitoneOn`, for every `t ≥ t₀`,
`f (X t) - f x⋆ ≤ 𝓔 t₀ · e^{-β t}` with
`𝓔 t₀ = ‖Z t₀ - x⋆‖² / 2 + e^{β t₀} (f (X t₀) - f x⋆)`: the rate `O(e^{-β t})`.

Source: A. Wibisono, A. C. Wilson and M. I. Jordan, arXiv:1603.04245v1, Theorem 2.1 (the bound
`f(X_t) - f(x⋆) ≤ 𝓔_{t₀} e^{-β_t}` at the end of its proof), Euclidean case. -/
theorem bregmanLagrangian_rate {f : E → ℝ} (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) {xstar : E} (hmin : ∀ x, f xstar ≤ f x)
    {α β β' : ℝ → ℝ} {X Z : ℝ → E} {t₀ : ℝ}
    (hβ : ∀ t ∈ Set.Ici t₀, HasDerivAt β (β' t) t)
    (hscale : ∀ t ∈ Set.Ici t₀, β' t ≤ Real.exp (α t))
    (hX : ∀ t ∈ Set.Ici t₀, HasDerivAt X (Real.exp (α t) • (Z t - X t)) t)
    (hZ : ∀ t ∈ Set.Ici t₀, HasDerivAt Z (-Real.exp (α t + β t) • gradient f (X t)) t)
    {t : ℝ} (ht : t₀ ≤ t) :
    f (X t) - f xstar ≤ energy f β X Z xstar t₀ * Real.exp (-β t) := by
  have hanti := bregmanLagrangian_energy_antitoneOn hconvex hdiff hmin hβ hscale hX hZ
    (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht) ht
  have hle : Real.exp (β t) * (f (X t) - f xstar) ≤ energy f β X Z xstar t₀ := by
    refine le_trans ?_ hanti
    simp only [energy]
    nlinarith [sq_nonneg ‖Z t - xstar‖]
  have hpos : 0 < Real.exp (β t) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

/-- **Polynomial rate `O(1 / t^p)` for the polynomial Bregman-Lagrangian family (Euclidean
case).** Let `f` be convex and differentiable on a real Hilbert space with a global minimizer
`x⋆`, and let `p C t₀ > 0`. Let `X Z : ℝ → E` satisfy, at every time `t ≥ t₀`, the first-order
form (3.3) of the Euler–Lagrange equation (3.2): `Z = X + (t / p) X'`, written
`X' t = (p / t) (Z t - X t)`, and `Z' t = -C p t^{p-1} ∇f (X t)`. Then for every `t ≥ t₀`,
`f (X t) - f x⋆ ≤ (‖Z t₀ - x⋆‖² / 2 + C t₀^p (f (X t₀) - f x⋆)) / (C t^p)`.

Source: A. Wibisono, A. C. Wilson and M. I. Jordan, arXiv:1603.04245v1, Section 3: the
parameters (3.1a)-(3.1b) `α t = log p - log t`, `β t = p log t + log C`, the system (3.3a)-(3.3b)
with `h = ‖·‖² / 2`, and the `O(1 / t^p)` rate obtained there from Theorem 2.1. -/
theorem polynomialFamily_rate {f : E → ℝ} (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) {xstar : E} (hmin : ∀ x, f xstar ≤ f x)
    {p C t₀ : ℝ} (hp : 0 < p) (hC : 0 < C) (ht₀ : 0 < t₀) {X Z : ℝ → E}
    (hX : ∀ t ∈ Set.Ici t₀, HasDerivAt X ((p / t) • (Z t - X t)) t)
    (hZ : ∀ t ∈ Set.Ici t₀,
      HasDerivAt Z (-(C * p * t ^ (p - 1)) • gradient f (X t)) t)
    {t : ℝ} (ht : t₀ ≤ t) :
    f (X t) - f xstar ≤
      (‖Z t₀ - xstar‖ ^ 2 / 2 + C * t₀ ^ p * (f (X t₀) - f xstar)) / (C * t ^ p) := by
  set α : ℝ → ℝ := fun s => Real.log p - Real.log s
  set β : ℝ → ℝ := fun s => p * Real.log s + Real.log C
  have hpos : ∀ s ∈ Set.Ici t₀, 0 < s := fun s hs => lt_of_lt_of_le ht₀ hs
  have hexpα : ∀ s ∈ Set.Ici t₀, Real.exp (α s) = p / s := by
    intro s hs
    simp only [α, Real.exp_sub, Real.exp_log hp, Real.exp_log (hpos s hs)]
  have hexpβ : ∀ s ∈ Set.Ici t₀, Real.exp (β s) = C * s ^ p := by
    intro s hs
    simp only [β, Real.exp_add, Real.exp_log hC, mul_comm p, Real.exp_mul,
      Real.exp_log (hpos s hs)]
    ring
  have hβ : ∀ s ∈ Set.Ici t₀, HasDerivAt β (p / s) s := by
    intro s hs
    have := ((Real.hasDerivAt_log (hpos s hs).ne').const_mul p).add_const (Real.log C)
    convert this using 1
    field_simp
  have hscale : ∀ s ∈ Set.Ici t₀, p / s ≤ Real.exp (α s) := fun s hs => (hexpα s hs).ge
  have hX' : ∀ s ∈ Set.Ici t₀, HasDerivAt X (Real.exp (α s) • (Z s - X s)) s := by
    intro s hs; rw [hexpα s hs]; exact hX s hs
  have hZ' : ∀ s ∈ Set.Ici t₀,
      HasDerivAt Z (-Real.exp (α s + β s) • gradient f (X s)) s := by
    intro s hs
    have hs0 := hpos s hs
    have : Real.exp (α s + β s) = C * p * s ^ (p - 1) := by
      rw [Real.exp_add, hexpα s hs, hexpβ s hs, Real.rpow_sub hs0, Real.rpow_one]
      field_simp
    rw [this]; exact hZ s hs
  have h := bregmanLagrangian_rate hconvex hdiff hmin hβ hscale hX' hZ' ht
  have ht0 : t₀ ∈ Set.Ici t₀ := Set.mem_Ici.2 le_rfl
  have htt : t ∈ Set.Ici t₀ := Set.mem_Ici.2 ht
  rw [Real.exp_neg, hexpβ t htt] at h
  simp only [energy, hexpβ t₀ ht0] at h
  simpa [div_eq_mul_inv] using h

/-- **The Su–Boyd–Candès rate for the continuous limit of Nesterov's method.** Let `f` be convex
and differentiable on a real Hilbert space with a global minimizer `x⋆`, and `t₀ > 0`. If
`X V : ℝ → E` solve `X' = V`, `V' = -(3 / t) V - ∇f (X)` on `[t₀, ∞)` (the ODE
`X'' + (3 / t) X' + ∇f(X) = 0`), then for every `t ≥ t₀`,
`f (X t) - f x⋆ ≤ (2 ‖X t₀ + (t₀ / 2) V t₀ - x⋆‖² + t₀² (f (X t₀) - f x⋆)) / t²`.

Source: A. Wibisono, A. C. Wilson and M. I. Jordan, arXiv:1603.04245v1, Section 3: equation
(3.2) with `p = 2`, `C = 1 / 4` and `∇²h = I` is the differential equation of W. Su, S. Boyd and
E. J. Candès (*A differential equation for modeling Nesterov's accelerated gradient method*,
JMLR 17 (2016)); the rate is Theorem 2.1 via `polynomialFamily_rate`. -/
theorem suBoydCandes_rate {f : E → ℝ} (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) {xstar : E} (hmin : ∀ x, f xstar ≤ f x)
    {t₀ : ℝ} (ht₀ : 0 < t₀) {X V : ℝ → E}
    (hX : ∀ t ∈ Set.Ici t₀, HasDerivAt X (V t) t)
    (hV : ∀ t ∈ Set.Ici t₀, HasDerivAt V (-(3 / t) • V t - gradient f (X t)) t)
    {t : ℝ} (ht : t₀ ≤ t) :
    f (X t) - f xstar ≤
      (2 * ‖X t₀ + (t₀ / 2) • V t₀ - xstar‖ ^ 2 + t₀ ^ 2 * (f (X t₀) - f xstar)) / t ^ 2 := by
  set Z : ℝ → E := fun s => X s + (s / 2) • V s
  have hpos : ∀ s ∈ Set.Ici t₀, 0 < s := fun s hs => lt_of_lt_of_le ht₀ hs
  have hX' : ∀ s ∈ Set.Ici t₀, HasDerivAt X ((2 / s) • (Z s - X s)) s := by
    intro s hs
    have hs0 := (hpos s hs).ne'
    convert hX s hs using 1
    simp only [Z, add_sub_cancel_left, smul_smul]
    rw [show 2 / s * (s / 2) = 1 by field_simp, one_smul]
  have hZ' : ∀ s ∈ Set.Ici t₀,
      HasDerivAt Z (-((1 / 4 : ℝ) * 2 * s ^ ((2 : ℝ) - 1)) • gradient f (X s)) s := by
    intro s hs
    have hs0 := (hpos s hs).ne'
    have hd := (hX s hs).add (((hasDerivAt_id s).div_const 2).smul (hV s hs))
    refine HasDerivAt.congr_deriv (f := Z) hd ?_
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    simp only [id_eq, smul_sub, smul_smul]
    rw [show s / 2 * -(3 / s) = -(3 / 2) by field_simp]
    module
  have h := polynomialFamily_rate hconvex hdiff hmin (p := 2) (C := 1 / 4) (by norm_num)
    (by norm_num) ht₀ hX' hZ' ht
  have ht0' : (0 : ℝ) < t := lt_of_lt_of_le ht₀ ht
  rw [show t ^ (2 : ℝ) = t ^ 2 by norm_cast, show t₀ ^ (2 : ℝ) = t₀ ^ 2 by norm_cast] at h
  convert h using 1
  simp only [Z]
  field_simp
  ring

/-- **Time dilation of the Bregman-Lagrangian flow (Euclidean case).** Let `τ` be differentiable
at `t` with `τ' t > 0`, and suppose `(X, Z)` solves the Euler–Lagrange system for the parameters
`(α, β)` at time `τ t`: `X' = e^{α} (Z - X)` and `Z' = -e^{α + β} ∇f(X)` there. Then the
reparametrized curves `X ∘ τ`, `Z ∘ τ` solve the same system at `t` for the parameters
`α̃ = α ∘ τ + log τ'`, `β̃ = β ∘ τ`. Moreover the ideal scaling is preserved: if `β` has
derivative `β'` at `τ t` with `β' ≤ e^{α}` there, then `β ∘ τ` has derivative `β' (τ t) τ' t`
and `β' (τ t) τ' t ≤ e^{α̃ t}`.

Source: A. Wibisono, A. C. Wilson and M. I. Jordan, arXiv:1603.04245v1, Theorem 2.2 with the
modified parameters (2.10a)-(2.10b), stated here for the first-order form (2.7) of the
Euler–Lagrange equation with `h = ‖·‖² / 2` (the parameter `γ` only enters through the ideal
scaling (2.2b) that reduces (2.5) to (2.7)). -/
theorem timeDilation {f : E → ℝ} {α β τ : ℝ → ℝ} {X Z : ℝ → E} {t τ' : ℝ}
    (hτ : HasDerivAt τ τ' t) (hτpos : 0 < τ')
    (hX : HasDerivAt X (Real.exp (α (τ t)) • (Z (τ t) - X (τ t))) (τ t))
    (hZ : HasDerivAt Z (-Real.exp (α (τ t) + β (τ t)) • gradient f (X (τ t))) (τ t)) :
    HasDerivAt (X ∘ τ)
        (Real.exp (α (τ t) + Real.log τ') • ((Z ∘ τ) t - (X ∘ τ) t)) t ∧
      HasDerivAt (Z ∘ τ)
        (-Real.exp ((α (τ t) + Real.log τ') + β (τ t)) • gradient f ((X ∘ τ) t)) t := by
  have he : Real.exp (α (τ t) + Real.log τ') = τ' * Real.exp (α (τ t)) := by
    rw [Real.exp_add, Real.exp_log hτpos, mul_comm]
  have he' : Real.exp ((α (τ t) + Real.log τ') + β (τ t)) =
      τ' * Real.exp (α (τ t) + β (τ t)) := by
    rw [add_right_comm, Real.exp_add (α (τ t) + β (τ t)), Real.exp_log hτpos, mul_comm]
  refine ⟨?_, ?_⟩
  · have := hX.scomp t hτ
    simpa [he, smul_smul, Function.comp_def] using this
  · have := hZ.scomp t hτ
    simpa [he', smul_smul, Function.comp_def, neg_smul, smul_neg] using this

/-- **Time dilation preserves the ideal scaling.** If `τ` has derivative `τ' > 0` at `t` and `β`
has derivative `β'` at `τ t` with `β' ≤ e^{α (τ t)}` (eq. (2.2a)), then `β ∘ τ` has derivative
`β' τ'` at `t` and `β' τ' ≤ e^{α (τ t) + log τ'}`: the reparametrized parameters (2.10a)-(2.10b)
again satisfy (2.2a).

Source: A. Wibisono, A. C. Wilson and M. I. Jordan, arXiv:1603.04245v1, Theorem 2.2 (last
sentence: `α, β, γ` satisfy the ideal scaling if and only if the modified parameters do; the
direction proved here, for (2.2a)). -/
theorem timeDilation_idealScaling {α β τ : ℝ → ℝ} {t τ' β' : ℝ} (hτ : HasDerivAt τ τ' t)
    (hτpos : 0 < τ') (hβ : HasDerivAt β β' (τ t)) (hscale : β' ≤ Real.exp (α (τ t))) :
    HasDerivAt (β ∘ τ) (β' * τ') t ∧ β' * τ' ≤ Real.exp (α (τ t) + Real.log τ') := by
  refine ⟨hβ.comp t hτ, ?_⟩
  rw [Real.exp_add, Real.exp_log hτpos]
  exact mul_le_mul_of_nonneg_right hscale hτpos.le

end MathlibExt.Analysis.Convex.AcceleratedGradientFlow
