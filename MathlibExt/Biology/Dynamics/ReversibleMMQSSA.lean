/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten
public import MathlibExt.Biology.Dynamics.MichaelisMenten
import MathlibExt.Analysis.ODE.ComparisonBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Reversible Michaelis–Menten: a uniform quasi-steady-state error bound

For the reversible mechanism `E + S ⇌ C ⇌ E + P` (`ReversibleMichaelisMenten.IsSolution k₁ kb
k₂ kb₂ s c e p`, with `k₁, k₂ > 0` and `kb, kb₂ ≥ 0`), write `e_T = e(0) + c(0)` for the total
enzyme, `M = s(0) + c(0) + p(0)` for the total mass, `D = kb + k₂`, and `A = k₁ s + kb₂ p`. The
quasi-steady-state complex is `q(s, p) = e_T A / (A + D)` (`revQSSComplex`), and the reversible
Michaelis–Menten rate law is

  `v(s, p) = (k₁ k₂ s - kb kb₂ p) / (k₁ s + kb₂ p + kb + k₂)` (`revMMRate`).

The small parameter is `ε = e_T` and the slow time is `τ = ε t`. Along the reduced flow
`S̄ + P̄` is conserved, so the reduced (reversible Michaelis–Menten) equation in slow time is the
scalar equation `dS̄/dτ = -v(S̄, M - S̄)` (`reducedRate`), with `P̄ = M - S̄`.

## Main results

* `IsSolution.abs_complex_sub_qss_le` (real time, all `t ≥ 0`): the complex is slaved to the
  QSS manifold up to an initial-layer term,
  `|c(t) - q(s(t), p(t))| ≤ |c(0) - q(s(0), p(0))| e^{-(kb + k₂) t} + e_T² F / (kb + k₂)²`,
  with `F = complexForcingConst k₁ kb k₂ kb₂ M = k₁ (k₁ M + kb) + kb₂ (k₂ + kb₂ M)`.
* `reducedRate_mono`: the reduced rate is nondecreasing on `[0, M]`.
* `reduced_mem_Icc`: every solution of the reduced equation starting in `[0, M]` stays there.
* `IsSolution.abs_substrate_sub_reduced_le` (real time, all `t ≥ 0`): the substrate tracks
  the reduced solution on the slow clock,
  `|s(t) - S̄(e_T t)| ≤ |s(0) - S̄(0)| + (k₁ M + kb) (|c(0) - q(s(0), p(0))| / (kb + k₂)
  + (e_T² F / (kb + k₂)² + e_T² kb₂ / (kb + k₂)) t)`.
* `abs_substrate_sub_reduced_le_mul`, `abs_product_sub_reduced_le_mul`: for the standard data
  `s(0) = s₀ = S̄(0)`, `c(0) = 0`, `e(0) = ε`, `p(0) = p₀`, on the slow window `τ ∈ [0, T]`
  (**including** `τ = 0`), `|s(τ/ε) - S̄(τ)| ≤ revSubstrateErrorConst k₁ kb k₂ kb₂ (s₀ + p₀) T · ε`
  and `|p(τ/ε) - (s₀ + p₀ - S̄(τ))| ≤ (revSubstrateErrorConst … + 1) · ε`: the first-order
  uniform QSSA estimate for both the substrate and the product, with explicit constants.
* `revQSSComplex_zero`, `reducedRate_zero`: for `kb₂ = 0` the QSS complex and the reduced rate
  are the irreversible `qssComplex` and `mmRate k₂ K_M` of
  `MathlibExt.Biology.Dynamics.MichaelisMenten`.

No all-time QSSA is claimed: the constant grows linearly in the window length `T`. Existence of
a reduced solution through a given point is not proved here; the theorems quantify over reduced
solutions (the test file exhibits the constant one at the reduced equilibrium). Existence of
solutions of the full system is `ReversibleMichaelisMenten.exists_isSolution_nonneg`. The
rate-law error bound of the irreversible case (`MichaelisMenten.abs_rate_sub_mmRate_le` in
`MathlibExt.Biology.Dynamics.MichaelisMenten.UniformBound`) has no reversible counterpart here.

## Proofs

Let `w = c - q(s, p)`. Conservation `e = e_T - c` turns the complex equation into
`c' = -(A + D) w`, so `w' = -(A + D) w - q'` with decay rate `A + D ≥ D` and forcing
`|q'| = e_T D |A'| / (A + D)² ≤ e_T² F / D`; a comparison argument bounds `|w|`. The same
conservation gives `s' = -e_T v(s, p) + (k₁ s + kb) w`. Mass conservation gives
`p = M - s - c`, and since `v` is linear-fractional in `p`,
`|v(s, M - s) - v(s, p)| ≤ kb₂ (k₁ M + kb) e_T / D`. The reduced rate `x ↦ v(x, M - x)` is
linear-fractional with a nonnegative determinant `k₁ kb₂ M (kb + k₂) + (kb + k₂)(k₁ k₂ + kb kb₂)`,
hence nondecreasing on `[0, M]`, so the difference `d = s - S̄(e_T ·)` satisfies
`d' ≤ (k₁ M + kb) |w| + e_T² kb₂ (k₁ M + kb) / D` wherever `d ≥ 0` (and symmetrically); `|d|`
grows at most by the integral of that bound, with no Gronwall factor.

## Source receipt (API-00)

Reuse search (2026-11-15, base `origin/main` ca1b9e8001): `grep` for `QSSA`, `qss`,
`quasi-steady`, `reducedRate`, `revMMRate` over `MathlibExt`, `WantedExt`, `MathlibExtTest`.
Reused: `ReversibleMichaelisMenten.IsSolution`, `IsSolution.enzyme_conservation`,
`IsSolution.substrate_conservation`, `IsSolution.nonneg`, `revComplexRate`, `revProductRate`
(`MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten`); `substrateRate`, `qssComplex`,
`mmRate`, `michaelisConstant` (`MathlibExt.Biology.Dynamics.MichaelisMenten`); Mathlib
`image_le_of_deriv_right_lt_deriv_boundary'`. The comparison helpers `le_of_lt_on_eq`,
`abs_le_of_decay`, `abs_le_of_drift` come from `MathlibExt.Analysis.ODE.ComparisonBounds`,
shared with the irreversible bound `MathlibExt.Biology.Dynamics.MichaelisMenten.UniformBound`
(which covers only `kb₂ = 0`). `ReversibleMichaelisMenten` and its
`LaSalle` file prove equilibria and convergence, not a QSS approximation.

Mathematical source: the reversible rate law and its QSS derivation follow Cornish-Bowden,
*Fundamentals of Enzyme Kinetics*, ch. 2, and Keener–Sneyd §1.4; the slow-time scaling
`τ = e_T t` and the uniform `O(e_T)` estimate follow Heineken, Tsuchiya and Aris (1967) and
Segel and Slemrod (1989) (irreversible case). The constants and the monotonicity argument for
the reversible reduced rate are this file's own.

## References

* A. Cornish-Bowden, *Fundamentals of Enzyme Kinetics*, 4th ed., Wiley-Blackwell (2012), ch. 2.
* J. Keener and J. Sneyd, *Mathematical Physiology I: Cellular Physiology*, 2nd ed., Springer
  (2009), §1.4.
* F. G. Heineken, H. M. Tsuchiya and R. Aris, *On the mathematical status of the pseudo-steady
  state hypothesis of biochemical kinetics*, Math. Biosci. 1 (1967) 95–113.
* L. A. Segel and M. Slemrod, *The quasi-steady-state assumption: a case study in
  perturbation*, SIAM Rev. 31 (1989) 446–477.
-/

@[expose] public section

open Real Set

namespace MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten

open MathlibExt.Biology.Dynamics.MichaelisMenten
  (substrateRate qssComplex mmRate michaelisConstant)
open MathlibExt.Analysis.ODE.ComparisonBounds

/-! ### Definitions -/

/-- The quasi-steady-state complex of the reversible mechanism with total enzyme `eT`,
`q(s, p) = eT (k₁ s + kb₂ p) / (k₁ s + kb₂ p + kb + k₂)`. -/
noncomputable def revQSSComplex (k₁ kb k₂ kb₂ eT s p : ℝ) : ℝ :=
  eT * (k₁ * s + kb₂ * p) / (k₁ * s + kb₂ * p + (kb + k₂))

/-- The reversible Michaelis–Menten rate law (per unit total enzyme),
`v(s, p) = (k₁ k₂ s - kb kb₂ p) / (k₁ s + kb₂ p + kb + k₂)`. -/
noncomputable def revMMRate (k₁ kb k₂ kb₂ s p : ℝ) : ℝ :=
  (k₁ * k₂ * s - kb * kb₂ * p) / (k₁ * s + kb₂ * p + (kb + k₂))

/-- The rate of the reduced scalar equation `S̄' = -v(S̄, M - S̄)` with total mass `M`. -/
noncomputable def reducedRate (k₁ kb k₂ kb₂ M x : ℝ) : ℝ :=
  revMMRate k₁ kb k₂ kb₂ x (M - x)

/-- The forcing constant of the complex estimate, `k₁ (k₁ M + kb) + kb₂ (k₂ + kb₂ M)`. -/
def complexForcingConst (k₁ kb k₂ kb₂ M : ℝ) : ℝ :=
  k₁ * (k₁ * M + kb) + kb₂ * (k₂ + kb₂ * M)

/-- The constant of the substrate estimate on the slow window `[0, T]`:
`(k₁ M + kb) (1 / (kb + k₂) + (F / (kb + k₂)² + kb₂ / (kb + k₂)) T)`. -/
noncomputable def revSubstrateErrorConst (k₁ kb k₂ kb₂ M T : ℝ) : ℝ :=
  (k₁ * M + kb) * (1 / (kb + k₂) +
    (complexForcingConst k₁ kb k₂ kb₂ M / (kb + k₂) ^ 2 + kb₂ / (kb + k₂)) * T)

/-! ### Bridges to the irreversible mechanism -/

/-- For `kb₂ = 0` the QSS complex is the irreversible `qssComplex`. -/
theorem revQSSComplex_zero {k₁ kb k₂ eT s p : ℝ} (hk₁ : 0 < k₁) :
    revQSSComplex k₁ kb k₂ 0 eT s p = qssComplex k₁ kb k₂ eT s := by
  unfold revQSSComplex qssComplex michaelisConstant at *
  have h2 : k₁ * s + 0 * p + (kb + k₂) = k₁ * ((kb + k₂) / k₁ + s) := by field_simp; ring
  rw [h2]
  field_simp
  ring

/-- For `kb₂ = 0` the reduced rate is the irreversible rate law `mmRate k₂ K_M`. -/
theorem reducedRate_zero {k₁ kb k₂ M x : ℝ} (hk₁ : 0 < k₁) :
    reducedRate k₁ kb k₂ 0 M x = mmRate k₂ (michaelisConstant k₁ kb k₂) x := by
  unfold reducedRate revMMRate mmRate michaelisConstant at *
  have h2 : k₁ * x + 0 * (M - x) + (kb + k₂) = k₁ * ((kb + k₂) / k₁ + x) := by
    field_simp; ring
  rw [h2]
  field_simp
  ring

/-! ### Algebraic identities -/

/-- With `e = e_T - c`, the complex equation is `c' = -(A + D) (c - q(s, p))`. -/
private lemma revComplexRate_eq {k₁ kb k₂ kb₂ eT s c p : ℝ}
    (hA : k₁ * s + kb₂ * p + (kb + k₂) ≠ 0) :
    revComplexRate k₁ kb k₂ kb₂ s c (eT - c) p =
      -(k₁ * s + kb₂ * p + (kb + k₂)) * (c - revQSSComplex k₁ kb k₂ kb₂ eT s p) := by
  unfold revComplexRate MichaelisMenten.complexRate revQSSComplex
  field_simp
  ring

/-- With `e = e_T - c`, the substrate equation is `s' = -e_T v(s, p) + (k₁ s + kb) w`. -/
private lemma substrateRate_eq {k₁ kb k₂ kb₂ eT s c p : ℝ}
    (hA : k₁ * s + kb₂ * p + (kb + k₂) ≠ 0) :
    substrateRate k₁ kb s c (eT - c) =
      -(eT * revMMRate k₁ kb k₂ kb₂ s p) +
        (k₁ * s + kb) * (c - revQSSComplex k₁ kb k₂ kb₂ eT s p) := by
  unfold substrateRate revMMRate revQSSComplex
  field_simp
  ring

/-- Derivative of the QSS complex along a curve. -/
private lemma hasDerivAt_revQSSComplex_comp {k₁ kb k₂ kb₂ eT : ℝ} {s p : ℝ → ℝ}
    {s' p' t : ℝ} (hs : HasDerivAt s s' t) (hp : HasDerivAt p p' t)
    (hA : k₁ * s t + kb₂ * p t + (kb + k₂) ≠ 0) :
    HasDerivAt (fun r ↦ revQSSComplex k₁ kb k₂ kb₂ eT (s r) (p r))
      (eT * (kb + k₂) * (k₁ * s' + kb₂ * p') / (k₁ * s t + kb₂ * p t + (kb + k₂)) ^ 2) t := by
  unfold revQSSComplex
  have hA' := (hs.const_mul k₁).fun_add (hp.const_mul kb₂)
  convert HasDerivAt.div (hA'.const_mul eT) (hA'.add_const (kb + k₂)) hA using 1
  field_simp
  ring

/-- The reduced rate is nondecreasing on `[0, M]`. -/
theorem reducedRate_mono {k₁ kb k₂ kb₂ M : ℝ} (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂)
    (hkb₂ : 0 ≤ kb₂) {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x ≤ M) :
    reducedRate k₁ kb k₂ kb₂ M y ≤ reducedRate k₁ kb k₂ kb₂ M x := by
  unfold reducedRate revMMRate
  have hDx : 0 < k₁ * x + kb₂ * (M - x) + (kb + k₂) := by
    nlinarith [mul_nonneg hk₁ (hy.trans hyx), mul_nonneg hkb₂ (by linarith : 0 ≤ M - x)]
  have hDy : 0 < k₁ * y + kb₂ * (M - y) + (kb + k₂) := by
    nlinarith [mul_nonneg hk₁ hy, mul_nonneg hkb₂ (by linarith : 0 ≤ M - y)]
  rw [div_le_div_iff₀ hDy hDx]
  have hid : (k₁ * k₂ * x - kb * kb₂ * (M - x)) * (k₁ * y + kb₂ * (M - y) + (kb + k₂)) -
      (k₁ * k₂ * y - kb * kb₂ * (M - y)) * (k₁ * x + kb₂ * (M - x) + (kb + k₂)) =
      (k₁ * kb₂ * M * (kb + k₂) + (kb + k₂) * (k₁ * k₂ + kb * kb₂)) * (x - y) := by ring
  have hM : 0 ≤ M := hy.trans (hyx.trans hx)
  have hdet : 0 ≤ k₁ * kb₂ * M * (kb + k₂) + (kb + k₂) * (k₁ * k₂ + kb * kb₂) := by positivity
  nlinarith [mul_nonneg hdet (by linarith : 0 ≤ x - y)]

/-- The gap between the reduced rate at `s` and the rate law at the actual product
`p = M - s - c`: `|v(s, M - s) - v(s, p)| ≤ kb₂ (k₁ M + kb) e_T / (kb + k₂)`. -/
private lemma abs_reducedRate_sub_revMMRate_le {k₁ kb k₂ kb₂ M eT s c p : ℝ} (hk₁ : 0 ≤ k₁)
    (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hkb₂ : 0 ≤ kb₂) (hs : 0 ≤ s) (hsM : s ≤ M) (hc : 0 ≤ c)
    (hceT : c ≤ eT) (hp : 0 ≤ p) (hmass : s + c + p = M) :
    |reducedRate k₁ kb k₂ kb₂ M s - revMMRate k₁ kb k₂ kb₂ s p| ≤
      kb₂ * (k₁ * M + kb) * eT / (kb + k₂) := by
  have hD : 0 < kb + k₂ := by linarith
  have hD1 : kb + k₂ ≤ k₁ * s + kb₂ * (M - s) + (kb + k₂) := by
    nlinarith [mul_nonneg hk₁ hs, mul_nonneg hkb₂ (by linarith : 0 ≤ M - s)]
  have hD2 : kb + k₂ ≤ k₁ * s + kb₂ * p + (kb + k₂) := by
    nlinarith [mul_nonneg hk₁ hs, mul_nonneg hkb₂ hp]
  have hp' : p = M - s - c := by linarith
  unfold reducedRate revMMRate
  rw [div_sub_div _ _ (by linarith) (by linarith)]
  have hnum : (k₁ * k₂ * s - kb * kb₂ * (M - s)) * (k₁ * s + kb₂ * p + (kb + k₂)) -
      (k₁ * s + kb₂ * (M - s) + (kb + k₂)) * (k₁ * k₂ * s - kb * kb₂ * p) =
      -(kb₂ * (kb + k₂) * (k₁ * s + kb) * c) := by rw [hp']; ring
  rw [hnum, abs_div, abs_neg, abs_of_nonneg (by positivity),
    abs_of_pos (by positivity : (0 : ℝ) < (k₁ * s + kb₂ * (M - s) + (kb + k₂)) *
      (k₁ * s + kb₂ * p + (kb + k₂)))]
  have hnum_le : kb₂ * (kb + k₂) * (k₁ * s + kb) * c ≤ kb₂ * (kb + k₂) * (k₁ * M + kb) * eT := by
    have h1 : k₁ * s + kb ≤ k₁ * M + kb := by nlinarith [mul_le_mul_of_nonneg_left hsM hk₁]
    have h2 : (k₁ * s + kb) * c ≤ (k₁ * M + kb) * eT :=
      mul_le_mul h1 hceT hc (by nlinarith [mul_nonneg hk₁ (hs.trans hsM)])
    have h3 : 0 ≤ kb₂ * (kb + k₂) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 h3]
  calc kb₂ * (kb + k₂) * (k₁ * s + kb) * c /
        ((k₁ * s + kb₂ * (M - s) + (kb + k₂)) * (k₁ * s + kb₂ * p + (kb + k₂)))
      ≤ kb₂ * (kb + k₂) * (k₁ * M + kb) * eT / ((kb + k₂) * (kb + k₂)) :=
        div_le_div₀ ((by positivity : (0 : ℝ) ≤ kb₂ * (kb + k₂) * (k₁ * s + kb) * c).trans
          hnum_le) hnum_le (by positivity) (mul_le_mul hD1 hD2 hD.le (by linarith))
    _ = kb₂ * (k₁ * M + kb) * eT / (kb + k₂) := by field_simp

/-! ### The physical region -/

variable {k₁ kb k₂ kb₂ : ℝ} {s c e p : ℝ → ℝ}

/-- Bounds on the physical region: with nonnegative data, `0 ≤ s, p ≤ M`, `0 ≤ c, e ≤ e_T`. -/
private lemma IsSolution.region (h : IsSolution k₁ kb k₂ kb₂ s c e p) (hk₁ : 0 ≤ k₁)
    (hkb : 0 ≤ kb) (hk₂ : 0 ≤ k₂) (hkb₂ : 0 ≤ kb₂) (hs0 : 0 ≤ s 0) (hc0 : 0 ≤ c 0)
    (he0 : 0 ≤ e 0) (hp0 : 0 ≤ p 0) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ s t ∧ s t ≤ s 0 + c 0 + p 0 ∧ 0 ≤ c t ∧ c t ≤ e 0 + c 0 ∧ 0 ≤ e t ∧
      e t ≤ e 0 + c 0 ∧ 0 ≤ p t ∧ p t ≤ s 0 + c 0 + p 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h.nonneg hk₁ hkb hk₂ hkb₂ hs0 hc0 he0 hp0 ht
  have he := h.enzyme_conservation ht
  have hm := h.substrate_conservation ht
  refine ⟨h1, by linarith, h2, by linarith, h3, by linarith, h4, by linarith⟩

/-! ### The complex estimate (real time) -/

/-- **The complex is slaved to the QSS manifold**, for all `t ≥ 0`: with `e_T = e(0) + c(0)`,
`M = s(0) + c(0) + p(0)` and `F = complexForcingConst k₁ kb k₂ kb₂ M`,
`|c(t) - q(s(t), p(t))| ≤ |c(0) - q(s(0), p(0))| e^{-(kb + k₂) t} + e_T² F / (kb + k₂)²`. -/
theorem IsSolution.abs_complex_sub_qss_le (h : IsSolution k₁ kb k₂ kb₂ s c e p)
    (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hkb₂ : 0 ≤ kb₂) (hs0 : 0 ≤ s 0)
    (hc0 : 0 ≤ c 0) (he0 : 0 ≤ e 0) (hp0 : 0 ≤ p 0) {t : ℝ} (ht : 0 ≤ t) :
    |c t - revQSSComplex k₁ kb k₂ kb₂ (e 0 + c 0) (s t) (p t)| ≤
      |c 0 - revQSSComplex k₁ kb k₂ kb₂ (e 0 + c 0) (s 0) (p 0)| * exp (-(kb + k₂) * t) +
        (e 0 + c 0) ^ 2 * complexForcingConst k₁ kb k₂ kb₂ (s 0 + c 0 + p 0) /
          (kb + k₂) ^ 2 := by
  set eT := e 0 + c 0 with heTdef
  set M := s 0 + c 0 + p 0 with hMdef
  set F := complexForcingConst k₁ kb k₂ kb₂ M with hFdef
  set D := kb + k₂ with hDdef
  have hD : 0 < D := by linarith
  have heT : 0 ≤ eT := by positivity
  have hM : 0 ≤ M := by positivity
  have hreg := fun r (hr : 0 ≤ r) ↦ h.region hk₁ hkb hk₂.le hkb₂ hs0 hc0 he0 hp0 hr
  have hApos : ∀ r, 0 ≤ r → D ≤ k₁ * s r + kb₂ * p r + D := fun r hr ↦ by
    obtain ⟨h1, -, -, -, -, -, h7, -⟩ := hreg r hr
    nlinarith [mul_nonneg hk₁ h1, mul_nonneg hkb₂ h7]
  have hrw : eT ^ 2 * F / D ^ 2 = eT ^ 2 * F / D / D := by rw [div_div, ← sq]
  rw [hrw]
  refine abs_le_of_decay (w := fun r ↦ c r - revQSSComplex k₁ kb k₂ kb₂ eT (s r) (p r))
    (a := fun r ↦ k₁ * s r + kb₂ * p r + D)
    (g := fun r ↦ -(eT * D * (k₁ * substrateRate k₁ kb (s r) (c r) (e r) +
      kb₂ * revProductRate k₂ kb₂ (c r) (e r) (p r)) / (k₁ * s r + kb₂ * p r + D) ^ 2))
    hD ?_ hApos ?_ ht
  · intro r hr
    have hA : k₁ * s r + kb₂ * p r + D ≠ 0 := by linarith [hApos r hr]
    have hcons := h.enzyme_conservation hr
    have he : e r = eT - c r := by linarith
    refine ((h.hasDerivAt_complex r hr).sub
      (hasDerivAt_revQSSComplex_comp (eT := eT) (h.hasDerivAt_substrate r hr)
        (h.hasDerivAt_product r hr) hA)).congr_deriv ?_
    rw [he, revComplexRate_eq hA]
    ring
  · intro r hr
    obtain ⟨hs1, hs2, hc1, hc2, he1, he2, hp1, hp2⟩ := hreg r hr
    set A := k₁ * s r + kb₂ * p r + D with hAdef
    have hAD := hApos r hr
    set u := k₁ * substrateRate k₁ kb (s r) (c r) (e r) +
      kb₂ * revProductRate k₂ kb₂ (c r) (e r) (p r) with hu
    have hes : e r * s r ≤ eT * M := mul_le_mul he2 hs2 hs1 heT
    have hep : e r * p r ≤ eT * M := mul_le_mul he2 hp2 hp1 heT
    have hS : |substrateRate k₁ kb (s r) (c r) (e r)| ≤ eT * (k₁ * M + kb) := by
      unfold substrateRate
      rw [abs_le]
      constructor
      · nlinarith [mul_nonneg hkb hc1, mul_le_mul_of_nonneg_left hes hk₁]
      · nlinarith [mul_nonneg hk₁ (mul_nonneg he1 hs1), mul_le_mul_of_nonneg_left hc2 hkb,
          mul_nonneg hk₁ (mul_nonneg heT hM)]
    have hP : |revProductRate k₂ kb₂ (c r) (e r) (p r)| ≤ eT * (k₂ + kb₂ * M) := by
      unfold revProductRate
      rw [abs_le]
      constructor
      · nlinarith [mul_nonneg hk₂.le hc1, mul_le_mul_of_nonneg_left hep hkb₂]
      · nlinarith [mul_nonneg hkb₂ (mul_nonneg he1 hp1), mul_le_mul_of_nonneg_left hc2 hk₂.le,
          mul_nonneg hkb₂ (mul_nonneg heT hM)]
    have hu_le : |u| ≤ eT * F := by
      rw [hu, hFdef]
      unfold complexForcingConst
      calc |k₁ * substrateRate k₁ kb (s r) (c r) (e r) +
            kb₂ * revProductRate k₂ kb₂ (c r) (e r) (p r)|
          ≤ |k₁ * substrateRate k₁ kb (s r) (c r) (e r)| +
            |kb₂ * revProductRate k₂ kb₂ (c r) (e r) (p r)| := abs_add_le _ _
        _ = k₁ * |substrateRate k₁ kb (s r) (c r) (e r)| +
            kb₂ * |revProductRate k₂ kb₂ (c r) (e r) (p r)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hk₁, abs_of_nonneg hkb₂]
        _ ≤ k₁ * (eT * (k₁ * M + kb)) + kb₂ * (eT * (k₂ + kb₂ * M)) := by gcongr
        _ = eT * (k₁ * (k₁ * M + kb) + kb₂ * (k₂ + kb₂ * M)) := by ring
    have hApos' : 0 < A := by linarith
    rw [abs_neg, abs_div, abs_mul, abs_mul, abs_of_nonneg heT, abs_of_pos hD,
      abs_of_pos (pow_pos hApos' 2)]
    calc eT * D * |u| / A ^ 2 ≤ eT * D * |u| / D ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (pow_pos hD 2)
          rw [sq, sq]; exact mul_le_mul hAD hAD hD.le hApos'.le
      _ = eT * |u| / D := by field_simp
      _ ≤ eT * (eT * F) / D := by gcongr
      _ = eT ^ 2 * F / D := by ring

/-! ### Forward invariance of `[0, M]` for the reduced equation -/

/-- A small slack `δ ≤ ε` with `k₁ δ < k₂` and `kb₂ δ < k₂`. -/
private lemma exists_small_delta {k₁ k₂ kb₂ ε : ℝ} (hk₁ : 0 ≤ k₁) (hk₂ : 0 < k₂)
    (hkb₂ : 0 ≤ kb₂) (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ ≤ ε ∧ k₁ * δ < k₂ ∧ kb₂ * δ < k₂ := by
  set m := 2 * (k₁ + kb₂ + 1) with hm
  have hmpos : 0 < m := by positivity
  refine ⟨min ε (k₂ / m), lt_min hε (div_pos hk₂ hmpos), min_le_left _ _, ?_, ?_⟩
  all_goals
    have h1 : min ε (k₂ / m) * m ≤ k₂ := by
      calc min ε (k₂ / m) * m ≤ k₂ / m * m := by gcongr; exact min_le_right _ _
        _ = k₂ := by field_simp
    have h2 : 0 < min ε (k₂ / m) := lt_min hε (div_pos hk₂ hmpos)
    nlinarith

/-- **The reduced equation keeps `[0, M]` invariant**: a solution of `S̄' = -v(S̄, M - S̄)` with
`S̄(0) ∈ [0, M]` stays in `[0, M]` for all `τ ≥ 0`. -/
theorem reduced_mem_Icc (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hkb₂ : 0 ≤ kb₂)
    {M : ℝ} (hM : 0 ≤ M) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-reducedRate k₁ kb k₂ kb₂ M (S τ)) τ)
    (hS0 : S 0 ∈ Icc 0 M) {τ : ℝ} (hτ : 0 ≤ τ) : S τ ∈ Icc 0 M := by
  constructor
  · have key : ∀ ε, 0 < ε → 0 ≤ S τ + ε := by
      intro ε hε
      obtain ⟨δ, hδ, hδε, hk₁δ, -⟩ := exists_small_delta hk₁.le hk₂ hkb₂ hε
      have := le_of_lt_on_eq (T := τ) (f := fun r ↦ -S r)
        (f' := fun r ↦ reducedRate k₁ kb k₂ kb₂ M (S r))
        (B := fun _ ↦ δ) (B' := fun _ ↦ 0)
        (fun r hr ↦ (hS r hr.1).neg.congr_deriv (neg_neg _)) (fun r _ ↦ hasDerivAt_const r δ)
        (by linarith [hS0.1]) ?_ τ ⟨hτ, le_rfl⟩
      · linarith
      · intro r _ heq
        have hSr : S r = -δ := by linarith
        rw [hSr]
        unfold reducedRate revMMRate
        apply div_neg_of_neg_of_pos
        · nlinarith [mul_pos (mul_pos hk₁ hk₂) hδ, mul_nonneg (mul_nonneg hkb hkb₂)
            (by linarith : 0 ≤ M - -δ)]
        · nlinarith [mul_nonneg hkb₂ (by linarith : 0 ≤ M - -δ)]
    by_contra hneg
    push Not at hneg
    linarith [key (-S τ / 2) (by linarith)]
  · have key : ∀ ε, 0 < ε → S τ ≤ M + ε := by
      intro ε hε
      obtain ⟨δ, hδ, hδε, -, hkb₂δ⟩ := exists_small_delta hk₁.le hk₂ hkb₂ hε
      have := le_of_lt_on_eq (T := τ) (f := S)
        (f' := fun r ↦ -reducedRate k₁ kb k₂ kb₂ M (S r))
        (B := fun _ ↦ M + δ) (B' := fun _ ↦ 0)
        (fun r hr ↦ hS r hr.1) (fun r _ ↦ hasDerivAt_const r (M + δ))
        (by linarith [hS0.2]) ?_ τ ⟨hτ, le_rfl⟩
      · linarith
      · intro r _ heq
        rw [heq]
        unfold reducedRate revMMRate
        rw [neg_lt_zero]
        apply div_pos
        · nlinarith [mul_pos (mul_pos hk₁ hk₂) (by linarith : 0 < M + δ),
            mul_nonneg (mul_nonneg hkb hkb₂) hδ.le]
        · nlinarith [mul_pos hk₁ (by linarith : 0 < M + δ)]
    exact le_of_forall_pos_le_add key

/-! ### The substrate estimate (real time) -/

/-- **The substrate tracks the reduced solution on the slow clock**, for all `t ≥ 0`: with
`e_T = e(0) + c(0)`, `M = s(0) + c(0) + p(0)`, `F = complexForcingConst k₁ kb k₂ kb₂ M`, and
`S̄` a solution of `S̄' = -v(S̄, M - S̄)` with `S̄(0) ∈ [0, M]`,
`|s(t) - S̄(e_T t)| ≤ |s(0) - S̄(0)| + (k₁ M + kb) (|c(0) - q(s(0), p(0))| / (kb + k₂) +
(e_T² F / (kb + k₂)² + e_T² kb₂ / (kb + k₂)) t)`. -/
theorem IsSolution.abs_substrate_sub_reduced_le (h : IsSolution k₁ kb k₂ kb₂ s c e p)
    (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hkb₂ : 0 ≤ kb₂) (hs0 : 0 ≤ s 0)
    (hc0 : 0 ≤ c 0) (he0 : 0 ≤ e 0) (hp0 : 0 ≤ p 0) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ →
      HasDerivAt S (-reducedRate k₁ kb k₂ kb₂ (s 0 + c 0 + p 0) (S τ)) τ)
    (hS0 : S 0 ∈ Icc 0 (s 0 + c 0 + p 0)) {t : ℝ} (ht : 0 ≤ t) :
    |s t - S ((e 0 + c 0) * t)| ≤ |s 0 - S 0| + (k₁ * (s 0 + c 0 + p 0) + kb) *
      (|c 0 - revQSSComplex k₁ kb k₂ kb₂ (e 0 + c 0) (s 0) (p 0)| / (kb + k₂) +
        ((e 0 + c 0) ^ 2 * complexForcingConst k₁ kb k₂ kb₂ (s 0 + c 0 + p 0) /
          (kb + k₂) ^ 2 + (e 0 + c 0) ^ 2 * kb₂ / (kb + k₂)) * t) := by
  have hw := fun r (hr : 0 ≤ r) ↦
    h.abs_complex_sub_qss_le hk₁.le hkb hk₂ hkb₂ hs0 hc0 he0 hp0 hr
  have hreg := fun r (hr : 0 ≤ r) ↦ h.region hk₁.le hkb hk₂.le hkb₂ hs0 hc0 he0 hp0 hr
  set eT := e 0 + c 0 with heTdef
  set M := s 0 + c 0 + p 0 with hMdef
  set F := complexForcingConst k₁ kb k₂ kb₂ M with hFdef
  set D := kb + k₂ with hDdef
  set w0 := |c 0 - revQSSComplex k₁ kb k₂ kb₂ eT (s 0) (p 0)|
  set Mc := k₁ * M + kb with hMcdef
  set L := eT ^ 2 * F / D ^ 2 + eT ^ 2 * kb₂ / D with hLdef
  have heT : 0 ≤ eT := by positivity
  have hD : 0 < D := by linarith
  have hM : 0 ≤ M := by positivity
  have hF : 0 ≤ F := by rw [hFdef]; unfold complexForcingConst; positivity
  have hMc : 0 ≤ Mc := by positivity
  have hL : 0 ≤ L := by positivity
  have hw0 : 0 ≤ w0 := abs_nonneg _
  have hSmem := fun r (hr : 0 ≤ r) ↦ reduced_mem_Icc hk₁ hkb hk₂ hkb₂ hM hS hS0 hr
  have hSr : ∀ r, 0 ≤ r → HasDerivAt (fun u ↦ S (eT * u))
      (-reducedRate k₁ kb k₂ kb₂ M (S (eT * r)) * (eT * 1)) r :=
    fun r hr ↦ (hS (eT * r) (by positivity)).comp r ((hasDerivAt_id' r).const_mul eT)
  -- the pointwise drift bound shared by both signs
  have hcore : ∀ r, 0 ≤ r →
      |eT * (reducedRate k₁ kb k₂ kb₂ M (s r) - revMMRate k₁ kb k₂ kb₂ (s r) (p r)) +
        (k₁ * s r + kb) * (c r - revQSSComplex k₁ kb k₂ kb₂ eT (s r) (p r))| ≤
        Mc * (w0 * exp (-D * r) + L) := by
    intro r hr
    obtain ⟨hs1, hs2, hc1, hc2, -, -, hp1, -⟩ := hreg r hr
    have hmass := h.substrate_conservation hr
    have hg := abs_reducedRate_sub_revMMRate_le hk₁.le hkb hk₂ hkb₂ hs1 hs2 hc1 hc2 hp1
      hmass
    have hcoef : 0 ≤ k₁ * s r + kb := by nlinarith
    have hcoef2 : k₁ * s r + kb ≤ Mc := by nlinarith
    have h2 := mul_le_mul hcoef2 (hw r hr) (abs_nonneg _) hMc
    calc _ ≤ |eT * (reducedRate k₁ kb k₂ kb₂ M (s r) - revMMRate k₁ kb k₂ kb₂ (s r) (p r))| +
          |(k₁ * s r + kb) * (c r - revQSSComplex k₁ kb k₂ kb₂ eT (s r) (p r))| :=
          abs_add_le _ _
      _ = eT * |reducedRate k₁ kb k₂ kb₂ M (s r) - revMMRate k₁ kb k₂ kb₂ (s r) (p r)| +
          (k₁ * s r + kb) * |c r - revQSSComplex k₁ kb k₂ kb₂ eT (s r) (p r)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg heT, abs_of_nonneg hcoef]
      _ ≤ eT * (kb₂ * Mc * eT / D) +
          Mc * (w0 * exp (-D * r) + eT ^ 2 * F / D ^ 2) := by
          gcongr
      _ = Mc * (w0 * exp (-D * r) + L) := by rw [hLdef]; ring
  have key := abs_le_of_drift (d := fun r ↦ s r - S (eT * r))
    (d' := fun r ↦ substrateRate k₁ kb (s r) (c r) (e r) -
      -reducedRate k₁ kb k₂ kb₂ M (S (eT * r)) * (eT * 1))
    (H := fun r ↦ Mc * (w0 * (1 - exp (-D * r)) / D + L * r))
    (h := fun r ↦ Mc * (w0 * exp (-D * r) + L))
    (fun r hr ↦ (h.hasDerivAt_substrate r hr).sub (hSr r hr)) ?_ (by simp) ?_ ?_ ?_ ht
  · have hexp : 0 < exp (-D * t) := exp_pos _
    have h1 : w0 * (1 - exp (-D * t)) / D ≤ w0 / D :=
      div_le_div_of_nonneg_right (by nlinarith) hD.le
    have h2 := mul_le_mul_of_nonneg_left (add_le_add_left h1 (L * t)) hMc
    simp only [mul_zero] at key
    have hLt : L * t = (eT ^ 2 * F / D ^ 2 + eT ^ 2 * kb₂ / D) * t := by rw [hLdef]
    rw [← hLt]
    linarith
  · intro r _
    have e1 := ((hasDerivAt_id' r).const_mul (-D)).exp
    have e2 := ((((e1.const_sub 1).const_mul w0).div_const D).add
      ((hasDerivAt_id' r).const_mul L)).const_mul Mc
    convert e2 using 1
    field_simp
  · intro r hr
    have : exp (-D * r) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
    have : 0 ≤ w0 * (1 - exp (-D * r)) / D :=
      div_nonneg (mul_nonneg hw0 (by linarith)) hD.le
    have : 0 ≤ L * r := mul_nonneg hL hr
    positivity
  · intro r hr hd
    obtain ⟨hs1, hs2, -, -, -, -, hp1, -⟩ := hreg r hr
    have hcons := h.enzyme_conservation hr
    have he : e r = eT - c r := by linarith
    have hA : k₁ * s r + kb₂ * p r + D ≠ 0 := by
      nlinarith [mul_nonneg hk₁.le hs1, mul_nonneg hkb₂ hp1]
    rw [he, substrateRate_eq hA]
    have hm : reducedRate k₁ kb k₂ kb₂ M (S (eT * r)) ≤ reducedRate k₁ kb k₂ kb₂ M (s r) :=
      reducedRate_mono hk₁.le hkb hk₂ hkb₂ (hSmem _ (by positivity)).1 (by linarith) hs2
    calc _ = (eT * (reducedRate k₁ kb k₂ kb₂ M (s r) - revMMRate k₁ kb k₂ kb₂ (s r) (p r)) +
          (k₁ * s r + kb) * (c r - revQSSComplex k₁ kb k₂ kb₂ eT (s r) (p r))) -
          eT * (reducedRate k₁ kb k₂ kb₂ M (s r) -
            reducedRate k₁ kb k₂ kb₂ M (S (eT * r))) := by ring
      _ ≤ eT * (reducedRate k₁ kb k₂ kb₂ M (s r) - revMMRate k₁ kb k₂ kb₂ (s r) (p r)) +
          (k₁ * s r + kb) * (c r - revQSSComplex k₁ kb k₂ kb₂ eT (s r) (p r)) :=
          sub_le_self _ (mul_nonneg heT (sub_nonneg.2 hm))
      _ ≤ _ := (le_abs_self _).trans (hcore r hr)
  · intro r hr hd
    obtain ⟨hs1, -, -, -, -, -, hp1, -⟩ := hreg r hr
    have hcons := h.enzyme_conservation hr
    have he : e r = eT - c r := by linarith
    have hA : k₁ * s r + kb₂ * p r + D ≠ 0 := by
      nlinarith [mul_nonneg hk₁.le hs1, mul_nonneg hkb₂ hp1]
    rw [he, substrateRate_eq hA]
    have hm : reducedRate k₁ kb k₂ kb₂ M (s r) ≤ reducedRate k₁ kb k₂ kb₂ M (S (eT * r)) :=
      reducedRate_mono hk₁.le hkb hk₂ hkb₂ hs1 (by linarith) (hSmem _ (by positivity)).2
    calc _ = -(eT * (reducedRate k₁ kb k₂ kb₂ M (s r) - revMMRate k₁ kb k₂ kb₂ (s r) (p r)) +
          (k₁ * s r + kb) * (c r - revQSSComplex k₁ kb k₂ kb₂ eT (s r) (p r))) -
          eT * (reducedRate k₁ kb k₂ kb₂ M (S (eT * r)) -
            reducedRate k₁ kb k₂ kb₂ M (s r)) := by ring
      _ ≤ -(eT * (reducedRate k₁ kb k₂ kb₂ M (s r) - revMMRate k₁ kb k₂ kb₂ (s r) (p r)) +
          (k₁ * s r + kb) * (c r - revQSSComplex k₁ kb k₂ kb₂ eT (s r) (p r))) :=
          sub_le_self _ (mul_nonneg heT (sub_nonneg.2 hm))
      _ ≤ _ := (neg_le_abs _).trans (hcore r hr)

/-! ### Standard data: the uniform first-order estimate on a slow window -/

/-- For the standard data `c(0) = 0`, the initial distance to the QSS manifold is at most the
total enzyme `ε`. -/
private lemma revQSSComplex_le {k₁ kb k₂ kb₂ ε s p : ℝ} (hk₁ : 0 ≤ k₁) (hkb : 0 ≤ kb)
    (hk₂ : 0 < k₂) (hkb₂ : 0 ≤ kb₂) (hε : 0 ≤ ε) (hs : 0 ≤ s) (hp : 0 ≤ p) :
    |0 - revQSSComplex k₁ kb k₂ kb₂ ε s p| ≤ ε := by
  unfold revQSSComplex
  have hA : 0 ≤ k₁ * s + kb₂ * p := by positivity
  have hAD : 0 < k₁ * s + kb₂ * p + (kb + k₂) := by linarith
  rw [zero_sub, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ hAD]
  nlinarith [mul_nonneg hε (by linarith : 0 ≤ kb + k₂)]

/-- **Uniform QSSA for the substrate on a slow window, including `τ = 0`.** For the standard
data `s(0) = s₀ = S̄(0)`, `c(0) = 0`, `e(0) = ε > 0`, `p(0) = p₀ ≥ 0`, with `S̄` a solution of the
reduced equation `S̄' = -v(S̄, s₀ + p₀ - S̄)`,
`|s(τ/ε) - S̄(τ)| ≤ revSubstrateErrorConst k₁ kb k₂ kb₂ (s₀ + p₀) T · ε` for all
`τ ∈ [0, T]`. -/
theorem abs_substrate_sub_reduced_le_mul (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂)
    (hkb₂ : 0 ≤ kb₂) {s₀ p₀ ε T : ℝ} (hs₀ : 0 ≤ s₀) (hp₀ : 0 ≤ p₀) (hε : 0 < ε)
    (h : IsSolution k₁ kb k₂ kb₂ s c e p) (hs0 : s 0 = s₀) (hc0 : c 0 = 0) (he0 : e 0 = ε)
    (hp0 : p 0 = p₀) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-reducedRate k₁ kb k₂ kb₂ (s₀ + p₀) (S τ)) τ)
    (hS0 : S 0 = s₀) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    |s (τ / ε) - S τ| ≤ revSubstrateErrorConst k₁ kb k₂ kb₂ (s₀ + p₀) T * ε := by
  have hM : s 0 + c 0 + p 0 = s₀ + p₀ := by rw [hs0, hc0, hp0]; ring
  have heT : e 0 + c 0 = ε := by rw [he0, hc0]; ring
  have htau : 0 ≤ τ / ε := div_nonneg hτ.1 hε.le
  have key := h.abs_substrate_sub_reduced_le hk₁ hkb hk₂ hkb₂ (by rw [hs0]; exact hs₀)
    (by rw [hc0]) (by rw [he0]; exact hε.le) (by rw [hp0]; exact hp₀) (S := S)
    (by rw [hM]; exact hS) (by rw [hM, hS0]; exact ⟨hs₀, by linarith⟩) htau
  rw [hM, heT, hs0, hc0, hp0, hS0, sub_self, abs_zero, zero_add,
    mul_div_cancel₀ τ hε.ne'] at key
  have hw0 := revQSSComplex_le hk₁.le hkb hk₂ hkb₂ hε.le hs₀ hp₀ (k₁ := k₁)
  set w0 := |0 - revQSSComplex k₁ kb k₂ kb₂ ε s₀ p₀|
  set F := complexForcingConst k₁ kb k₂ kb₂ (s₀ + p₀) with hFdef
  have hD : 0 < kb + k₂ := by linarith
  have hF : 0 ≤ F := by rw [hFdef]; unfold complexForcingConst; positivity
  have hMc : 0 ≤ k₁ * (s₀ + p₀) + kb := by positivity
  have hG : 0 ≤ F / (kb + k₂) ^ 2 + kb₂ / (kb + k₂) := by positivity
  refine key.trans ?_
  unfold revSubstrateErrorConst
  rw [← hFdef]
  have hrw : (ε ^ 2 * F / (kb + k₂) ^ 2 + ε ^ 2 * kb₂ / (kb + k₂)) * (τ / ε) =
      ε * ((F / (kb + k₂) ^ 2 + kb₂ / (kb + k₂)) * τ) := by field_simp
  rw [hrw]
  have h1 : w0 / (kb + k₂) ≤ ε * (1 / (kb + k₂)) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right hw0 hD.le
  have h2 : ε * ((F / (kb + k₂) ^ 2 + kb₂ / (kb + k₂)) * τ) ≤
      ε * ((F / (kb + k₂) ^ 2 + kb₂ / (kb + k₂)) * T) := by
    gcongr; exact hτ.2
  calc (k₁ * (s₀ + p₀) + kb) *
        (w0 / (kb + k₂) + ε * ((F / (kb + k₂) ^ 2 + kb₂ / (kb + k₂)) * τ))
      ≤ (k₁ * (s₀ + p₀) + kb) *
        (ε * (1 / (kb + k₂)) + ε * ((F / (kb + k₂) ^ 2 + kb₂ / (kb + k₂)) * T)) := by
        gcongr
    _ = _ := by ring

/-- **Uniform QSSA for the product on a slow window, including `τ = 0`.** For the standard data
of `abs_substrate_sub_reduced_le_mul`, the product tracks the reduced product
`P̄ = s₀ + p₀ - S̄`: `|p(τ/ε) - (s₀ + p₀ - S̄(τ))| ≤
(revSubstrateErrorConst k₁ kb k₂ kb₂ (s₀ + p₀) T + 1) · ε` for all `τ ∈ [0, T]`. -/
theorem abs_product_sub_reduced_le_mul (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂)
    (hkb₂ : 0 ≤ kb₂) {s₀ p₀ ε T : ℝ} (hs₀ : 0 ≤ s₀) (hp₀ : 0 ≤ p₀) (hε : 0 < ε)
    (h : IsSolution k₁ kb k₂ kb₂ s c e p) (hs0 : s 0 = s₀) (hc0 : c 0 = 0) (he0 : e 0 = ε)
    (hp0 : p 0 = p₀) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-reducedRate k₁ kb k₂ kb₂ (s₀ + p₀) (S τ)) τ)
    (hS0 : S 0 = s₀) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    |p (τ / ε) - (s₀ + p₀ - S τ)| ≤
      (revSubstrateErrorConst k₁ kb k₂ kb₂ (s₀ + p₀) T + 1) * ε := by
  have hsub := abs_substrate_sub_reduced_le_mul hk₁ hkb hk₂ hkb₂ hs₀ hp₀ hε h hs0 hc0 he0 hp0
    hS hS0 hτ
  have htau : 0 ≤ τ / ε := div_nonneg hτ.1 hε.le
  obtain ⟨-, -, hc1, hc2, -, -, -, -⟩ := h.region hk₁.le hkb hk₂.le hkb₂
    (by rw [hs0]; exact hs₀) (by rw [hc0]) (by rw [he0]; exact hε.le)
    (by rw [hp0]; exact hp₀) htau
  have hmass := h.substrate_conservation htau
  rw [hs0, hc0, hp0] at hmass
  rw [he0, hc0] at hc2
  have hp : p (τ / ε) - (s₀ + p₀ - S τ) = -(s (τ / ε) - S τ) - c (τ / ε) := by linarith
  rw [hp]
  calc |-(s (τ / ε) - S τ) - c (τ / ε)| ≤ |s (τ / ε) - S τ| + |c (τ / ε)| := by
        rw [sub_eq_add_neg]
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_neg]
    _ ≤ revSubstrateErrorConst k₁ kb k₂ kb₂ (s₀ + p₀) T * ε + ε := by
        rw [abs_of_nonneg hc1]; linarith
    _ = _ := by ring

end MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten
