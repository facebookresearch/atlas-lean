/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.MichaelisMenten
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Michaelis–Menten: a uniform quasi-steady-state error bound

For the mechanism `E + S ⇌ C → E + P` (`IsSolution k₁ kb k₂ s c e p`, with `k₁, k₂ > 0`,
`kb ≥ 0`), write `e_T = e(0) + c(0)` for the total enzyme, `s_T = s(0) + c(0)`,
`K = K_M = (kb + k₂)/k₁` and `q(s) = e_T s / (K + s)` for the quasi-steady-state complex. The
small parameter is `ε = e_T`, and the slow time is `τ = ε t` (Heineken, Tsuchiya and Aris). The
reduced (Michaelis–Menten) equation in slow time is `dS̄/dτ = -k₂ S̄ / (K + S̄)`, i.e.
`S̄' = -mmRate k₂ K S̄`.

## Main results

All bounds are explicit in `ε` and the rate constants, and every statement names its time
window.

* `IsSolution.substrate_pos`, `IsSolution.complex_nonneg`, `IsSolution.complex_le`,
  `IsSolution.substrate_le`: the physical region is forward invariant, `s > 0`,
  `0 ≤ c ≤ e_T`, `s ≤ s_T`, for `s(0) > 0`, `c(0), e(0) ≥ 0`.
* `exists_reduced_solution`, `reduced_pos`: the reduced equation has a positive solution
  through every `s₀ > 0` (`S̄(τ) = Φ⁻¹(Φ(s₀) - k₂ τ)`, `Φ(x) = x + K log x`), and every solution
  with `S̄(0) > 0` stays positive.
* `IsSolution.abs_complex_sub_qss_le` (real time, all `t ≥ 0`): the complex is slaved to the
  QSS manifold up to an initial-layer term,
  `|c(t) - q(s(t))| ≤ |c(0) - q(s(0))| e^{-(kb + k₂) t} + e_T² (k₁ s_T + kb) / (K (kb + k₂))`.
* `IsSolution.abs_substrate_sub_reduced_le` (real time): the substrate tracks the reduced
  solution run on the slow clock, `|s(t) - S̄(e_T t)| ≤ |s(0) - S̄(0)| + (k₁ s_T + kb)
  (|c(0) - q(s(0))| / (kb + k₂) + e_T² (k₁ s_T + kb) / (K (kb + k₂)) · t)`.
* `abs_substrate_sub_reduced_le_mul`, `exists_abs_substrate_sub_reduced_le`: for the standard
  data `s(0) = s₀ = S̄(0)`, `c(0) = 0`, `e(0) = ε`, on the slow window `τ ∈ [0, T]`
  (**including** `τ = 0`; the substrate has no initial layer),
  `|s(τ/ε) - S̄(τ)| ≤ substrateErrorConst k₁ kb k₂ s₀ T · ε`. This is the first-order Tikhonov
  estimate recorded as `abs_sub_reduced_le` in
  `WantedExt.Biology.Dynamics.MichaelisMentenQSSAWanted`, with an explicit constant.
* `abs_rate_sub_mmRate_le`: for the same data, on the slow window `τ ∈ [τ₀, T]`, the
  slow-time product rate `dP/dτ = k₂ c(τ/ε)/ε` obeys
  `|k₂ c(τ/ε)/ε - mmRate k₂ K (S̄ τ)| ≤ rateErrorBound k₁ kb k₂ s₀ T τ₀ ε
  = k₂ (e^{-(kb + k₂) τ₀ / ε} + ε (…))`. The initial layer is the term
  `e^{-(kb + k₂) τ₀ / ε}`: it tends to `0` only for `τ₀ > 0` (`tendsto_rateErrorBound`).
* `abs_rate_sub_mmRate_le_of_prepared`: for prepared data `c(0) = q(s₀)` the initial-layer
  term vanishes and the rate-law error is `≤ preparedRateBound k₁ kb k₂ s₀ T ε`, `O(ε)`
  uniformly on `[0, T]` **including** `τ = 0` (`tendsto_preparedRateBound`).
* `tendsto_substrate_of_family`, `tendsto_rate_of_family`: along any family of solutions
  with standard data, `s_ε(τ/ε) → S̄(τ)` for `τ ≥ 0` and the slow-time product rate tends to
  the Michaelis–Menten rate law `mmRate k₂ K (S̄ τ)` for `τ > 0`, as `ε → 0⁺`.

No all-time QSSA is claimed: the substrate constant grows linearly in the window length `T`,
and without prepared data the rate-law bound needs `τ ≥ τ₀ > 0`. The test file shows that at
`τ = 0` with `c(0) = 0` the rate-law error equals `mmRate k₂ K s₀ > 0` for every `ε`.

## Proofs

Let `w = c - q(s)`. Conservation `e = e_T - c` turns the complex equation into
`c' = -k₁ (K + s) w`, so `w' = -k₁ (K + s) w - q'(s) s'` with decay rate
`k₁ (K + s) ≥ k₁ K = kb + k₂` and forcing `|q'(s) s'| ≤ e_T² (k₁ s_T + kb) / K`; a comparison
argument (`image_le_of_deriv_right_lt_deriv_boundary'`, with a slack `δ → 0`) bounds `|w|`.
The same conservation gives `s' = -e_T mmRate k₂ K s + (k₁ s + kb) w`. Since `mmRate` is
increasing on `[0, ∞)` (`mmRate_strictMono`), the difference `d = s - S̄(e_T ·)` satisfies
`d' ≤ (k₁ s + kb) |w|` wherever `d ≥ 0` (and symmetrically), so `|d|` grows at most by the
integral of the `w` bound; no Gronwall factor appears. Forward invariance uses a first-exit
time for `s` and comparison for `c` and `e`.

## Source receipt (API-00)

Reuse search (2026-11-11, base `origin/main` 53666a3c1): `grep` for `QSSA`, `qss`,
`Tikhonov`, `singular perturbation`, `quasi-steady` over `MathlibExt`, `WantedExt`,
`MathlibExtTest`, and Mathlib v4.35.0 for comparison/Gronwall lemmas. Found and reused:
`MathlibExt.Biology.Dynamics.MichaelisMenten` (`IsSolution`, conservation, `qssComplex`,
`mmRate`, `mmRate_strictMono`, `michaelisConstant`); Mathlib
`image_le_of_deriv_right_lt_deriv_boundary'`, `antitoneOn_of_hasDerivWithinAt_nonpos`. The only
existing QSSA approximation statement is the `theorem_wanted`
`WantedExt.Biology.Dynamics.MichaelisMentenQSSAWanted.abs_sub_reduced_le` (unproved, not
imported here). `MathlibExt.Analysis.FunctionalAnalysis.TikhonovRegularization` is unrelated
(ridge regression). No sibling CRN-02 file is imported.

Statements follow the slow-time scaling `τ = e₀ t` and the `O(e₀)` uniform estimate of
Heineken, Tsuchiya and Aris (1967), §§2–3, and the initial-layer / outer-solution split of
Segel and Slemrod (1989), §§3–5 (fast time scale `t_c = 1/(k₁ (s₀ + K_M))`, prepared versus
unprepared data); the constants and the monotonicity argument are this file's own.

## References

* A. N. Tikhonov, *Systems of differential equations containing small parameters in the
  derivatives*, Mat. Sb. (N.S.) 31(73) (1952) 575–586.
* F. G. Heineken, H. M. Tsuchiya and R. Aris, *On the mathematical status of the pseudo-steady
  state hypothesis of biochemical kinetics*, Math. Biosci. 1 (1967) 95–113.
* L. A. Segel and M. Slemrod, *The quasi-steady-state assumption: a case study in
  perturbation*, SIAM Rev. 31 (1989) 446–477.
-/

@[expose] public section

open Filter Topology Real Set

namespace MathlibExt.Biology.Dynamics.MichaelisMenten

/-! ### Comparison lemmas -/

/-- Strict-boundary comparison on `[0, T]` for functions with two-sided derivatives. -/
private lemma le_of_lt_on_eq {f f' B B' : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t) (hB : ∀ t ∈ Icc 0 T, HasDerivAt B (B' t) t)
    (h0 : f 0 ≤ B 0) (hbd : ∀ t ∈ Ico 0 T, f t = B t → f' t < B' t) :
    ∀ t ∈ Icc 0 T, f t ≤ B t :=
  image_le_of_deriv_right_lt_deriv_boundary'
    (fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt) h0
    (fun t ht ↦ (hB t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hB t (Ico_subset_Icc_self ht)).hasDerivWithinAt) hbd

/-- A positive function whose logarithmic derivative is at least `-M` while it is positive
stays above `f(0)/2 · e^{-(M + 1) t}` on `[0, T]`. -/
private lemma exp_lower_le {f f' : ℝ → ℝ} {T M : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t) (h0 : 0 < f 0)
    (hbd : ∀ t ∈ Ico 0 T, 0 < f t → -M * f t ≤ f' t) :
    ∀ t ∈ Icc 0 T, f 0 / 2 * exp (-(M + 1) * t) ≤ f t := by
  have key := le_of_lt_on_eq (f := fun r ↦ -f r) (f' := fun r ↦ -f' r)
    (B := fun r ↦ -(f 0 / 2 * exp (-(M + 1) * r)))
    (B' := fun r ↦ -(f 0 / 2 * (exp (-(M + 1) * r) * (-(M + 1) * 1))))
    (fun r hr ↦ (hf r hr).neg)
    (fun r _ ↦ (((hasDerivAt_id' r).const_mul (-(M + 1))).exp.const_mul (f 0 / 2)).neg)
    (by simp only [mul_zero, exp_zero, mul_one]; linarith) ?_
  · intro t ht
    have := key t ht
    linarith
  · intro r hr heq
    have hfr : f r = f 0 / 2 * exp (-(M + 1) * r) := by linarith
    have hpos : 0 < f r := by rw [hfr]; positivity
    have h1 := hbd r hr hpos
    have h2 : -(f 0 / 2 * (exp (-(M + 1) * r) * (-(M + 1) * 1))) = (M + 1) * f r := by
      rw [hfr]; ring
    rw [h2]
    nlinarith

/-- One-sided decay estimate: if `w' = -a w + g` with `a ≥ λ > 0` and `g ≤ G`, then
`w(t) ≤ |w(0)| e^{-λ t} + G/λ`. -/
private lemma le_of_decay {w a g : ℝ → ℝ} {lam G : ℝ} (hlam : 0 < lam) (hG : 0 ≤ G)
    (hw : ∀ t, 0 ≤ t → HasDerivAt w (-a t * w t + g t) t)
    (ha : ∀ t, 0 ≤ t → lam ≤ a t) (hg : ∀ t, 0 ≤ t → g t ≤ G) {t : ℝ} (ht : 0 ≤ t) :
    w t ≤ |w 0| * exp (-lam * t) + G / lam := by
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  refine le_of_lt_on_eq (T := t) (f := w) (f' := fun r ↦ -a r * w r + g r)
    (B := fun r ↦ |w 0| * exp (-lam * r) + G / lam + δ)
    (B' := fun r ↦ |w 0| * (exp (-lam * r) * (-lam * 1)))
    (fun r hr ↦ hw r hr.1)
    (fun r _ ↦ (((((hasDerivAt_id' r).const_mul (-lam)).exp).const_mul |w 0|).add_const
      (G / lam)).add_const δ)
    (by simp only [mul_zero, exp_zero, mul_one]
        linarith [le_abs_self (w 0), div_nonneg hG hlam.le]) ?_ t ⟨ht, le_rfl⟩
  intro r hr heq
  have hwpos : 0 ≤ w r := by rw [heq]; positivity
  have h1 : -a r * w r ≤ -lam * w r := by nlinarith [ha r hr.1]
  have h2 := hg r hr.1
  have h3 : |w 0| * (exp (-lam * r) * (-lam * 1)) = -lam * w r + G + lam * δ := by
    rw [heq]; field_simp; ring
  rw [h3]
  nlinarith [mul_pos hlam hδ]

/-- Two-sided decay estimate: if `w' = -a w + g` with `a ≥ λ > 0` and `|g| ≤ G`, then
`|w(t)| ≤ |w(0)| e^{-λ t} + G/λ`. -/
private lemma abs_le_of_decay {w a g : ℝ → ℝ} {lam G : ℝ} (hlam : 0 < lam)
    (hw : ∀ t, 0 ≤ t → HasDerivAt w (-a t * w t + g t) t)
    (ha : ∀ t, 0 ≤ t → lam ≤ a t) (hg : ∀ t, 0 ≤ t → |g t| ≤ G) {t : ℝ} (ht : 0 ≤ t) :
    |w t| ≤ |w 0| * exp (-lam * t) + G / lam := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hg 0 le_rfl)
  rw [abs_le]
  constructor
  · have := le_of_decay (w := fun r ↦ -w r) (a := a) (g := fun r ↦ -g r) hlam hG
      (fun r hr ↦ (hw r hr).neg.congr_deriv (by ring)) ha
      (fun r hr ↦ (neg_le_abs _).trans (hg r hr)) ht
    simp only [abs_neg] at this
    linarith
  · exact le_of_decay hlam hG hw ha (fun r hr ↦ (le_abs_self _).trans (hg r hr)) ht

/-- One-sided drift estimate: if `d' ≤ h` wherever `d ≥ 0`, and `H' = h`, `H(0) = 0`,
`H ≥ 0`, then `d(t) ≤ |d(0)| + H(t)`. -/
private lemma le_of_drift {d d' H h : ℝ → ℝ}
    (hd : ∀ t, 0 ≤ t → HasDerivAt d (d' t) t) (hH : ∀ t, 0 ≤ t → HasDerivAt H (h t) t)
    (hH0 : H 0 = 0) (hHnn : ∀ t, 0 ≤ t → 0 ≤ H t)
    (hbd : ∀ t, 0 ≤ t → 0 ≤ d t → d' t ≤ h t) {t : ℝ} (ht : 0 ≤ t) :
    d t ≤ |d 0| + H t := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set δ := ε / (t + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδt : δ * t ≤ ε := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; nlinarith
  have key := le_of_lt_on_eq (T := t) (f := d) (f' := d')
    (B := fun r ↦ |d 0| + H r + δ * r) (B' := fun r ↦ h r + δ * 1)
    (fun r hr ↦ hd r hr.1)
    (fun r hr ↦ ((hH r hr.1).const_add |d 0|).add ((hasDerivAt_id' r).const_mul δ))
    (by simp only [hH0, mul_zero, add_zero]; exact le_abs_self _) ?_ t ⟨ht, le_rfl⟩
  · linarith
  · intro r hr heq
    have : 0 ≤ d r := by
      rw [heq]; have := hHnn r hr.1; have := abs_nonneg (d 0); nlinarith [hr.1]
    linarith [hbd r hr.1 this]

/-- Two-sided drift estimate. -/
private lemma abs_le_of_drift {d d' H h : ℝ → ℝ}
    (hd : ∀ t, 0 ≤ t → HasDerivAt d (d' t) t) (hH : ∀ t, 0 ≤ t → HasDerivAt H (h t) t)
    (hH0 : H 0 = 0) (hHnn : ∀ t, 0 ≤ t → 0 ≤ H t)
    (hbd : ∀ t, 0 ≤ t → 0 ≤ d t → d' t ≤ h t)
    (hbd' : ∀ t, 0 ≤ t → d t ≤ 0 → -d' t ≤ h t) {t : ℝ} (ht : 0 ≤ t) :
    |d t| ≤ |d 0| + H t := by
  rw [abs_le]
  constructor
  · have := le_of_drift (d := fun r ↦ -d r) (d' := fun r ↦ -d' r) (fun r hr ↦ (hd r hr).neg)
      hH hH0 hHnn (fun r hr hr' ↦ hbd' r hr (by simpa using hr')) ht
    simp only [abs_neg] at this
    linarith
  · exact le_of_drift hd hH hH0 hHnn hbd ht

/-! ### Algebraic identities -/

private lemma michaelisConstant_pos' {k₁ kb k₂ : ℝ} (hk₁ : 0 < k₁) (hkb : 0 ≤ kb)
    (hk₂ : 0 < k₂) : 0 < michaelisConstant k₁ kb k₂ :=
  div_pos (by linarith) hk₁

private lemma mul_michaelisConstant {k₁ kb k₂ : ℝ} (hk₁ : 0 < k₁) :
    k₁ * michaelisConstant k₁ kb k₂ = kb + k₂ := by
  unfold michaelisConstant; field_simp

/-- With `e = e_T - c`, the complex equation is `c' = -k₁ (K + s) (c - q(s))`. -/
private lemma complexRate_eq {k₁ kb k₂ eT s c : ℝ} (hk₁ : 0 < k₁)
    (hK : michaelisConstant k₁ kb k₂ + s ≠ 0) :
    complexRate k₁ kb k₂ s c (eT - c) =
      -(k₁ * (michaelisConstant k₁ kb k₂ + s)) * (c - qssComplex k₁ kb k₂ eT s) := by
  have hKk := mul_michaelisConstant (kb := kb) (k₂ := k₂) hk₁
  unfold complexRate qssComplex
  set K := michaelisConstant k₁ kb k₂
  rw [← hKk]
  field_simp
  ring

/-- With `e = e_T - c`, the substrate equation is
`s' = -e_T mmRate k₂ K s + (k₁ s + kb) (c - q(s))`. -/
private lemma substrateRate_eq {k₁ kb k₂ eT s c : ℝ} (hk₁ : 0 < k₁)
    (hK : michaelisConstant k₁ kb k₂ + s ≠ 0) :
    substrateRate k₁ kb s c (eT - c) =
      -(eT * mmRate k₂ (michaelisConstant k₁ kb k₂) s) +
        (k₁ * s + kb) * (c - qssComplex k₁ kb k₂ eT s) := by
  have hKk := mul_michaelisConstant (kb := kb) (k₂ := k₂) hk₁
  unfold substrateRate mmRate qssComplex
  set K := michaelisConstant k₁ kb k₂
  have hkb : kb = k₁ * K - k₂ := by linarith
  rw [hkb]
  field_simp
  ring

/-- Derivative of the QSS complex along a curve. -/
private lemma hasDerivAt_qssComplex_comp {k₁ kb k₂ eT : ℝ} {s : ℝ → ℝ} {s' t : ℝ}
    (hs : HasDerivAt s s' t) (hK : michaelisConstant k₁ kb k₂ + s t ≠ 0) :
    HasDerivAt (fun r ↦ qssComplex k₁ kb k₂ eT (s r))
      (eT * michaelisConstant k₁ kb k₂ * s' / (michaelisConstant k₁ kb k₂ + s t) ^ 2) t := by
  unfold qssComplex
  convert HasDerivAt.div (hs.const_mul eT) (hs.const_add (michaelisConstant k₁ kb k₂)) hK using 1
  field_simp
  ring

/-! ### Forward invariance of the physical region -/

variable {k₁ kb k₂ : ℝ} {s c e p : ℝ → ℝ}

/-- While `s ≥ 0` on `[0, T]`, the complex stays in `[0, e_T]` there. -/
private lemma complex_mem_Icc (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 < k₁) (hkb : 0 ≤ kb)
    (hk₂ : 0 < k₂) (hc0 : 0 ≤ c 0) (he0 : 0 ≤ e 0) {T : ℝ}
    (hs : ∀ t ∈ Icc 0 T, 0 ≤ s t) : ∀ t ∈ Icc 0 T, 0 ≤ c t ∧ c t ≤ e 0 + c 0 := by
  have hcd : ∀ t ∈ Icc 0 T,
      HasDerivAt c (k₁ * (e 0 + c 0 - c t) * s t - (kb + k₂) * c t) t := by
    intro t ht
    have hcons := h.enzyme_conservation ht.1
    have := h.hasDerivAt_complex t ht.1
    unfold complexRate at this
    rwa [show e t = e 0 + c 0 - c t by linarith] at this
  intro t ht
  constructor
  · have key : ∀ δ, 0 < δ → -c t ≤ 0 + δ := by
      intro δ hδ
      have := le_of_lt_on_eq (f := fun r ↦ -c r)
        (f' := fun r ↦ -(k₁ * (e 0 + c 0 - c r) * s r - (kb + k₂) * c r))
        (B := fun _ ↦ δ) (B' := fun _ ↦ 0)
        (fun r hr ↦ (hcd r hr).neg) (fun r _ ↦ hasDerivAt_const r δ) (by linarith)
        ?_ t ht
      · simpa using this
      · intro r hr heq
        have hc : c r = -δ := by linarith
        rw [hc]
        have hsr := hs r (Ico_subset_Icc_self hr)
        nlinarith [mul_nonneg (mul_nonneg hk₁.le (by linarith : 0 ≤ e 0 + c 0 - -δ)) hsr,
          mul_pos (by linarith : 0 < kb + k₂) hδ]
    linarith [le_of_forall_pos_le_add key]
  · have key : ∀ δ, 0 < δ → c t ≤ e 0 + c 0 + δ := by
      intro δ hδ
      refine le_of_lt_on_eq (f := c)
        (f' := fun r ↦ k₁ * (e 0 + c 0 - c r) * s r - (kb + k₂) * c r)
        (B := fun _ ↦ e 0 + c 0 + δ) (B' := fun _ ↦ 0)
        hcd (fun r _ ↦ hasDerivAt_const r _) (by linarith) ?_ t ht
      intro r hr heq
      rw [heq]
      have hsr := hs r (Ico_subset_Icc_self hr)
      nlinarith [mul_nonneg (mul_nonneg hk₁.le hδ.le) hsr,
        mul_pos (by linarith : 0 < kb + k₂) (by linarith : 0 < e 0 + c 0 + δ)]
    exact le_of_forall_pos_le_add key

/-- **Positivity of the substrate**: `s(0) > 0`, `c(0), e(0) ≥ 0` give `s(t) > 0` for
`t ≥ 0`. -/
theorem IsSolution.substrate_pos (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 < k₁)
    (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hs0 : 0 < s 0) (hc0 : 0 ≤ c 0) (he0 : 0 ≤ e 0) {t : ℝ}
    (ht : 0 ≤ t) : 0 < s t := by
  by_contra hneg
  push Not at hneg
  have hcont : ContinuousOn s (Icc 0 t) := fun r hr ↦
    (h.hasDerivAt_substrate r hr.1).continuousAt.continuousWithinAt
  have hA : IsClosed (Icc 0 t ∩ s ⁻¹' Iic 0) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hne : (Icc 0 t ∩ s ⁻¹' Iic 0).Nonempty := ⟨t, ⟨ht, le_rfl⟩, hneg⟩
  have hbdd : BddBelow (Icc 0 t ∩ s ⁻¹' Iic 0) := ⟨0, fun r hr ↦ hr.1.1⟩
  set t₀ := sInf (Icc 0 t ∩ s ⁻¹' Iic 0)
  have hmem : t₀ ∈ Icc 0 t ∩ s ⁻¹' Iic 0 := hA.csInf_mem hne hbdd
  have hbelow : ∀ r ∈ Ico 0 t₀, 0 < s r := by
    intro r hr
    by_contra hr'
    push Not at hr'
    have : t₀ ≤ r := csInf_le hbdd ⟨⟨hr.1, hr.2.le.trans hmem.1.2⟩, hr'⟩
    linarith [hr.2]
  have hcb : ∀ r ∈ Ico 0 t₀, 0 ≤ c r ∧ c r ≤ e 0 + c 0 := fun r hr ↦
    complex_mem_Icc h hk₁ hkb hk₂ hc0 he0 (T := r)
      (fun u hu ↦ (hbelow u ⟨hu.1, hu.2.trans_lt hr.2⟩).le) r ⟨hr.1, le_rfl⟩
  have hlow := exp_lower_le (T := t₀) (M := k₁ * (e 0 + c 0))
    (f' := fun r ↦ substrateRate k₁ kb (s r) (c r) (e r))
    (fun r hr ↦ h.hasDerivAt_substrate r hr.1) hs0 (by
      intro r hr hsr
      obtain ⟨hc1, hc2⟩ := hcb r hr
      have hcons := h.enzyme_conservation hr.1
      unfold substrateRate
      nlinarith [mul_nonneg (mul_nonneg hk₁.le hsr.le) (by linarith : 0 ≤ e 0 + c 0 - e r),
        mul_nonneg hkb hc1]) t₀ ⟨hmem.1.1, le_rfl⟩
  have : 0 < s 0 / 2 * exp (-(k₁ * (e 0 + c 0) + 1) * t₀) := by positivity
  have h2 : s t₀ ≤ 0 := hmem.2
  linarith

/-- The complex stays nonnegative. -/
theorem IsSolution.complex_nonneg (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 < k₁)
    (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hs0 : 0 < s 0) (hc0 : 0 ≤ c 0) (he0 : 0 ≤ e 0) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ c t :=
  (complex_mem_Icc h hk₁ hkb hk₂ hc0 he0 (T := t)
    (fun _ hr ↦ (h.substrate_pos hk₁ hkb hk₂ hs0 hc0 he0 hr.1).le) t ⟨ht, le_rfl⟩).1

/-- The complex stays below the total enzyme `e_T = e(0) + c(0)` (equivalently `e ≥ 0`). -/
theorem IsSolution.complex_le (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 < k₁)
    (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hs0 : 0 < s 0) (hc0 : 0 ≤ c 0) (he0 : 0 ≤ e 0) {t : ℝ}
    (ht : 0 ≤ t) : c t ≤ e 0 + c 0 :=
  (complex_mem_Icc h hk₁ hkb hk₂ hc0 he0 (T := t)
    (fun _ hr ↦ (h.substrate_pos hk₁ hkb hk₂ hs0 hc0 he0 hr.1).le) t ⟨ht, le_rfl⟩).2

/-- The free enzyme stays nonnegative. -/
theorem IsSolution.enzyme_nonneg (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 < k₁)
    (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hs0 : 0 < s 0) (hc0 : 0 ≤ c 0) (he0 : 0 ≤ e 0) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ e t := by
  have := h.complex_le hk₁ hkb hk₂ hs0 hc0 he0 ht
  have := h.enzyme_conservation ht
  linarith

/-- The substrate stays below `s_T = s(0) + c(0)`. -/
theorem IsSolution.substrate_le (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 < k₁)
    (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hs0 : 0 < s 0) (hc0 : 0 ≤ c 0) (he0 : 0 ≤ e 0) {t : ℝ}
    (ht : 0 ≤ t) : s t ≤ s 0 + c 0 := by
  have hanti : AntitoneOn (fun r ↦ s r + c r) (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (f' := fun r ↦ -(k₂ * c r))
      (fun r hr ↦ ((h.hasDerivAt_substrate r hr).add
        (h.hasDerivAt_complex r hr)).continuousAt.continuousWithinAt) ?_ ?_
    · intro r hr
      rw [interior_Ici] at hr
      refine (((h.hasDerivAt_substrate r (le_of_lt hr)).add
        (h.hasDerivAt_complex r (le_of_lt hr))).congr_deriv ?_).hasDerivWithinAt
      unfold substrateRate complexRate; ring
    · intro r hr
      rw [interior_Ici] at hr
      have := h.complex_nonneg hk₁ hkb hk₂ hs0 hc0 he0 (le_of_lt hr)
      nlinarith
  have h1 : s t + c t ≤ s 0 + c 0 := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
  have := h.complex_nonneg hk₁ hkb hk₂ hs0 hc0 he0 ht
  linarith

/-- A solution of the reduced equation `S̄' = -mmRate k₂ K S̄` with `S̄(0) > 0` stays
positive. -/
theorem reduced_pos {k₂ K : ℝ} (hk₂ : 0 < k₂) (hK : 0 < K) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-mmRate k₂ K (S τ)) τ) (hS0 : 0 < S 0) {τ : ℝ}
    (hτ : 0 ≤ τ) : 0 < S τ := by
  have := exp_lower_le (T := τ) (M := k₂ / K) (fun r hr ↦ hS r hr.1) hS0 (by
    intro r _ hr
    unfold mmRate
    have : k₂ * S r / (K + S r) ≤ k₂ / K * S r := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) hK (by linarith)
    linarith) τ ⟨hτ, le_rfl⟩
  have : 0 < S 0 / 2 * exp (-(k₂ / K + 1) * τ) := by positivity
  linarith

/-- **The reduced equation is solvable**: for `K > 0` and `s₀ > 0` there is a positive
solution of `S̄' = -mmRate k₂ K S̄` on all of `ℝ` with `S̄(0) = s₀`, namely
`S̄(τ) = Φ⁻¹(Φ(s₀) - k₂ τ)` with `Φ(x) = x + K log x` (the implicit Michaelis–Menten
integral). -/
theorem exists_reduced_solution {k₂ K s₀ : ℝ} (hK : 0 < K) (hs₀ : 0 < s₀) :
    ∃ S : ℝ → ℝ, (∀ τ, HasDerivAt S (-mmRate k₂ K (S τ)) τ) ∧ S 0 = s₀ ∧ ∀ τ, 0 < S τ := by
  set Φ : ℝ → ℝ := fun x ↦ x + K * log x with hΦ
  have hmono : StrictMonoOn Φ (Ioi 0) := by
    intro x hx y _ hxy
    have := log_lt_log hx hxy
    simp only [hΦ]
    nlinarith
  have hcont : ContinuousOn Φ (Ioi 0) :=
    continuousOn_id.add (continuousOn_const.mul (continuousOn_log.mono fun x hx ↦ ne_of_gt hx))
  have hsurj : ∀ y, ∃ x, 0 < x ∧ Φ x = y := by
    intro y
    set a := min 1 (exp ((y - 1) / K))
    set b := max 1 (|y| + 1)
    have ha : 0 < a := lt_min one_pos (exp_pos _)
    have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
    have hΦa : Φ a ≤ y := by
      have h1 : a ≤ 1 := min_le_left _ _
      have h2 : log a ≤ (y - 1) / K := by
        rw [← log_exp ((y - 1) / K)]
        exact log_le_log ha (min_le_right _ _)
      rw [le_div_iff₀ hK] at h2
      simp only [hΦ]
      linarith
    have hΦb : y ≤ Φ b := by
      have h1 : 0 ≤ log b := log_nonneg (le_max_left _ _)
      have h2 : |y| + 1 ≤ b := le_max_right _ _
      simp only [hΦ]
      nlinarith [le_abs_self y, mul_nonneg hK.le h1]
    obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hab
      (hcont.mono fun z hz ↦ lt_of_lt_of_le ha hz.1) ⟨hΦa, hΦb⟩
    exact ⟨x, lt_of_lt_of_le ha hx.1, hxy⟩
  choose g hg0 hgΦ using hsurj
  have hgΦ' : ∀ x, 0 < x → g (Φ x) = x := fun x hx ↦
    hmono.injOn (hg0 (Φ x)) hx (hgΦ (Φ x))
  have hgmono : Monotone g := by
    intro y₁ y₂ hy
    by_contra hlt
    push Not at hlt
    have := hmono (hg0 y₂) (hg0 y₁) hlt
    rw [hgΦ, hgΦ] at this
    linarith
  have hgcont : Continuous g := by
    refine continuous_iff_continuousAt.2 fun y ↦ ?_
    refine continuousAt_of_monotoneOn_of_image_mem_nhds (hgmono.monotoneOn univ)
      univ_mem ?_
    rw [image_univ]
    refine mem_of_superset (Ioi_mem_nhds (hg0 y)) fun x hx ↦ ⟨Φ x, hgΦ' x hx⟩
  have hgd : ∀ y, HasDerivAt g (1 + K * (g y)⁻¹)⁻¹ y := by
    intro y
    refine HasDerivAt.of_local_left_inverse hgcont.continuousAt ?_ ?_
      (Eventually.of_forall hgΦ)
    · exact (hasDerivAt_id' (g y)).add ((hasDerivAt_log (hg0 y).ne').const_mul K)
    · have := hg0 y
      positivity
  refine ⟨fun τ ↦ g (Φ s₀ - k₂ * τ), fun τ ↦ ?_, by simpa using hgΦ' s₀ hs₀,
    fun τ ↦ hg0 _⟩
  have := (hgd (Φ s₀ - k₂ * τ)).comp τ (((hasDerivAt_id' τ).const_mul k₂).const_sub (Φ s₀))
  refine HasDerivAt.congr_deriv (f := fun τ ↦ g (Φ s₀ - k₂ * τ)) this ?_
  have hpos := hg0 (Φ s₀ - k₂ * τ)
  unfold mmRate
  field_simp
  ring

/-! ### The QSS slaving estimate (real time) -/

/-- **The complex is slaved to the QSS manifold**, for all `t ≥ 0`, up to an initial-layer
term decaying at rate `kb + k₂ = k₁ K`:
`|c(t) - q(s(t))| ≤ |c(0) - q(s(0))| e^{-(kb + k₂) t} + e_T² (k₁ s_T + kb) / K / (kb + k₂)`,
with `e_T = e(0) + c(0)`, `s_T = s(0) + c(0)`. -/
theorem IsSolution.abs_complex_sub_qss_le (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 < k₁)
    (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hs0 : 0 < s 0) (hc0 : 0 ≤ c 0) (he0 : 0 ≤ e 0) {t : ℝ}
    (ht : 0 ≤ t) :
    |c t - qssComplex k₁ kb k₂ (e 0 + c 0) (s t)| ≤
      |c 0 - qssComplex k₁ kb k₂ (e 0 + c 0) (s 0)| * exp (-(kb + k₂) * t) +
        (e 0 + c 0) ^ 2 * (k₁ * (s 0 + c 0) + kb) / michaelisConstant k₁ kb k₂ /
          (kb + k₂) := by
  have hK := michaelisConstant_pos' hk₁ hkb hk₂
  have hKk := mul_michaelisConstant (kb := kb) (k₂ := k₂) hk₁
  set K := michaelisConstant k₁ kb k₂
  set eT := e 0 + c 0
  set sT := s 0 + c 0
  have heT : 0 ≤ eT := by positivity
  have hpos := fun r (hr : 0 ≤ r) ↦ h.substrate_pos hk₁ hkb hk₂ hs0 hc0 he0 hr
  refine abs_le_of_decay (w := fun r ↦ c r - qssComplex k₁ kb k₂ eT (s r))
    (a := fun r ↦ k₁ * (K + s r))
    (g := fun r ↦ -(eT * K * substrateRate k₁ kb (s r) (c r) (e r) / (K + s r) ^ 2))
    (by linarith) ?_ ?_ ?_ ht
  · intro r hr
    have hKs : K + s r ≠ 0 := by linarith [hpos r hr]
    have hcons := h.enzyme_conservation hr
    have he : e r = eT - c r := by linarith
    refine ((h.hasDerivAt_complex r hr).sub
      (hasDerivAt_qssComplex_comp (eT := eT) (h.hasDerivAt_substrate r hr) hKs)).congr_deriv ?_
    rw [he, complexRate_eq hk₁ hKs]
    ring
  · intro r hr
    nlinarith [hpos r hr]
  · intro r hr
    have hsr := hpos r hr
    have hc1 := h.complex_nonneg hk₁ hkb hk₂ hs0 hc0 he0 hr
    have hc2 := h.complex_le hk₁ hkb hk₂ hs0 hc0 he0 hr
    have he1 := h.enzyme_nonneg hk₁ hkb hk₂ hs0 hc0 he0 hr
    have hs2 := h.substrate_le hk₁ hkb hk₂ hs0 hc0 he0 hr
    have hcons := h.enzyme_conservation hr
    set v := substrateRate k₁ kb (s r) (c r) (e r) with hv
    have hvabs : |v| ≤ eT * (k₁ * sT + kb) := by
      rw [abs_le, hv]
      unfold substrateRate
      have h1 : e r * s r ≤ eT * sT := mul_le_mul (by linarith) hs2 hsr.le heT
      constructor
      · nlinarith [mul_nonneg hkb hc1, mul_nonneg hk₁.le (mul_nonneg he1 hsr.le)]
      · nlinarith [mul_nonneg hkb hc1, mul_nonneg hk₁.le (mul_nonneg he1 hsr.le),
          mul_le_mul_of_nonneg_left hc2 hkb]
    rw [abs_neg, abs_div, abs_mul, abs_mul, abs_of_nonneg heT, abs_of_pos hK,
      abs_of_pos (by positivity : (0 : ℝ) < (K + s r) ^ 2)]
    calc eT * K * |v| / (K + s r) ^ 2 ≤ eT * K * |v| / K ^ 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          nlinarith
      _ = eT * |v| / K := by field_simp
      _ ≤ eT * (eT * (k₁ * sT + kb)) / K := by gcongr
      _ = eT ^ 2 * (k₁ * sT + kb) / K := by ring

/-! ### The substrate estimate (real time) -/

/-- **The substrate tracks the reduced solution on the slow clock**, for all `t ≥ 0`: with
`e_T = e(0) + c(0)`, `s_T = s(0) + c(0)` and `S̄` a solution of the reduced equation
`S̄' = -mmRate k₂ K S̄` with `S̄(0) > 0`,
`|s(t) - S̄(e_T t)| ≤ |s(0) - S̄(0)| + (k₁ s_T + kb) (|c(0) - q(s(0))| / (kb + k₂) +
e_T² (k₁ s_T + kb) / K / (kb + k₂) · t)`. -/
theorem IsSolution.abs_substrate_sub_reduced_le (h : IsSolution k₁ kb k₂ s c e p)
    (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hs0 : 0 < s 0) (hc0 : 0 ≤ c 0)
    (he0 : 0 ≤ e 0) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)) τ)
    (hS0 : 0 < S 0) {t : ℝ} (ht : 0 ≤ t) :
    |s t - S ((e 0 + c 0) * t)| ≤ |s 0 - S 0| + (k₁ * (s 0 + c 0) + kb) *
      (|c 0 - qssComplex k₁ kb k₂ (e 0 + c 0) (s 0)| / (kb + k₂) +
        (e 0 + c 0) ^ 2 * (k₁ * (s 0 + c 0) + kb) / michaelisConstant k₁ kb k₂ / (kb + k₂) *
          t) := by
  have hK := michaelisConstant_pos' hk₁ hkb hk₂
  have hpos := fun r (hr : 0 ≤ r) ↦ h.substrate_pos hk₁ hkb hk₂ hs0 hc0 he0 hr
  have hw := fun r (hr : 0 ≤ r) ↦ h.abs_complex_sub_qss_le hk₁ hkb hk₂ hs0 hc0 he0 hr
  have hsle := fun r (hr : 0 ≤ r) ↦ h.substrate_le hk₁ hkb hk₂ hs0 hc0 he0 hr
  set K := michaelisConstant k₁ kb k₂
  set eT := e 0 + c 0 with heTdef
  set sT := s 0 + c 0 with hsTdef
  set w0 := |c 0 - qssComplex k₁ kb k₂ eT (s 0)|
  set M := k₁ * sT + kb with hMdef
  set L := eT ^ 2 * M / K / (kb + k₂) with hLdef
  have heT : 0 ≤ eT := by positivity
  have hlam : 0 < kb + k₂ := by linarith
  have hsT : 0 ≤ sT := by positivity
  have hM : 0 ≤ M := by positivity
  have hL : 0 ≤ L := by positivity
  have hw0 : 0 ≤ w0 := abs_nonneg _
  have hSpos := fun r (hr : 0 ≤ r) ↦ reduced_pos hk₂ hK hS hS0 hr
  have hSr : ∀ r, 0 ≤ r → HasDerivAt (fun u ↦ S (eT * u))
      (-mmRate k₂ K (S (eT * r)) * (eT * 1)) r :=
    fun r hr ↦ (hS (eT * r) (by positivity)).comp r ((hasDerivAt_id' r).const_mul eT)
  have hmono := (mmRate_strictMono hk₂ hK).monotoneOn
  have key := abs_le_of_drift (d := fun r ↦ s r - S (eT * r))
    (d' := fun r ↦ substrateRate k₁ kb (s r) (c r) (e r) - -mmRate k₂ K (S (eT * r)) * (eT * 1))
    (H := fun r ↦ M * (w0 * (1 - exp (-(kb + k₂) * r)) / (kb + k₂) + L * r))
    (h := fun r ↦ M * (w0 * exp (-(kb + k₂) * r) + L))
    (fun r hr ↦ (h.hasDerivAt_substrate r hr).sub (hSr r hr)) ?_ (by simp) ?_ ?_ ?_ ht
  · have hexp : 0 < exp (-(kb + k₂) * t) := exp_pos _
    have h1 : w0 * (1 - exp (-(kb + k₂) * t)) / (kb + k₂) ≤ w0 / (kb + k₂) :=
      div_le_div_of_nonneg_right (by nlinarith) hlam.le
    have h2 := mul_le_mul_of_nonneg_left (add_le_add_left h1 (L * t)) hM
    rw [mul_zero] at key
    linarith
  · intro r _
    have e1 := ((hasDerivAt_id' r).const_mul (-(kb + k₂))).exp
    have e2 := ((((e1.const_sub 1).const_mul w0).div_const (kb + k₂)).add
      ((hasDerivAt_id' r).const_mul L)).const_mul M
    convert e2 using 1
    field_simp
  · intro r hr
    have : exp (-(kb + k₂) * r) ≤ 1 := exp_le_one_iff.2 (by nlinarith)
    have : 0 ≤ w0 * (1 - exp (-(kb + k₂) * r)) / (kb + k₂) :=
      div_nonneg (mul_nonneg hw0 (by linarith)) hlam.le
    have : 0 ≤ L * r := mul_nonneg hL hr
    positivity
  · intro r hr hd
    have hcons := h.enzyme_conservation hr
    have he : e r = eT - c r := by linarith
    have hKs : K + s r ≠ 0 := by linarith [hpos r hr]
    rw [he, substrateRate_eq hk₁ hKs]
    have hm : mmRate k₂ K (S (eT * r)) ≤ mmRate k₂ K (s r) :=
      hmono (hSpos _ (by positivity)).le (hpos r hr).le (by linarith)
    have hcoef : 0 ≤ k₁ * s r + kb := by nlinarith [hpos r hr]
    have hcoef2 : k₁ * s r + kb ≤ M := by nlinarith [hsle r hr]
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self (c r - qssComplex k₁ kb k₂ eT (s r))) hcoef
    have h2 := mul_le_mul hcoef2 (hw r hr) (abs_nonneg _) hM
    nlinarith [mul_le_mul_of_nonneg_left hm heT]
  · intro r hr hd
    have hcons := h.enzyme_conservation hr
    have he : e r = eT - c r := by linarith
    have hKs : K + s r ≠ 0 := by linarith [hpos r hr]
    rw [he, substrateRate_eq hk₁ hKs]
    have hm : mmRate k₂ K (s r) ≤ mmRate k₂ K (S (eT * r)) :=
      hmono (hpos r hr).le (hSpos _ (by positivity)).le (by linarith)
    have hcoef : 0 ≤ k₁ * s r + kb := by nlinarith [hpos r hr]
    have hcoef2 : k₁ * s r + kb ≤ M := by nlinarith [hsle r hr]
    have h1 := mul_le_mul_of_nonneg_left (neg_abs_le (c r - qssComplex k₁ kb k₂ eT (s r))) hcoef
    have h2 := mul_le_mul hcoef2 (hw r hr) (abs_nonneg _) hM
    nlinarith [mul_le_mul_of_nonneg_left hm heT]

/-! ### Standard data: the first-order Tikhonov estimate on a slow window -/

/-- The constant of the substrate estimate on the slow window `[0, T]`:
`(k₁ s₀ + kb) (1 / (kb + k₂) + (k₁ s₀ + kb) / K / (kb + k₂) · T)`. It grows linearly in
`T`. -/
noncomputable def substrateErrorConst (k₁ kb k₂ s₀ T : ℝ) : ℝ :=
  (k₁ * s₀ + kb) *
    (1 / (kb + k₂) + (k₁ * s₀ + kb) / michaelisConstant k₁ kb k₂ / (kb + k₂) * T)

/-- **Uniform QSSA for the substrate on a slow window, including `τ = 0`.** For the standard
data `s(0) = s₀ = S̄(0)`, `c(0) = 0`, `e(0) = ε > 0`,
`|s(τ/ε) - S̄(τ)| ≤ substrateErrorConst k₁ kb k₂ s₀ T · ε` for all `τ ∈ [0, T]`. -/
theorem abs_substrate_sub_reduced_le_mul (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂)
    {s₀ T ε : ℝ} (hs₀ : 0 < s₀) (hε : 0 < ε) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)) τ)
    (hS0 : S 0 = s₀) (h : IsSolution k₁ kb k₂ s c e p) (hs : s 0 = s₀) (hc : c 0 = 0)
    (he : e 0 = ε) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    |s (τ / ε) - S τ| ≤ substrateErrorConst k₁ kb k₂ s₀ T * ε := by
  have hK := michaelisConstant_pos' hk₁ hkb hk₂
  have key := h.abs_substrate_sub_reduced_le hk₁ hkb hk₂ (hs ▸ hs₀) hc.ge (he ▸ hε.le) hS
    (hS0 ▸ hs₀) (t := τ / ε) (div_nonneg hτ.1 hε.le)
  rw [hc, he, hs, hS0, add_zero, add_zero, sub_self, abs_zero, zero_add, zero_sub, abs_neg,
    mul_div_cancel₀ τ hε.ne'] at key
  set K := michaelisConstant k₁ kb k₂ with hKdef
  have hlam : 0 < kb + k₂ := by linarith
  have hM : 0 ≤ k₁ * s₀ + kb := by positivity
  have hq : |qssComplex k₁ kb k₂ ε s₀| ≤ ε := by
    unfold qssComplex
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have h1 : ε ^ 2 * (k₁ * s₀ + kb) / K / (kb + k₂) * (τ / ε) ≤
      ε ^ 2 * (k₁ * s₀ + kb) / K / (kb + k₂) * (T / ε) := by
    gcongr
    exact hτ.2
  refine key.trans ?_
  calc (k₁ * s₀ + kb) * (|qssComplex k₁ kb k₂ ε s₀| / (kb + k₂) +
        ε ^ 2 * (k₁ * s₀ + kb) / K / (kb + k₂) * (τ / ε))
      ≤ (k₁ * s₀ + kb) * (ε / (kb + k₂) + ε ^ 2 * (k₁ * s₀ + kb) / K / (kb + k₂) * (T / ε)) := by
        gcongr
    _ = substrateErrorConst k₁ kb k₂ s₀ T * ε := by
        unfold substrateErrorConst
        rw [← hKdef]
        field_simp

/-- The first-order Tikhonov estimate in the form of
`WantedExt.Biology.Dynamics.MichaelisMentenQSSAWanted.abs_sub_reduced_le`: one constant
(`substrateErrorConst k₁ kb k₂ s₀ T`) works for every `e₀ > 0`, every solution with data
`(s₀, 0, e₀)`, and every slow time `τ ∈ [0, T]`. -/
theorem exists_abs_substrate_sub_reduced_le (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂)
    {s₀ T : ℝ} (hs₀ : 0 < s₀) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)) τ)
    (hS₀ : S 0 = s₀) :
    ∃ C : ℝ, ∀ e₀ : ℝ, 0 < e₀ → ∀ s c e p : ℝ → ℝ, IsSolution k₁ kb k₂ s c e p →
      s 0 = s₀ → c 0 = 0 → e 0 = e₀ → ∀ τ ∈ Icc 0 T, |s (τ / e₀) - S τ| ≤ C * e₀ :=
  ⟨substrateErrorConst k₁ kb k₂ s₀ T, fun _ he₀ _ _ _ _ h hs hc he _ hτ ↦
    abs_substrate_sub_reduced_le_mul hk₁ hkb hk₂ hs₀ he₀ hS hS₀ h hs hc he hτ⟩

/-! ### The Michaelis–Menten rate law -/

/-- **Rate-law error on the slow clock, general data.** With `ε = e_T = e(0) + c(0) > 0`, the
slow-time product rate `dP/dτ = k₂ c(τ/ε)/ε` differs from the Michaelis–Menten rate
`mmRate k₂ K (S̄ τ)` by at most an initial-layer term `|c(0) - q(s(0))|/ε · e^{-(kb+k₂) τ/ε}`,
a slaving term `ε (k₁ s_T + kb)/K/(kb + k₂)`, and the substrate error divided by `K`. -/
theorem IsSolution.abs_rate_sub_mmRate_le (h : IsSolution k₁ kb k₂ s c e p) (hk₁ : 0 < k₁)
    (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) (hs0 : 0 < s 0) (hc0 : 0 ≤ c 0) (he0 : 0 ≤ e 0)
    (heT : 0 < e 0 + c 0) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)) τ)
    (hS0 : 0 < S 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    |k₂ * c (τ / (e 0 + c 0)) / (e 0 + c 0) - mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)| ≤
      k₂ * (|c 0 - qssComplex k₁ kb k₂ (e 0 + c 0) (s 0)| / (e 0 + c 0) *
          exp (-(kb + k₂) * τ / (e 0 + c 0)) +
        (e 0 + c 0) * (k₁ * (s 0 + c 0) + kb) / michaelisConstant k₁ kb k₂ / (kb + k₂) +
        |s (τ / (e 0 + c 0)) - S τ| / michaelisConstant k₁ kb k₂) := by
  have hK := michaelisConstant_pos' hk₁ hkb hk₂
  have ht : 0 ≤ τ / (e 0 + c 0) := div_nonneg hτ heT.le
  have hw := h.abs_complex_sub_qss_le hk₁ hkb hk₂ hs0 hc0 he0 ht
  have hst := h.substrate_pos hk₁ hkb hk₂ hs0 hc0 he0 ht
  have hSτ := reduced_pos hk₂ hK hS hS0 hτ
  set K := michaelisConstant k₁ kb k₂ with hKdef
  set eT := e 0 + c 0
  set t := τ / eT with htdef
  set x := s t
  set y := S τ
  have hlam : 0 < kb + k₂ := by linarith
  have hsplit : k₂ * c t / eT - mmRate k₂ K y =
      k₂ * ((c t - qssComplex k₁ kb k₂ eT x) / eT) + k₂ * (x / (K + x) - y / (K + y)) := by
    unfold mmRate qssComplex
    rw [← hKdef]
    field_simp
    ring
  have hlip : |x / (K + x) - y / (K + y)| ≤ |x - y| / K := by
    have hKx : 0 < K + x := by linarith
    have hKy : 0 < K + y := by linarith
    have e1 : x / (K + x) - y / (K + y) = K * (x - y) / ((K + x) * (K + y)) := by
      field_simp; ring
    rw [e1, abs_div, abs_mul, abs_of_pos hK, abs_of_pos (mul_pos hKx hKy),
      div_le_div_iff₀ (mul_pos hKx hKy) hK]
    have : K * K ≤ (K + x) * (K + y) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (abs_nonneg (x - y))]
  have hexp : exp (-(kb + k₂) * t) = exp (-(kb + k₂) * τ / eT) := by
    rw [htdef, mul_div_assoc]
  have hc' : |(c t - qssComplex k₁ kb k₂ eT x) / eT| ≤
      |c 0 - qssComplex k₁ kb k₂ eT (s 0)| / eT * exp (-(kb + k₂) * τ / eT) +
        eT * (k₁ * (s 0 + c 0) + kb) / K / (kb + k₂) := by
    rw [abs_div, abs_of_pos heT, div_le_iff₀ heT, ← hexp]
    convert hw using 1
    field_simp
  rw [hsplit]
  calc |k₂ * ((c t - qssComplex k₁ kb k₂ eT x) / eT) + k₂ * (x / (K + x) - y / (K + y))|
      ≤ k₂ * |(c t - qssComplex k₁ kb k₂ eT x) / eT| + k₂ * |x / (K + x) - y / (K + y)| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos hk₂]
    _ ≤ _ := by
        rw [← mul_add]
        gcongr

/-- The explicit rate-law error bound for standard data on the slow window `[τ₀, T]`:
`k₂ (e^{-(kb + k₂) τ₀ / ε} + ε ((k₁ s₀ + kb)/K/(kb + k₂) + substrateErrorConst/K))`. The first
term is the initial layer; it is small only when `τ₀ ≫ ε / (kb + k₂)`. -/
noncomputable def rateErrorBound (k₁ kb k₂ s₀ T τ₀ ε : ℝ) : ℝ :=
  k₂ * (exp (-(kb + k₂) * τ₀ / ε) +
    ε * ((k₁ * s₀ + kb) / michaelisConstant k₁ kb k₂ / (kb + k₂) +
      substrateErrorConst k₁ kb k₂ s₀ T / michaelisConstant k₁ kb k₂))

/-- **The Michaelis–Menten rate law away from the initial layer.** For the standard data
`s(0) = s₀ = S̄(0)`, `c(0) = 0`, `e(0) = ε > 0`, on the slow window `τ ∈ [τ₀, T]` with
`τ₀ ≥ 0`, `|k₂ c(τ/ε)/ε - mmRate k₂ K (S̄ τ)| ≤ rateErrorBound k₁ kb k₂ s₀ T τ₀ ε`. -/
theorem abs_rate_sub_mmRate_le (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂)
    {s₀ T τ₀ ε : ℝ} (hs₀ : 0 < s₀) (hε : 0 < ε) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)) τ)
    (hS0 : S 0 = s₀) (h : IsSolution k₁ kb k₂ s c e p) (hs : s 0 = s₀) (hc : c 0 = 0)
    (he : e 0 = ε) (hτ₀ : 0 ≤ τ₀) {τ : ℝ} (hτ : τ ∈ Icc τ₀ T) :
    |k₂ * c (τ / ε) / ε - mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)| ≤
      rateErrorBound k₁ kb k₂ s₀ T τ₀ ε := by
  have hK := michaelisConstant_pos' hk₁ hkb hk₂
  have hτ0 : 0 ≤ τ := hτ₀.trans hτ.1
  have key := h.abs_rate_sub_mmRate_le hk₁ hkb hk₂ (hs ▸ hs₀) hc.ge (he ▸ hε.le)
    (by rw [he, hc, add_zero]; exact hε) hS (hS0 ▸ hs₀) hτ0
  have hsub := abs_substrate_sub_reduced_le_mul hk₁ hkb hk₂ hs₀ hε hS hS0 h hs hc he
    ⟨hτ0, hτ.2⟩
  rw [hc, he, hs, add_zero, add_zero, zero_sub, abs_neg] at key
  set K := michaelisConstant k₁ kb k₂
  have hlam : 0 < kb + k₂ := by linarith
  have hq : |qssComplex k₁ kb k₂ ε s₀| / ε ≤ 1 := by
    rw [div_le_one hε]
    unfold qssComplex
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have hexp : exp (-(kb + k₂) * τ / ε) ≤ exp (-(kb + k₂) * τ₀ / ε) := by
    rw [exp_le_exp, div_le_div_iff_of_pos_right hε]
    nlinarith [mul_nonneg hlam.le (sub_nonneg.2 hτ.1)]
  refine key.trans ?_
  unfold rateErrorBound
  gcongr k₂ * ?_
  calc |qssComplex k₁ kb k₂ ε s₀| / ε * exp (-(kb + k₂) * τ / ε) +
        ε * (k₁ * s₀ + kb) / K / (kb + k₂) + |s (τ / ε) - S τ| / K
      ≤ 1 * exp (-(kb + k₂) * τ₀ / ε) + ε * (k₁ * s₀ + kb) / K / (kb + k₂) +
          substrateErrorConst k₁ kb k₂ s₀ T * ε / K := by
        gcongr
    _ = _ := by ring

/-- The rate-law bound tends to `0` as `ε → 0⁺` whenever the window excludes the initial
layer, `τ₀ > 0`. -/
theorem tendsto_rateErrorBound (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) {s₀ T τ₀ : ℝ} (hτ₀ : 0 < τ₀) :
    Tendsto (rateErrorBound k₁ kb k₂ s₀ T τ₀) (𝓝[>] 0) (𝓝 0) := by
  have hc : 0 < (kb + k₂) * τ₀ := by positivity
  have h1 : Tendsto (fun ε : ℝ ↦ exp (-(kb + k₂) * τ₀ / ε)) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_inv_nhdsGT_zero.const_mul_atTop hc))
    refine this.congr fun ε ↦ ?_
    simp only [Function.comp_apply]
    congr 1
    ring
  have h2 : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have := (h1.add (h2.mul_const ((k₁ * s₀ + kb) / michaelisConstant k₁ kb k₂ / (kb + k₂) +
    substrateErrorConst k₁ kb k₂ s₀ T / michaelisConstant k₁ kb k₂))).const_mul k₂
  unfold rateErrorBound
  simpa using this

/-! ### Prepared data: the bound including `τ = 0` -/

/-- The explicit rate-law error bound for prepared data on `[0, T]`:
`k₂ ε (k₁ (s₀ + ε) + kb)/K/(kb + k₂) · (1 + (k₁ (s₀ + ε) + kb) T / K)`. -/
noncomputable def preparedRateBound (k₁ kb k₂ s₀ T ε : ℝ) : ℝ :=
  k₂ * ε * ((k₁ * (s₀ + ε) + kb) / michaelisConstant k₁ kb k₂ / (kb + k₂) *
    (1 + (k₁ * (s₀ + ε) + kb) * T / michaelisConstant k₁ kb k₂))

/-- **The rate law including time zero, for prepared data.** If the complex starts on the
QSS manifold, `c(0) = q(s₀) = ε s₀/(K + s₀)` with total enzyme `e(0) + c(0) = ε > 0`, and
`s(0) = s₀ = S̄(0)`, then there is no initial layer:
`|k₂ c(τ/ε)/ε - mmRate k₂ K (S̄ τ)| ≤ preparedRateBound k₁ kb k₂ s₀ T ε` for all
`τ ∈ [0, T]`. -/
theorem abs_rate_sub_mmRate_le_of_prepared (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂)
    {s₀ T ε : ℝ} (hs₀ : 0 < s₀) (hε : 0 < ε) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)) τ)
    (hS0 : S 0 = s₀) (h : IsSolution k₁ kb k₂ s c e p) (hs : s 0 = s₀)
    (hc : c 0 = qssComplex k₁ kb k₂ ε s₀) (he : e 0 + c 0 = ε) {τ : ℝ} (hτ : τ ∈ Icc 0 T) :
    |k₂ * c (τ / ε) / ε - mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)| ≤
      preparedRateBound k₁ kb k₂ s₀ T ε := by
  have hK := michaelisConstant_pos' hk₁ hkb hk₂
  have hlam : 0 < kb + k₂ := by linarith
  have hq0 : 0 ≤ qssComplex k₁ kb k₂ ε s₀ := by unfold qssComplex; positivity
  have hqε : qssComplex k₁ kb k₂ ε s₀ ≤ ε := by
    unfold qssComplex
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hc0 : 0 ≤ c 0 := hc ▸ hq0
  have he0 : 0 ≤ e 0 := by linarith
  have key := h.abs_rate_sub_mmRate_le hk₁ hkb hk₂ (hs ▸ hs₀) hc0 he0 (he ▸ hε) hS
    (hS0 ▸ hs₀) hτ.1
  have hsub := h.abs_substrate_sub_reduced_le hk₁ hkb hk₂ (hs ▸ hs₀) hc0 he0 hS (hS0 ▸ hs₀)
    (t := τ / (e 0 + c 0)) (div_nonneg hτ.1 (he ▸ hε.le))
  rw [he] at key hsub
  rw [mul_div_cancel₀ τ hε.ne', hs, hS0, sub_self, abs_zero, zero_add] at hsub
  rw [hs, hc, sub_self, abs_zero, zero_div, zero_mul, zero_add] at key
  rw [hc, sub_self, abs_zero, zero_div, zero_add] at hsub
  set K := michaelisConstant k₁ kb k₂ with hKdef
  set M := k₁ * (s₀ + qssComplex k₁ kb k₂ ε s₀) + kb
  set M' := k₁ * (s₀ + ε) + kb with hM'def
  have hτ0 : 0 ≤ τ := hτ.1
  have hM : 0 ≤ M := by positivity
  have hMM : M ≤ M' := by have := mul_le_mul_of_nonneg_left hqε hk₁.le; linarith
  have hsub' : |s (τ / ε) - S τ| ≤ M' * (ε ^ 2 * M' / K / (kb + k₂) * (τ / ε)) := by
    refine hsub.trans ?_
    gcongr
  refine key.trans ?_
  have hτT : τ / ε ≤ T / ε := div_le_div_of_nonneg_right hτ.2 hε.le
  calc k₂ * (ε * M / K / (kb + k₂) + |s (τ / ε) - S τ| / K)
      ≤ k₂ * (ε * M' / K / (kb + k₂) + M' * (ε ^ 2 * M' / K / (kb + k₂) * (T / ε)) / K) := by
        gcongr
        exact hsub'.trans (by gcongr)
    _ = preparedRateBound k₁ kb k₂ s₀ T ε := by
        unfold preparedRateBound
        rw [← hKdef, ← hM'def]
        field_simp

/-- The prepared-data bound tends to `0` as `ε → 0⁺`. -/
theorem tendsto_preparedRateBound {s₀ T : ℝ} :
    Tendsto (preparedRateBound k₁ kb k₂ s₀ T) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds ?_
  have : Continuous (preparedRateBound k₁ kb k₂ s₀ T) := by
    unfold preparedRateBound; fun_prop
  simpa [preparedRateBound] using this.tendsto 0

/-! ### Limits along families of solutions -/

/-- **Reduced substrate dynamics as a limit.** Along any family of solutions with standard
data `(s₀, 0, ε)`, `s_ε(τ/ε) → S̄(τ)` as `ε → 0⁺`, for every slow time `τ ≥ 0`. -/
theorem tendsto_substrate_of_family (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) {s₀ : ℝ}
    (hs₀ : 0 < s₀) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)) τ)
    (hS0 : S 0 = s₀) {sf cf ef pf : ℝ → ℝ → ℝ}
    (hsol : ∀ ε, 0 < ε → IsSolution k₁ kb k₂ (sf ε) (cf ε) (ef ε) (pf ε) ∧ sf ε 0 = s₀ ∧
      cf ε 0 = 0 ∧ ef ε 0 = ε) {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun ε ↦ sf ε (τ / ε)) (𝓝[>] 0) (𝓝 (S τ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun ε : ℝ ↦ substrateErrorConst k₁ kb k₂ s₀ τ * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ)))).const_mul
      (substrateErrorConst k₁ kb k₂ s₀ τ)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨h, hs, hc, he⟩ := hsol ε hε
  rw [Real.norm_eq_abs]
  exact abs_substrate_sub_reduced_le_mul hk₁ hkb hk₂ hs₀ hε hS hS0 h hs hc he ⟨hτ, le_rfl⟩

/-- **The Michaelis–Menten rate law as a limit.** Along any family of solutions with standard
data `(s₀, 0, ε)`, the slow-time product rate `k₂ c_ε(τ/ε)/ε` tends to
`mmRate k₂ K (S̄ τ) = k₂ S̄(τ) / (K + S̄(τ))` as `ε → 0⁺`, for every slow time `τ > 0` (outside
the initial layer). -/
theorem tendsto_rate_of_family (hk₁ : 0 < k₁) (hkb : 0 ≤ kb) (hk₂ : 0 < k₂) {s₀ : ℝ}
    (hs₀ : 0 < s₀) {S : ℝ → ℝ}
    (hS : ∀ τ, 0 ≤ τ → HasDerivAt S (-mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ)) τ)
    (hS0 : S 0 = s₀) {sf cf ef pf : ℝ → ℝ → ℝ}
    (hsol : ∀ ε, 0 < ε → IsSolution k₁ kb k₂ (sf ε) (cf ε) (ef ε) (pf ε) ∧ sf ε 0 = s₀ ∧
      cf ε 0 = 0 ∧ ef ε 0 = ε) {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun ε ↦ k₂ * cf ε (τ / ε) / ε) (𝓝[>] 0)
      (𝓝 (mmRate k₂ (michaelisConstant k₁ kb k₂) (S τ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_
    (tendsto_rateErrorBound (k₁ := k₁) (s₀ := s₀) (T := τ) hkb hk₂ hτ)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨h, hs, hc, he⟩ := hsol ε hε
  rw [Real.norm_eq_abs]
  exact abs_rate_sub_mmRate_le hk₁ hkb hk₂ hs₀ hε hS hS0 h hs hc he hτ.le ⟨le_rfl, le_rfl⟩

end MathlibExt.Biology.Dynamics.MichaelisMenten
