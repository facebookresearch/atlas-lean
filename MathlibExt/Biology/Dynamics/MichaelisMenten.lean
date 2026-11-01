/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Michaelis–Menten kinetics: conservation laws and the quasi-steady state

The enzyme mechanism `E + S ⇌ C → E + P` with forward, backward and catalytic rate constants
`k₁, k₋₁, k₂ > 0` (`k₁`, `kb`, `k₂` in Lean) has the mass-action equations

  `s' = -k₁ e s + k₋₁ c`,  `c' = k₁ e s - (k₋₁ + k₂) c`,  `e' = -c'`,  `p' = k₂ c`.

This file proves the exact facts on which the quasi-steady-state approximation (QSSA) of
Briggs and Haldane rests:

* `IsSolution.enzyme_conservation`, `IsSolution.substrate_conservation`: `e + c` and
  `s + c + p` are constant along solutions.
* `complexRate_eq_zero_iff`: with `e = e₀ - c`, the complex is stationary (`c' = 0`) exactly on
  the quasi-steady-state manifold `c = e₀ s / (K_M + s)`, `K_M = (k₋₁ + k₂)/k₁` (the
  Michaelis constant of Briggs and Haldane).
* `productRate_qss`, `substrateRate_qss`: on that manifold `p' = -s' = V_max s / (K_M + s)` with
  `V_max = k₂ e₀` (the Michaelis–Menten rate law).
* `mmRate_strictMono`, `mmRate_michaelisConstant`, `tendsto_mmRate`: the rate law is strictly
  increasing, half-maximal at `s = K_M`, and saturates at `V_max`.
* `hasDerivAt_fastTransient`, `tendsto_fastTransient`: with the substrate frozen at `s̄ ≥ 0`
  (the boundary-layer system of the singular perturbation), the complex relaxes exponentially,
  at rate `k₁ (s̄ + K_M)`, onto the quasi-steady-state value.

The rigorous statement that the full solution stays within `O(e₀)` of the reduced
(Michaelis–Menten) solution on the slow time scale (Tikhonov's theorem as applied by Heineken,
Tsuchiya and Aris) is recorded as a wanted theorem in
`WantedExt.Biology.Dynamics.MichaelisMentenQSSAWanted`; it is not proved here.

## References

* L. Michaelis and M. L. Menten, *Die Kinetik der Invertinwirkung*, Biochem. Z. 49 (1913)
  333–369.
* G. E. Briggs and J. B. S. Haldane, *A note on the kinetics of enzyme action*, Biochem. J. 19
  (1925) 338–339.
* F. G. Heineken, H. M. Tsuchiya and R. Aris, *On the mathematical status of the pseudo-steady
  state hypothesis of biochemical kinetics*, Math. Biosci. 1 (1967) 95–113.
* L. A. Segel and M. Slemrod, *The quasi-steady-state assumption: a case study in
  perturbation*, SIAM Rev. 31 (1989) 446–477.
-/

@[expose] public section

open Filter Topology Real Set

namespace MathlibExt.Biology.Dynamics.MichaelisMenten

/-- The Michaelis constant `K_M = (kb + k₂)/k₁` (Briggs–Haldane). Meaningful for `k₁ > 0`. -/
noncomputable def michaelisConstant (k₁ kb k₂ : ℝ) : ℝ :=
  (kb + k₂) / k₁

/-- The mass-action rate of the substrate, `s' = -k₁ e s + kb c`. -/
def substrateRate (k₁ kb s c e : ℝ) : ℝ :=
  -k₁ * e * s + kb * c

/-- The mass-action rate of the complex, `c' = k₁ e s - (kb + k₂) c`. -/
def complexRate (k₁ kb k₂ s c e : ℝ) : ℝ :=
  k₁ * e * s - (kb + k₂) * c

/-- A solution of the Michaelis–Menten mass-action system on `[0, ∞)`:
`s' = -k₁ e s + kb c`, `c' = k₁ e s - (kb + k₂) c`, `e' = -c'`, `p' = k₂ c`. -/
structure IsSolution (k₁ kb k₂ : ℝ) (s c e p : ℝ → ℝ) : Prop where
  hasDerivAt_substrate : ∀ t, 0 ≤ t → HasDerivAt s (substrateRate k₁ kb (s t) (c t) (e t)) t
  hasDerivAt_complex : ∀ t, 0 ≤ t →
    HasDerivAt c (complexRate k₁ kb k₂ (s t) (c t) (e t)) t
  hasDerivAt_enzyme : ∀ t, 0 ≤ t →
    HasDerivAt e (-complexRate k₁ kb k₂ (s t) (c t) (e t)) t
  hasDerivAt_product : ∀ t, 0 ≤ t → HasDerivAt p (k₂ * c t) t

/-- A function with zero derivative on `[0, ∞)` is constant there. -/
private lemma eq_of_hasDerivAt_zero {f : ℝ → ℝ} (hf : ∀ t, 0 ≤ t → HasDerivAt f 0 t) {t : ℝ}
    (ht : 0 ≤ t) : f t = f 0 := by
  refine constant_of_has_deriv_right_zero (fun x hx ↦ (hf x hx.1).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hf x hx.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩

/-- **Enzyme conservation**: `e(t) + c(t) = e(0) + c(0)`. -/
theorem IsSolution.enzyme_conservation {k₁ kb k₂ : ℝ} {s c e p : ℝ → ℝ}
    (h : IsSolution k₁ kb k₂ s c e p) {t : ℝ} (ht : 0 ≤ t) : e t + c t = e 0 + c 0 := by
  refine eq_of_hasDerivAt_zero (f := fun t ↦ e t + c t) (fun x hx ↦ ?_) ht
  simpa using (h.hasDerivAt_enzyme x hx).fun_add (h.hasDerivAt_complex x hx)

/-- **Mass conservation**: `s(t) + c(t) + p(t) = s(0) + c(0) + p(0)`. -/
theorem IsSolution.substrate_conservation {k₁ kb k₂ : ℝ} {s c e p : ℝ → ℝ}
    (h : IsSolution k₁ kb k₂ s c e p) {t : ℝ} (ht : 0 ≤ t) :
    s t + c t + p t = s 0 + c 0 + p 0 := by
  refine eq_of_hasDerivAt_zero (f := fun t ↦ s t + c t + p t) (fun x hx ↦ ?_) ht
  convert ((h.hasDerivAt_substrate x hx).fun_add (h.hasDerivAt_complex x hx)).fun_add
    (h.hasDerivAt_product x hx) using 1
  simp only [substrateRate, complexRate]; ring

/-- The quasi-steady-state value of the complex, `c = e₀ s / (K_M + s)`. -/
noncomputable def qssComplex (k₁ kb k₂ e₀ s : ℝ) : ℝ :=
  e₀ * s / (michaelisConstant k₁ kb k₂ + s)

/-- The Michaelis–Menten rate law `v(s) = V_max s / (K_M + s)`. -/
noncomputable def mmRate (Vmax KM s : ℝ) : ℝ :=
  Vmax * s / (KM + s)

/-- **Quasi-steady-state manifold.** With total enzyme `e₀` (so `e = e₀ - c`), `k₁ > 0` and
`K_M + s ≠ 0`, the complex is stationary iff `c = e₀ s / (K_M + s)`. -/
theorem complexRate_eq_zero_iff {k₁ kb k₂ e₀ s c : ℝ} (hk₁ : 0 < k₁)
    (hs : michaelisConstant k₁ kb k₂ + s ≠ 0) :
    complexRate k₁ kb k₂ s c (e₀ - c) = 0 ↔ c = qssComplex k₁ kb k₂ e₀ s := by
  unfold complexRate qssComplex
  rw [eq_div_iff hs]
  unfold michaelisConstant at hs ⊢
  have hk : k₁ ≠ 0 := hk₁.ne'
  constructor
  · intro h; field_simp; linarith
  · intro h; field_simp at h; linarith

/-- **Briggs–Haldane rate law.** On the quasi-steady-state manifold the product forms at rate
`k₂ c = V_max s / (K_M + s)`, `V_max = k₂ e₀`. -/
theorem productRate_qss (k₁ kb k₂ e₀ s : ℝ) :
    k₂ * qssComplex k₁ kb k₂ e₀ s = mmRate (k₂ * e₀) (michaelisConstant k₁ kb k₂) s := by
  unfold qssComplex mmRate; ring

/-- On the quasi-steady-state manifold the substrate is consumed at the Michaelis–Menten rate:
`s' = -V_max s / (K_M + s)`. -/
theorem substrateRate_qss {k₁ kb k₂ e₀ s : ℝ} (hk₁ : 0 < k₁)
    (hs : michaelisConstant k₁ kb k₂ + s ≠ 0) :
    substrateRate k₁ kb s (qssComplex k₁ kb k₂ e₀ s) (e₀ - qssComplex k₁ kb k₂ e₀ s) =
      -mmRate (k₂ * e₀) (michaelisConstant k₁ kb k₂) s := by
  have h0 := (complexRate_eq_zero_iff (e₀ := e₀) hk₁ hs).2 rfl
  rw [← productRate_qss]
  unfold complexRate at h0
  unfold substrateRate
  linarith

/-- The rate law is strictly increasing on `s ≥ 0` for `V_max, K_M > 0`. -/
theorem mmRate_strictMono {Vmax KM : ℝ} (hV : 0 < Vmax) (hK : 0 < KM) :
    StrictMonoOn (mmRate Vmax KM) (Ici 0) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  unfold mmRate
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith [mul_pos (mul_pos hV hK) (sub_pos.2 hxy)]

/-- The Michaelis constant is the half-saturation substrate level: `v(K_M) = V_max / 2`. -/
theorem mmRate_michaelisConstant {Vmax KM : ℝ} (hK : KM ≠ 0) :
    mmRate Vmax KM KM = Vmax / 2 := by
  unfold mmRate
  rw [div_eq_div_iff (by intro h; apply hK; linarith) two_ne_zero]
  ring

/-- The rate law is below its maximum: `v(s) < V_max` for `s ≥ 0`, `V_max, K_M > 0`. -/
theorem mmRate_lt {Vmax KM s : ℝ} (hV : 0 < Vmax) (hK : 0 < KM) (hs : 0 ≤ s) :
    mmRate Vmax KM s < Vmax := by
  unfold mmRate
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- Saturation: `v(s) → V_max` as `s → ∞`. -/
theorem tendsto_mmRate (Vmax KM : ℝ) :
    Tendsto (mmRate Vmax KM) atTop (𝓝 Vmax) := by
  have h1 : Tendsto (fun s : ℝ ↦ KM + s) atTop atTop := tendsto_atTop_add_const_left _ _ tendsto_id
  have h2 : Tendsto (fun s : ℝ ↦ Vmax * KM / (KM + s)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1
  have h3 := (tendsto_const_nhds (x := Vmax)).sub h2
  rw [sub_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (-KM)] with s hs
  have : KM + s ≠ 0 := by linarith
  unfold mmRate
  field_simp
  ring

/-- The fast transient of the complex with the substrate frozen at `s̄`:
`c(t) = c* + (c₀ - c*) e^{-k₁ (s̄ + K_M) t}`, where `c* = e₀ s̄ / (K_M + s̄)`. -/
noncomputable def fastTransient (k₁ kb k₂ e₀ s c₀ t : ℝ) : ℝ :=
  qssComplex k₁ kb k₂ e₀ s + (c₀ - qssComplex k₁ kb k₂ e₀ s) *
    exp (-(k₁ * (s + michaelisConstant k₁ kb k₂)) * t)

/-- The fast transient solves the boundary-layer equation `c' = k₁ (e₀ - c) s̄ - (kb + k₂) c`
for `k₁ > 0` and `K_M + s̄ ≠ 0`. -/
theorem hasDerivAt_fastTransient {k₁ kb k₂ e₀ s : ℝ} (hk₁ : 0 < k₁)
    (hs : michaelisConstant k₁ kb k₂ + s ≠ 0) (c₀ t : ℝ) :
    HasDerivAt (fastTransient k₁ kb k₂ e₀ s c₀)
      (complexRate k₁ kb k₂ s (fastTransient k₁ kb k₂ e₀ s c₀ t)
        (e₀ - fastTransient k₁ kb k₂ e₀ s c₀ t)) t := by
  have h := ((((hasDerivAt_id' t).const_mul (-(k₁ * (s + michaelisConstant k₁ kb k₂)))).exp
    ).const_mul (c₀ - qssComplex k₁ kb k₂ e₀ s)).const_add (qssComplex k₁ kb k₂ e₀ s)
  unfold fastTransient
  convert h using 1
  have hk : k₁ ≠ 0 := hk₁.ne'
  set Q := qssComplex k₁ kb k₂ e₀ s
  set E := exp (-(k₁ * (s + michaelisConstant k₁ kb k₂)) * t)
  have hr : k₁ * (s + michaelisConstant k₁ kb k₂) = k₁ * s + kb + k₂ := by
    unfold michaelisConstant; field_simp; ring
  have hQ : k₁ * (s + michaelisConstant k₁ kb k₂) * Q = k₁ * e₀ * s := by
    simp only [Q, qssComplex]; rw [add_comm s]; field_simp
  unfold complexRate
  linear_combination (-1 : ℝ) * hQ + (Q + (c₀ - Q) * E) * hr

/-- The fast transient converges to the quasi-steady-state value for `k₁ > 0` and
`s̄ + K_M > 0`. -/
theorem tendsto_fastTransient {k₁ kb k₂ e₀ s : ℝ} (hk₁ : 0 < k₁)
    (hs : 0 < s + michaelisConstant k₁ kb k₂) (c₀ : ℝ) :
    Tendsto (fastTransient k₁ kb k₂ e₀ s c₀) atTop (𝓝 (qssComplex k₁ kb k₂ e₀ s)) := by
  have hr : 0 < k₁ * (s + michaelisConstant k₁ kb k₂) := mul_pos hk₁ hs
  have h : Tendsto (fun t ↦ exp (-(k₁ * (s + michaelisConstant k₁ kb k₂)) * t)) atTop (𝓝 0) :=
    (tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hr)).congr
      (fun t ↦ by simp [neg_mul])
  have h' := (h.const_mul (c₀ - qssComplex k₁ kb k₂ e₀ s)).const_add (qssComplex k₁ kb k₂ e₀ s)
  rw [mul_zero, add_zero] at h'
  exact h'

end MathlibExt.Biology.Dynamics.MichaelisMenten
