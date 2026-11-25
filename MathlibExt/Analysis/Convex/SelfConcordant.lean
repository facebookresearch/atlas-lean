/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Self-concordant functions and barriers

Self-concordance (Nesterov and Nemirovski) is the property behind the polynomial-time complexity
of interior-point methods: the third derivative of a convex function is bounded by its second
derivative in the local norm `|h|_x = (D²F(x)[h, h])^{1/2}` that the function defines itself,
`|D³F(x)[h, h, h]| ≤ 2 (D²F(x)[h, h])^{3/2}`, so that Newton's method behaves the same way in
every affine coordinate system. A self-concordant barrier with parameter `ϑ` also has its first
derivative bounded in the local norm, `|DF(x)[h]| ≤ ϑ^{1/2} |h|_x`; path-following methods
for a domain with a `ϑ`-self-concordant barrier need `O(√ϑ log (1/ε))` Newton steps.

Following A. Nemirovski, *Interior Point Polynomial Time Methods in Convex Programming*, lecture
notes (Georgia Tech, 2004), Definitions 2.0.1 and 3.1.1, the directional derivatives
`DᵏF(x)[h, …, h]` are written as the derivatives at `0` of the restriction `t ↦ F (x + t h)` to
the line through `x` in direction `h`, which is what `DᵏF(x)[h, …, h]` denotes there.

* `IsSelfConcordant F Q`: `F` is self-concordant on the open convex set `Q`.
* `IsSelfConcordantBarrier F Q ϑ`: `F` is a `ϑ`-self-concordant barrier for the closure of `Q`.
* `isSelfConcordantBarrier_neg_log`: `-log` is a `1`-self-concordant barrier for the ray
  `[0, ∞)` (Examples 2.1.2 and 3.1.2).
-/

@[expose] public section

open Filter Set Topology

namespace MathlibExt.Analysis.Convex.SelfConcordant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Self-concordant function.** A function `F : E → ℝ` is self-concordant on a nonempty open
convex set `Q` if it is `C³` and convex on `Q`, tends to `+∞` at every boundary point of `Q`
from inside `Q` (barrier property), and satisfies the differential inequality
`|D³F(x)[h, h, h]| ≤ 2 (D²F(x)[h, h])^{3/2}` for all `x ∈ Q` and all directions `h`, where
`DᵏF(x)[h, …, h]` is the `k`-th derivative at `0` of `t ↦ F (x + t h)`.
This is Definition 2.0.1 of A. Nemirovski, *Interior Point Polynomial Time Methods in Convex
Programming*, lecture notes (2004), stated there on `ℝⁿ`; here on a real normed space `E`. -/
def IsSelfConcordant (F : E → ℝ) (Q : Set E) : Prop :=
  Q.Nonempty ∧ IsOpen Q ∧ Convex ℝ Q ∧ ContDiffOn ℝ 3 F Q ∧ ConvexOn ℝ Q F ∧
    (∀ x ∈ frontier Q, Tendsto F (𝓝[Q] x) atTop) ∧
    ∀ x ∈ Q, ∀ h : E, |iteratedDeriv 3 (fun t : ℝ => F (x + t • h)) 0| ≤
      2 * iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0 ^ (3 / 2 : ℝ)

/-- **Self-concordant barrier.** For `ϑ ≥ 0`, `F` is a `ϑ`-self-concordant barrier for the
closed convex domain `closure Q` (with interior `Q`) if `F` is self-concordant on `Q` and
`|DF(x)[h]| ≤ ϑ^{1/2} (D²F(x)[h, h])^{1/2}` for all `x ∈ Q` and all `h`, i.e. the Newton
decrement of `F` is at most `ϑ^{1/2}` everywhere.
This is Definition 3.1.1 of A. Nemirovski, *Interior Point Polynomial Time Methods in Convex
Programming*, lecture notes (2004), where the barrier is defined on the interior `int G` of a
closed convex domain `G`; here `Q` plays the role of `int G`. -/
def IsSelfConcordantBarrier (F : E → ℝ) (Q : Set E) (ϑ : ℝ) : Prop :=
  0 ≤ ϑ ∧ IsSelfConcordant F Q ∧
    ∀ x ∈ Q, ∀ h : E, |deriv (fun t : ℝ => F (x + t • h)) 0| ≤
      √ϑ * √(iteratedDeriv 2 (fun t : ℝ => F (x + t • h)) 0)

/-- On an open set, a function that agrees with `g` and has derivative `g'` there has, at each
point of the set, its derivative equal to `g'`. -/
private lemma deriv_eq_of_eqOn {U : Set ℝ} (hU : IsOpen U) {f g g' : ℝ → ℝ}
    (hfg : EqOn f g U) (hg : ∀ t ∈ U, HasDerivAt g (g' t) t) : EqOn (deriv f) g' U := by
  intro t ht
  rw [Filter.EventuallyEq.deriv_eq (hfg.eventuallyEq_of_mem (hU.mem_nhds ht))]
  exact (hg t ht).deriv

/-- **`-log` is a `1`-self-concordant barrier for the nonnegative ray.** The function
`F(x) = -log x` is self-concordant on `(0, ∞)` and satisfies `|F'(x) h| ≤ (F''(x) h²)^{1/2}`:
along a line, `D²F(x)[h, h] = h² / x²`, `D³F(x)[h, h, h] = -2 h³ / x³` and `DF(x)[h] = -h / x`.
This is Example 2.1.2 (self-concordance of `-ln t` on the positive ray) and Example 3.1.2 (a
self-concordant barrier with parameter `1` for the nonnegative ray) of A. Nemirovski, *Interior
Point Polynomial Time Methods in Convex Programming*, lecture notes (2004). -/
theorem isSelfConcordantBarrier_neg_log :
    IsSelfConcordantBarrier (fun x : ℝ => -Real.log x) (Ioi 0) 1 := by
  -- Derivatives of `t ↦ -log (x + t h)` near `t = 0`.
  have key : ∀ x : ℝ, 0 < x → ∀ h : ℝ,
      deriv (fun t : ℝ => -Real.log (x + t • h)) 0 = -h / x ∧
      iteratedDeriv 2 (fun t : ℝ => -Real.log (x + t • h)) 0 = (|h| / x) ^ 2 ∧
      iteratedDeriv 3 (fun t : ℝ => -Real.log (x + t • h)) 0 = -2 * h ^ 3 / x ^ 3 := by
    intro x hx h
    set U : Set ℝ := {t | 0 < x + t * h} with hUdef
    have hU : IsOpen U := isOpen_lt continuous_const (continuous_const.add
      (continuous_id.mul continuous_const))
    have h0 : (0 : ℝ) ∈ U := by simp [hUdef, hx]
    have hlin : ∀ t, HasDerivAt (fun s : ℝ => x + s * h) h t := fun t => by
      simpa using ((hasDerivAt_id t).mul_const h).const_add x
    set φ : ℝ → ℝ := fun t => -Real.log (x + t • h) with hφ
    set g1 : ℝ → ℝ := fun t => -h * (x + t * h)⁻¹
    set g2 : ℝ → ℝ := fun t => h ^ 2 * ((x + t * h)⁻¹) ^ 2
    set g3 : ℝ → ℝ := fun t => -2 * h ^ 3 * ((x + t * h)⁻¹) ^ 3
    have hinv : ∀ t ∈ U, HasDerivAt (fun s : ℝ => (x + s * h)⁻¹) (-h / (x + t * h) ^ 2) t := by
      intro t ht
      have hne : x + t * h ≠ 0 := (show 0 < x + t * h from ht).ne'
      exact (hlin t).inv hne
    have d1 : ∀ t ∈ U, HasDerivAt φ (g1 t) t := by
      intro t ht
      have hne : x + t * h ≠ 0 := (show 0 < x + t * h from ht).ne'
      have := ((hlin t).log hne).neg
      convert this using 1
      simp only [g1]; field_simp
    have d2 : ∀ t ∈ U, HasDerivAt g1 (g2 t) t := by
      intro t ht
      have hne : x + t * h ≠ 0 := (show 0 < x + t * h from ht).ne'
      have := (hinv t ht).const_mul (-h)
      convert this using 1
      simp only [g2]; field_simp
    have d3 : ∀ t ∈ U, HasDerivAt g2 (g3 t) t := by
      intro t ht
      have hne : x + t * h ≠ 0 := (show 0 < x + t * h from ht).ne'
      have := ((hinv t ht).pow 2).const_mul (h ^ 2)
      convert this using 1
      have alg : ∀ u : ℝ, u ≠ 0 →
          -2 * h ^ 3 * (u⁻¹) ^ 3 = h ^ 2 * (((2 : ℕ) : ℝ) * u⁻¹ ^ (2 - 1) * (-h / u ^ 2)) := by
        intro u hu
        rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
        push_cast
        field_simp
      exact alg _ hne
    have e1 : EqOn (deriv φ) g1 U := deriv_eq_of_eqOn hU (fun _ _ => rfl) d1
    have e2 : EqOn (deriv (deriv φ)) g2 U := deriv_eq_of_eqOn hU e1 d2
    have e3 : EqOn (deriv (deriv (deriv φ))) g3 U := deriv_eq_of_eqOn hU e2 d3
    have i2 : iteratedDeriv 2 φ = deriv (deriv φ) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    have i3 : iteratedDeriv 3 φ = deriv (deriv (deriv φ)) := by
      rw [iteratedDeriv_succ, i2]
    refine ⟨?_, ?_, ?_⟩
    · rw [e1 h0]; simp only [g1, zero_mul, add_zero]; field_simp
    · rw [i2, e2 h0]; simp only [g2, zero_mul, add_zero]; rw [div_pow, sq_abs]; field_simp
    · rw [i3, e3 h0]; simp only [g3, zero_mul, add_zero]; field_simp
  refine ⟨zero_le_one, ⟨nonempty_Ioi, isOpen_Ioi, convex_Ioi 0, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (Real.contDiffOn_log.mono fun x hx => (ne_of_gt (mem_Ioi.mp hx))).neg
  · exact strictConcaveOn_log_Ioi.concaveOn.neg
  · intro x hx
    rw [frontier_Ioi, mem_singleton_iff] at hx
    subst hx
    exact tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  · intro x hx h
    have hx' : 0 < x := hx
    obtain ⟨-, h2, h3⟩ := key x hx h
    have hp : ((|h| / x) ^ 2) ^ (3 / 2 : ℝ) = (|h| / x) ^ 3 := by
      rw [← Real.rpow_natCast (|h| / x) 2, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [h2, h3, hp, abs_div, abs_mul, abs_pow, abs_of_pos (pow_pos hx' 3), div_pow]
    norm_num
    exact le_of_eq (by ring)
  · intro x hx h
    have hx' : 0 < x := hx
    obtain ⟨h1, h2, -⟩ := key x hx h
    rw [h1, h2, Real.sqrt_one, one_mul, Real.sqrt_sq (by positivity), abs_div, abs_neg,
      abs_of_pos hx']

end MathlibExt.Analysis.Convex.SelfConcordant
