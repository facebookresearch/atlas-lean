/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.SIRExistence
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Long-time behaviour of the SIR system

Along a nonnegative solution of the Kermack–McKendrick system
(`MathlibExt.Biology.Epidemiology.SIR.IsSolution`) with `β ≥ 0`, `γ > 0`, `N ≥ 0`:

* `IsSolution.antitoneOn_susceptible`, `IsSolution.monotoneOn_removed`: `S` decreases and `R`
  increases on `[0, ∞)`.
* `IsSolution.tendsto_final_size`: `S(t) → S∞`, `I(t) → 0`, `R(t) → R∞`, with
  `0 ≤ S∞ ≤ S(0)`, `S∞ + R∞ = S(0) + I(0) + R(0)` and the final-size relation
  `S∞ = S(0) e^{-R₀ (S(0) + I(0) - S∞) / N}` (`R₀ = β / γ`), obtained from
  `IsSolution.final_size`.
* `final_size_root_unique`: for `I₀ > 0` the final-size equation has at most one root `x ≤ S₀`,
  so `S∞` is determined by the initial data.

`I(t) → 0` holds because a positive limit `L` would give `R' = γ I ≥ γ L / 2` eventually, so
`R` would grow without bound, while `R ≤ S(0) + I(0) + R(0)`. Root uniqueness uses convexity of
`x ↦ S₀ e^{-R₀ (S₀ + I₀ - x) / N} - x` and its negative value at `x = S₀`.

Combined with `exists_isSolution_nonneg`, every nonnegative initial state yields a solution with
these limits.
-/

@[expose] public section

open Set Filter Real
open scoped Topology

namespace MathlibExt.Biology.Epidemiology.SIR

/-- A function with derivative `f' t ≥ 0` at every `t ≥ a` is monotone on `[a, ∞)`. -/
private theorem monotoneOn_Ici_of_hasDerivAt {f f' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ t, a ≤ t → HasDerivAt f (f' t) t) (hf' : ∀ t, a < t → 0 ≤ f' t) :
    MonotoneOn f (Ici a) :=
  monotoneOn_of_deriv_nonneg (convex_Ici a)
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => by
      rw [interior_Ici] at ht
      exact (hf t (le_of_lt ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [interior_Ici] at ht
      rw [(hf t (le_of_lt ht)).deriv]
      exact hf' t ht)

namespace IsSolution

variable {β γ N : ℝ} {S I R : ℝ → ℝ}

/-- For `β ≥ 0`, `N ≥ 0` and nonnegative initial compartments (`γ ≥ 0`), `S` is antitone on
`[0, ∞)`. -/
theorem antitoneOn_susceptible (h : IsSolution β γ N S I R) (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hN : 0 ≤ N) (hS : 0 ≤ S 0) (hI : 0 ≤ I 0) (hR : 0 ≤ R 0) :
    AntitoneOn S (Ici 0) := by
  have := monotoneOn_Ici_of_hasDerivAt (f := fun t => -S t) (a := 0)
    (fun t ht => (h.hasDerivAt_susceptible t ht).neg) (fun t ht => by
      obtain ⟨hSt, hIt, -⟩ := h.nonneg hγ hS hI hR ht.le
      simp only [neg_neg]
      positivity)
  exact fun x hx y hy hxy => neg_le_neg_iff.1 (this hx hy hxy)

/-- For `γ ≥ 0` and nonnegative initial compartments, `R` is monotone on `[0, ∞)`. -/
theorem monotoneOn_removed (h : IsSolution β γ N S I R) (hγ : 0 ≤ γ) (hS : 0 ≤ S 0)
    (hI : 0 ≤ I 0) (hR : 0 ≤ R 0) : MonotoneOn R (Ici 0) :=
  monotoneOn_Ici_of_hasDerivAt h.hasDerivAt_removed fun _ ht =>
    mul_nonneg hγ (h.nonneg hγ hS hI hR ht.le).2.1

/-- **Limits and final size.** Along a solution with `β ≥ 0`, `γ > 0`, `N ≥ 0` and nonnegative
initial compartments, `S(t) → S∞`, `I(t) → 0` and `R(t) → R∞` as `t → ∞`, with
`0 ≤ S∞ ≤ S(0)`, `S∞ + R∞ = S(0) + I(0) + R(0)`, and the final-size relation
`S∞ = S(0) e^{-R₀ (S(0) + I(0) - S∞) / N}` (`R₀ = β / γ`; no assumption on `R(0)`). -/
theorem tendsto_final_size (h : IsSolution β γ N S I R) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hN : 0 ≤ N) (hS : 0 ≤ S 0) (hI : 0 ≤ I 0) (hR : 0 ≤ R 0) :
    ∃ Sinf Rinf : ℝ, Tendsto S atTop (𝓝 Sinf) ∧ Tendsto I atTop (𝓝 0) ∧
      Tendsto R atTop (𝓝 Rinf) ∧ 0 ≤ Sinf ∧ Sinf ≤ S 0 ∧ Sinf + Rinf = S 0 + I 0 + R 0 ∧
      Sinf = S 0 * exp (-(β / γ * (S 0 + I 0 - Sinf) / N)) := by
  set P := S 0 + I 0 + R 0 with hP
  have hnn := fun t (ht : 0 ≤ t) => h.nonneg hγ.le hS hI hR ht
  have hanti := h.antitoneOn_susceptible hβ hγ.le hN hS hI hR
  have hmono := h.monotoneOn_removed hγ.le hS hI hR
  have hRle : ∀ t, 0 ≤ t → R t ≤ P := fun t ht => by
    have := h.total_eq ht
    have := hnn t ht
    linarith
  have hmax : ∀ t : ℝ, max t 0 ∈ Ici (0 : ℝ) := fun t => le_max_right t 0
  have hev : ∀ F : ℝ → ℝ, (fun t => F (max t 0)) =ᶠ[atTop] F :=
    fun F => eventually_atTop.2 ⟨0, fun t ht => by simp only [max_eq_left ht]⟩
  -- `S` converges.
  have hSlim : Tendsto S atTop (𝓝 (⨅ t, S (max t 0))) :=
    (tendsto_atTop_ciInf (f := fun t => S (max t 0))
      (fun a b hab => hanti (hmax a) (hmax b) (max_le_max hab le_rfl))
      ⟨0, by rintro _ ⟨t, rfl⟩; exact (hnn _ (hmax t)).1⟩).congr' (hev S)
  -- `R` converges.
  have hRlim : Tendsto R atTop (𝓝 (⨆ t, R (max t 0))) :=
    (tendsto_atTop_ciSup (f := fun t => R (max t 0))
      (fun a b hab => hmono (hmax a) (hmax b) (max_le_max hab le_rfl))
      ⟨P, by rintro _ ⟨t, rfl⟩; exact hRle _ (hmax t)⟩).congr' (hev R)
  set Sinf := ⨅ t, S (max t 0)
  set Rinf := ⨆ t, R (max t 0)
  have hIL : Tendsto I atTop (𝓝 (P - Sinf - Rinf)) :=
    ((tendsto_const_nhds.sub hSlim).sub hRlim).congr' (eventually_atTop.2 ⟨0, fun t ht => by
      have := h.total_eq ht
      linarith⟩)
  have hL0 : 0 ≤ P - Sinf - Rinf :=
    ge_of_tendsto hIL (eventually_atTop.2 ⟨0, fun t ht => (hnn t ht).2.1⟩)
  -- The limit of `I` vanishes: otherwise `R' = γ I` stays above `γ L / 2 > 0`.
  have hL : P - Sinf - Rinf = 0 := by
    by_contra hne
    set L := P - Sinf - Rinf
    have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hne)
    obtain ⟨t₁, ht₁⟩ := eventually_atTop.1 (hIL.eventually_const_lt (half_lt_self hLpos))
    set a := max t₁ 0
    have hF := monotoneOn_Ici_of_hasDerivAt (f := fun t => R t - γ * (L / 2) * t)
      (f' := fun t => γ * I t - γ * (L / 2)) (a := a)
      (fun t ht => (h.hasDerivAt_removed t ((le_max_right t₁ 0).trans ht)).sub
        ((hasDerivAt_id t).const_mul (γ * (L / 2)) |>.congr_deriv (mul_one _)))
      (fun t ht => by
        have := ht₁ t ((le_max_left _ _).trans ht.le)
        nlinarith)
    have hP0 : 0 ≤ P := by positivity
    set t := a + 2 * (P + 1) / (γ * L)
    have hat : a ≤ t := le_add_of_nonneg_right (by positivity)
    have h1 := hF (self_mem_Ici) hat hat
    have h2 : γ * (L / 2) * (t - a) = P + 1 := by
      simp only [t, add_sub_cancel_left]
      field_simp
    have h3 := hRle t ((le_max_right _ _).trans hat)
    have h4 := (hnn a (le_max_right _ _)).2.2
    simp only at h1
    nlinarith
  refine ⟨Sinf, Rinf, hSlim, hL ▸ hIL, hRlim,
    ge_of_tendsto hSlim (eventually_atTop.2 ⟨0, fun t ht => (hnn t ht).1⟩),
    le_of_tendsto hSlim (eventually_atTop.2 ⟨0, fun t ht => hanti self_mem_Ici ht ht⟩),
    by linarith, ?_⟩
  have hfs := h.final_size hγ.ne' hSlim hRlim
  rwa [show Rinf - R 0 = S 0 + I 0 - Sinf by linarith] at hfs

end IsSolution

/-- Two roots `a < b ≤ S₀` of `z = S₀ e^{-k (S₀ + I₀ - z)}` (`k, S₀, I₀ > 0`) are impossible:
`φ(z) = S₀ e^{-k (S₀ + I₀ - z)} - z` is convex with `φ(S₀) < 0`. -/
private theorem final_size_two_roots_false {k S₀ I₀ a b : ℝ} (hk : 0 < k) (hS₀ : 0 < S₀)
    (hI₀ : 0 < I₀) (hab : a < b) (hb : b ≤ S₀)
    (ha_eq : a = S₀ * exp (-(k * (S₀ + I₀ - a))))
    (hb_eq : b = S₀ * exp (-(k * (S₀ + I₀ - b)))) : False := by
  have hφS : S₀ * exp (-(k * I₀)) < S₀ :=
    mul_lt_of_lt_one_right hS₀ (exp_lt_one_iff.2 (by nlinarith))
  rcases hb.lt_or_eq with hb | hbS
  · have hd : 0 < S₀ - a := by linarith
    set μ := (S₀ - b) / (S₀ - a)
    set ν := (b - a) / (S₀ - a)
    have hμ : 0 ≤ μ := div_nonneg (by linarith) hd.le
    have hν : 0 < ν := div_pos (by linarith) hd
    have hμν : μ + ν = 1 := by
      simp only [μ, ν]
      field_simp
      ring
    have hcomb : μ * a + ν * S₀ = b := by
      simp only [μ, ν]
      field_simp
      ring
    have hconv := convexOn_exp.2 (mem_univ (-(k * (S₀ + I₀ - a)))) (mem_univ (-(k * I₀)))
      hμ hν.le hμν
    simp only [smul_eq_mul] at hconv
    have harg : μ * -(k * (S₀ + I₀ - a)) + ν * -(k * I₀) = -(k * (S₀ + I₀ - b)) := by
      rw [← hcomb]
      linear_combination (-(k * (I₀ + S₀))) * hμν
    rw [harg] at hconv
    have key : b ≤ μ * a + ν * (S₀ * exp (-(k * I₀))) :=
      calc b = S₀ * exp (-(k * (S₀ + I₀ - b))) := hb_eq
        _ ≤ S₀ * (μ * exp (-(k * (S₀ + I₀ - a))) + ν * exp (-(k * I₀))) :=
          mul_le_mul_of_nonneg_left hconv hS₀.le
        _ = μ * (S₀ * exp (-(k * (S₀ + I₀ - a)))) + ν * (S₀ * exp (-(k * I₀))) := by ring
        _ = μ * a + ν * (S₀ * exp (-(k * I₀))) := by rw [← ha_eq]
    linarith [mul_lt_mul_of_pos_left hφS hν]
  · rw [hbS, show S₀ + I₀ - S₀ = I₀ by ring] at hb_eq
    linarith

/-- **Uniqueness of the final size.** For `β ≥ 0`, `γ > 0`, `N > 0`, `S₀ ≥ 0` and `I₀ > 0`, the
final-size equation `x = S₀ e^{-R₀ (S₀ + I₀ - x) / N}` (`R₀ = β / γ`) has at most one root
`x ≤ S₀`. For `β = 0` the root is `S₀`. For `I₀ = 0`, `x = S₀` is always a root, and for
`R₀ S₀ / N > 1` there is a second one in `(0, S₀)` (not formalized here), so `I₀ > 0` is needed. -/
theorem final_size_root_unique {β γ N S₀ I₀ x y : ℝ} (hβ : 0 ≤ β) (hγ : 0 < γ) (hN : 0 < N)
    (hS₀ : 0 ≤ S₀) (hI₀ : 0 < I₀) (hx : x ≤ S₀) (hy : y ≤ S₀)
    (hxe : x = S₀ * exp (-(β / γ * (S₀ + I₀ - x) / N)))
    (hye : y = S₀ * exp (-(β / γ * (S₀ + I₀ - y) / N))) : x = y := by
  rcases hβ.eq_or_lt with rfl | hβ
  · simp only [zero_div, zero_mul, neg_zero, exp_zero, mul_one] at hxe hye
    rw [hxe, hye]
  rcases hS₀.eq_or_lt with rfl | hS₀
  · simp only [zero_mul] at hxe hye
    rw [hxe, hye]
  have hk : 0 < β / γ / N := by positivity
  have hconv : ∀ z, -(β / γ * (S₀ + I₀ - z) / N) = -(β / γ / N * (S₀ + I₀ - z)) :=
    fun z => by ring
  rw [hconv] at hxe hye
  rcases lt_trichotomy x y with h | h | h
  · exact (final_size_two_roots_false hk hS₀ hI₀ h hy hxe hye).elim
  · exact h
  · exact (final_size_two_roots_false hk hS₀ hI₀ h hx hye hxe).elim

end MathlibExt.Biology.Epidemiology.SIR
