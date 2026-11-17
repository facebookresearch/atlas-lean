/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

/-!
# Control volumes: one-dimensional moving-endpoint transport

## i. Overview

The Leibniz (moving-endpoint transport) identity in one space
dimension: for a jointly `C¹` field `u t x` and `C¹` endpoints
`a, b`,
`d/dt ∫_{a t}^{b t} u t x dx = ∫_{a t}^{b t} u_t dx
+ u(t, b t) b'(t) - u(t, a t) a'(t)`, and, when
`u_t = src - f_x`, the relative-flux form with endpoint terms
`f - u * endpointSpeed`. Joint `C¹` control is essential:
slice-wise continuity plus fixed-limit differentiation alone
admit oscillating mass at the moving endpoint. No general
moving-domain Reynolds theorem is claimed.

## ii. Key results

- `ControlVolumes.movingEndpoint_deriv`: the Leibniz identity
  for oriented integrals (no endpoint ordering needed).
- `ControlVolumes.movingEndpoint_deriv_flux`: the relative-flux
  form exposing `f - u * endpointSpeed` at both ends.

## iii. Table of contents

- A. Moving-endpoint transport

## iv. References

- The classical Leibniz integral rule; the statement is
  self-contained.

## A. Moving-endpoint transport

-/

@[expose] public section

namespace ControlVolumes

private lemma slice_continuous_u {u : ℝ → ℝ → ℝ}
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2) (τ : ℝ) :
    Continuous fun x : ℝ => u τ x :=
  hjoint.comp (continuous_const.prodMk continuous_id)

private lemma hasDerivAt_endpoint_integral {u ut : ℝ → ℝ → ℝ} {c c' : ℝ → ℝ}
    (hc : ∀ t : ℝ, HasDerivAt c (c' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hswap : ∀ t y : ℝ,
      HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..y, u τ x)
        (∫ x in (0 : ℝ)..y, ut t x) t)
    (t : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..c τ, u τ x)
      ((∫ x in (0 : ℝ)..c t, ut t x) + u t (c t) * c' t) t := by
  have hslice : ∀ τ : ℝ, Continuous fun x : ℝ => u τ x :=
    fun τ => hjoint.comp (continuous_const.prodMk continuous_id)
  have hE1 : ∀ τ : ℝ,
      (∫ x in (0 : ℝ)..c τ, u τ x) - (∫ x in (0 : ℝ)..c t, u τ x)
        - u t (c t) * (c τ - c t)
        = ∫ x in c t..c τ, (u τ x - u t (c t)) := by
    intro τ
    have h1 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume (c t) 0 :=
      (hslice τ).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume 0 (c τ) :=
      (hslice τ).intervalIntegrable _ _
    have h3 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume (c t) (c τ) :=
      (hslice τ).intervalIntegrable _ _
    have h4 : IntervalIntegrable (fun _ : ℝ => u t (c t)) MeasureTheory.volume (c t) (c τ) :=
      intervalIntegrable_const
    have hadj : (∫ x in c t..(0 : ℝ), u τ x) + (∫ x in (0 : ℝ)..c τ, u τ x)
        = ∫ x in c t..c τ, u τ x :=
      intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hsymm : (∫ x in c t..(0 : ℝ), u τ x) = -(∫ x in (0 : ℝ)..c t, u τ x) :=
      intervalIntegral.integral_symm 0 (c t)
    have hsub : (∫ x in c t..c τ, (u τ x - u t (c t)))
        = (∫ x in c t..c τ, u τ x) - (∫ x in c t..c τ, u t (c t)) :=
      intervalIntegral.integral_sub h3 h4
    have hconst : (∫ x in c t..c τ, u t (c t)) = (c τ - c t) * u t (c t) := by
      have hc0 := intervalIntegral.integral_const (a := c t) (b := c τ) (u t (c t))
      rwa [smul_eq_mul] at hc0
    have eA : (∫ x in (0 : ℝ)..c τ, u τ x) - (∫ x in (0 : ℝ)..c t, u τ x)
        = ∫ x in c t..c τ, u τ x := by
      rw [← hadj, hsymm]; ring
    rw [eA, hsub, hconst]; ring
  have hE1o : (fun τ : ℝ => (∫ x in (0 : ℝ)..c τ, u τ x)
      - (∫ x in (0 : ℝ)..c t, u τ x) - u t (c t) * (c τ - c t))
      =o[nhds t] fun τ : ℝ => τ - t := by
    refine Asymptotics.isLittleO_iff.mpr ?_
    intro c₀ hc₀
    have hK : (0 : ℝ) < ‖c' t‖ + 1 := by
      have hnn := norm_nonneg (c' t)
      linarith
    have hKne : (‖c' t‖ + 1 : ℝ) ≠ 0 := ne_of_gt hK
    have hε0 : (0 : ℝ) < c₀ / (‖c' t‖ + 1) := div_pos hc₀ hK
    have hcont_at : ContinuousAt (fun p : ℝ × ℝ => u p.1 p.2) (t, c t) :=
      hjoint.continuousAt
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hcont_at _ hε0
    have e1 : ∀ᶠ τ in nhds t, τ ∈ Metric.ball t δ :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds t hδ0) (fun _ h => h)
    have e2 : ∀ᶠ τ in nhds t, c τ ∈ Metric.ball (c t) δ :=
      (hc t).continuousAt.eventually_mem (Metric.ball_mem_nhds _ hδ0)
    have hco := HasDerivAt.isLittleO (hc t)
    have eK : ∀ᶠ τ in nhds t, ‖c τ - c t - (τ - t) • c' t‖ ≤ 1 * ‖τ - t‖ :=
      hco.def zero_lt_one
    filter_upwards [e1, e2, eK] with τ hτ hcτ hKτ
    rw [Metric.mem_ball, Real.dist_eq] at hτ hcτ
    have hmem : ∀ x ∈ Set.uIoc (c t) (c τ),
        ‖u τ x - u t (c t)‖ ≤ c₀ / (‖c' t‖ + 1) := by
      intro x hx
      have hxcc : x ∈ Set.uIcc (c t) (c τ) := Set.uIoc_subset_uIcc hx
      have hxc : |x - c t| ≤ |c τ - c t| := Set.abs_sub_left_of_mem_uIcc hxcc
      have hdist : dist (τ, x) (t, c t) < δ := by
        rw [Prod.dist_eq]
        show max |τ - t| |x - c t| < δ
        exact max_lt hτ (lt_of_le_of_lt hxc hcτ)
      have hclose : |u τ x - u t (c t)| < c₀ / (‖c' t‖ + 1) := hδ hdist
      rw [Real.norm_eq_abs]
      exact le_of_lt hclose
    have hI : ‖∫ x in c t..c τ, (u τ x - u t (c t))‖
        ≤ (c₀ / (‖c' t‖ + 1)) * |c τ - c t| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hmem
    have hE1τ := hE1 τ
    have hKd : ‖c τ - c t‖ ≤ (‖c' t‖ + 1) * ‖τ - t‖ := by
      have hexpand : c τ - c t = (c τ - c t - (τ - t) • c' t) + (τ - t) * c' t := by
        rw [smul_eq_mul]; ring
      calc ‖c τ - c t‖
          = ‖(c τ - c t - (τ - t) • c' t) + (τ - t) * c' t‖ :=
            congrArg Norm.norm hexpand
        _ ≤ ‖c τ - c t - (τ - t) • c' t‖ + ‖(τ - t) * c' t‖ := norm_add_le _ _
        _ ≤ 1 * ‖τ - t‖ + ‖τ - t‖ * ‖c' t‖ := by
            rw [norm_mul]; exact add_le_add hKτ le_rfl
        _ = (‖c' t‖ + 1) * ‖τ - t‖ := by ring
    have hεK : c₀ / (‖c' t‖ + 1) * (‖c' t‖ + 1) = c₀ :=
      div_mul_cancel₀ _ hKne
    show ‖(∫ x in (0 : ℝ)..c τ, u τ x) - (∫ x in (0 : ℝ)..c t, u τ x)
        - u t (c t) * (c τ - c t)‖ ≤ c₀ * ‖τ - t‖
    rw [hE1τ]
    calc ‖∫ x in c t..c τ, (u τ x - u t (c t))‖
        ≤ (c₀ / (‖c' t‖ + 1)) * |c τ - c t| := hI
      _ = (c₀ / (‖c' t‖ + 1)) * ‖c τ - c t‖ := by rw [Real.norm_eq_abs (c τ - c t)]
      _ ≤ (c₀ / (‖c' t‖ + 1)) * ((‖c' t‖ + 1) * ‖τ - t‖) :=
          mul_le_mul_of_nonneg_left hKd (le_of_lt hε0)
      _ = c₀ * ‖τ - t‖ := by rw [← mul_assoc, hεK]
  have hE2o : (fun τ : ℝ => (∫ x in (0 : ℝ)..c t, u τ x)
      - (∫ x in (0 : ℝ)..c t, u t x) - (τ - t) • (∫ x in (0 : ℝ)..c t, ut t x))
      =o[nhds t] fun τ : ℝ => τ - t :=
    HasDerivAt.isLittleO (hswap t (c t))
  have hCo : (fun τ : ℝ => c τ - c t - (τ - t) • c' t)
      =o[nhds t] fun τ : ℝ => τ - t :=
    HasDerivAt.isLittleO (hc t)
  have hsum := (hE1o.add hE2o).add (hCo.const_mul_left (u t (c t)))
  refine HasDerivAt.of_isLittleO
    ((Asymptotics.isLittleO_congr ?hf Filter.EventuallyEq.rfl).mp hsum)
  filter_upwards with τ
  show ((∫ x in (0 : ℝ)..c τ, u τ x) - (∫ x in (0 : ℝ)..c t, u τ x)
      - u t (c t) * (c τ - c t)
      + ((∫ x in (0 : ℝ)..c t, u τ x) - (∫ x in (0 : ℝ)..c t, u t x)
        - (τ - t) • (∫ x in (0 : ℝ)..c t, ut t x)))
      + u t (c t) * (c τ - c t - (τ - t) • c' t)
      = (∫ x in (0 : ℝ)..c τ, u τ x) - (∫ x in (0 : ℝ)..c t, u t x)
        - (τ - t) • ((∫ x in (0 : ℝ)..c t, ut t x) + u t (c t) * c' t)
  simp only [smul_eq_mul]
  ring

/-- Moving-endpoint transport (Leibniz rule): for a jointly smooth
field `u t x` with time partial `ut`, and `C¹` endpoints `a, b`
with derivatives `a', b'`,
`d/dt ∫_{a t}^{b t} u t x dx = ∫_{a t}^{b t} ut t x dx
+ u t (b t) * b' t - u t (a t) * a' t`.
The field is jointly `C¹`: `hjoint` and `hcont_ut` give joint
continuity of `u` and of its time partial `ut` (an actual
derivative, by `hut`). This joint control is essential: slice-wise
continuity plus fixed-limit differentiation alone admit
oscillating mass at the moving endpoint. The hypothesis `hswap`
is the differentiation under the fixed-limit integral; the moving
endpoints enter through the fundamental theorem of calculus and
the chain rule. No ordering `a t < b t` is needed for the identity
as an oriented-integral statement. -/
theorem movingEndpoint_deriv {u ut : ℝ → ℝ → ℝ} {a b a' b' : ℝ → ℝ}
    (ha : ∀ t : ℝ, HasDerivAt a (a' t) t)
    (hb : ∀ t : ℝ, HasDerivAt b (b' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2)
    (hcont : ∀ t y : ℝ, ContinuousOn (fun x : ℝ => u t x)
      (Set.uIcc 0 y))
    (hswap : ∀ t y : ℝ,
      HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..y, u τ x)
        (∫ x in (0 : ℝ)..y, ut t x) t)
    (t : ℝ) :
    deriv (fun τ : ℝ => ∫ x in a τ..b τ, u τ x) t =
      (∫ x in a t..b t, ut t x) + u t (b t) * b' t -
        u t (a t) * a' t := by
  have _ := hut
  have hslice : ∀ τ : ℝ, Continuous fun x : ℝ => u τ x :=
    fun τ => hjoint.comp (continuous_const.prodMk continuous_id)
  have hslice_ut : ∀ τ : ℝ, Continuous fun x : ℝ => ut τ x :=
    fun τ => hcont_ut.comp (continuous_const.prodMk continuous_id)
  have hGb : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..b τ, u τ x)
      ((∫ x in (0 : ℝ)..b t, ut t x) + u t (b t) * b' t) t :=
    hasDerivAt_endpoint_integral hb hjoint hswap t
  have hGa : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..a τ, u τ x)
      ((∫ x in (0 : ℝ)..a t, ut t x) + u t (a t) * a' t) t :=
    hasDerivAt_endpoint_integral ha hjoint hswap t
  have hsplit : ∀ τ : ℝ, (∫ x in a τ..b τ, u τ x)
      = (∫ x in (0 : ℝ)..b τ, u τ x) - (∫ x in (0 : ℝ)..a τ, u τ x) := by
    intro τ
    have h1 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume (a τ) 0 :=
      (hslice τ).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume 0 (b τ) :=
      (hcont τ (b τ)).intervalIntegrable
    have hadj : (∫ x in a τ..(0 : ℝ), u τ x) + (∫ x in (0 : ℝ)..b τ, u τ x)
        = ∫ x in a τ..b τ, u τ x :=
      intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hsymm : (∫ x in a τ..(0 : ℝ), u τ x) = -(∫ x in (0 : ℝ)..a τ, u τ x) :=
      intervalIntegral.integral_symm 0 (a τ)
    rw [← hadj, hsymm]; ring
  have hS : (∫ x in (0 : ℝ)..b t, ut t x) - (∫ x in (0 : ℝ)..a t, ut t x)
      = ∫ x in a t..b t, ut t x := by
    have h1 : IntervalIntegrable (fun x : ℝ => ut t x) MeasureTheory.volume (a t) 0 :=
      (hslice_ut t).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun x : ℝ => ut t x) MeasureTheory.volume 0 (b t) :=
      (hslice_ut t).intervalIntegrable _ _
    have hadj : (∫ x in a t..(0 : ℝ), ut t x) + (∫ x in (0 : ℝ)..b t, ut t x)
        = ∫ x in a t..b t, ut t x :=
      intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hsymm : (∫ x in a t..(0 : ℝ), ut t x) = -(∫ x in (0 : ℝ)..a t, ut t x) :=
      intervalIntegral.integral_symm 0 (a t)
    rw [← hadj, hsymm]; ring
  have heq : (fun τ : ℝ => ∫ x in a τ..b τ, u τ x)
      = (fun τ : ℝ => (∫ x in (0 : ℝ)..b τ, u τ x)
        - (∫ x in (0 : ℝ)..a τ, u τ x)) :=
    funext hsplit
  rw [heq]
  have hderiv : deriv (fun τ : ℝ => (∫ x in (0 : ℝ)..b τ, u τ x)
      - (∫ x in (0 : ℝ)..a τ, u τ x)) t
      = ((∫ x in (0 : ℝ)..b t, ut t x) + u t (b t) * b' t)
        - ((∫ x in (0 : ℝ)..a t, ut t x) + u t (a t) * a' t) :=
    (hGb.sub hGa).deriv
  rw [hderiv, ← hS]; ring

/-- Relative-flux form: if `ut = src - fx` where `fx t` is the
spatial derivative of a flux `f t`, the endpoint terms combine
into relative fluxes `f - u * endpointSpeed`:
`d/dt ∫_{a t}^{b t} u = ∫_{a t}^{b t} src
- (f t (b t) - u t (b t) * b' t) + (f t (a t) - u t (a t) * a' t)`. -/
theorem movingEndpoint_deriv_flux {u ut f fx src : ℝ → ℝ → ℝ}
    {a b a' b' : ℝ → ℝ}
    (ha : ∀ t : ℝ, HasDerivAt a (a' t) t)
    (hb : ∀ t : ℝ, HasDerivAt b (b' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2)
    (hcont : ∀ t y : ℝ, ContinuousOn (fun x : ℝ => u t x)
      (Set.uIcc 0 y))
    (hswap : ∀ t y : ℝ,
      HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..y, u τ x)
        (∫ x in (0 : ℝ)..y, ut t x) t)
    (hfx : ∀ t x : ℝ, HasDerivAt (fun y : ℝ => f t y) (fx t x) x)
    (hcont_fx : ∀ t : ℝ, ContinuousOn (fun x : ℝ => fx t x)
      (Set.uIcc (a t) (b t)))
    (hPDE : ∀ t x : ℝ, ut t x = src t x - fx t x)
    (hint_src : ∀ t : ℝ, IntervalIntegrable (fun x : ℝ => src t x)
      MeasureTheory.volume (a t) (b t))
    (hint_ut : ∀ t : ℝ, IntervalIntegrable (fun x : ℝ => ut t x)
      MeasureTheory.volume (a t) (b t))
    (t : ℝ) :
    deriv (fun τ : ℝ => ∫ x in a τ..b τ, u τ x) t =
      (∫ x in a t..b t, src t x) -
        (f t (b t) - u t (b t) * b' t) +
          (f t (a t) - u t (a t) * a' t) := by
  have _ := hint_ut
  have hmain := movingEndpoint_deriv ha hb hjoint hut hcont_ut hcont hswap t
  have hFTC : (∫ x in a t..b t, fx t x) = f t (b t) - f t (a t) := by
    have hderiv : ∀ x ∈ Set.uIcc (a t) (b t),
        HasDerivAt (fun y : ℝ => f t y) (fx t x) x :=
      fun x _ => hfx t x
    have hint : IntervalIntegrable (fun x : ℝ => fx t x) MeasureTheory.volume (a t) (b t) :=
      (hcont_fx t).intervalIntegrable
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hsplit : (∫ x in a t..b t, ut t x)
      = (∫ x in a t..b t, src t x) - (∫ x in a t..b t, fx t x) := by
    have hfx_int : IntervalIntegrable (fun x : ℝ => fx t x) MeasureTheory.volume (a t) (b t) :=
      (hcont_fx t).intervalIntegrable
    have h : (fun x : ℝ => ut t x) = (fun x : ℝ => src t x - fx t x) :=
      funext (fun x => hPDE t x)
    rw [h]
    exact intervalIntegral.integral_sub (hint_src t) hfx_int
  rw [hmain, hsplit, hFTC]; ring

end ControlVolumes
