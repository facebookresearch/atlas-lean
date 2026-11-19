/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import MathlibExt.Analysis.ODE.ContinuumBalances
import MathlibExt.Probability.Diffusion.FokkerPlanckFreeEnergy
import Mathlib.Tactic.Ring

/-!
# Control volumes: moving-endpoint transport and fixed-box balance

## i. Overview

The Leibniz (moving-endpoint transport) identity in one space
dimension: for a field `u t x` with `u` and its time partial
`u_t` jointly continuous (no spatial derivative of `u` is
assumed) and endpoints `a, b` differentiable at the evaluation
time `t`,
`d/dt ∫_{a t}^{b t} u t x dx = ∫_{a t}^{b t} u_t dx
+ u(t, b t) b'(t) - u(t, a t) a'(t)`, and, when
`u_t = src - f_x`, the relative-flux form with endpoint terms
`f - u * endpointSpeed`. Joint continuity of `u` and `u_t` is
what the proof uses: slice-wise continuity plus fixed-limit
differentiation alone admit oscillating mass at the moving
endpoint. No general moving-domain Reynolds theorem is
claimed.

For a fixed nondegenerate rectangular box `[a, b]` in
`ℝⁿ⁺¹ = Fin (n + 1) → ℝ`, a jointly `C¹` density `u`, a flux `q`
that is `C¹` on an open neighbourhood of the box and the local law
`∂ₜu + div q = s`, the stored amount satisfies
`d/dt ∫_[a, b] u = ∫_[a, b] s - boxOutwardFlux a b (q t)`. The
outward flux is written face by face: the face `x i = b i` has
outward normal `+eᵢ` and the face `x i = a i` has `-eᵢ`, so a
positive `qᵢ` is outflow on the upper face and inflow on the lower
one. Mathlib's divergence theorem for boxes discharges the
boundary-divergence premise of
`MathlibExt.Analysis.ODE.ContinuumBalances.hasDerivAt_setIntegral_of_divergence`;
local conservation stays the model input. No general smooth-domain
trace or divergence theorem is claimed.

## ii. Key results

- `ControlVolumes.movingEndpoint_hasDerivAt`: the Leibniz
  identity in `HasDerivAt` form for oriented integrals (no
  endpoint ordering needed), with differentiation under the
  fixed-limit integral derived from the joint-continuity data.
- `ControlVolumes.movingEndpoint_deriv`: its `deriv` corollary.
- `ControlVolumes.movingEndpoint_hasDerivAt_flux` and
  `movingEndpoint_deriv_flux`: the relative-flux forms exposing
  `f - u * endpointSpeed` at both ends.
- `ControlVolumes.boxOutwardFlux`: the outward flux of a vector
  field through the faces of a box.
- `ControlVolumes.integral_divergence_box`: the divergence theorem
  on a box, `∫_[a, b] div F = boxOutwardFlux a b F`.
- `ControlVolumes.hasDerivAt_boxIntegral`: the fixed-box balance
  with explicit faces.

## iii. Table of contents

- A. Moving-endpoint transport
- B. Fixed-box balance with explicit faces
  - B.1. Faces and the divergence theorem
  - B.2. The balance

## iv. References

- The classical Leibniz integral rule; the statement is
  self-contained.
- Mathlib's divergence theorem for rectangular boxes,
  `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`.
- R. B. Bird, W. E. Stewart and E. N. Lightfoot, *Transport
  Phenomena*, 2nd ed., Wiley (2002), Section 19.1 (the equation of
  continuity for a fixed volume element).

## A. Moving-endpoint transport

-/

@[expose] public section

namespace ControlVolumes

private lemma slice_continuous {w : ℝ → ℝ → ℝ}
    (hjoint : Continuous fun p : ℝ × ℝ => w p.1 p.2) (τ : ℝ) :
    Continuous fun x : ℝ => w τ x :=
  hjoint.comp (continuous_const.prodMk continuous_id)

private lemma hasDerivAt_fixed_integral {u ut : ℝ → ℝ → ℝ}
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2)
    (t y : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..y, u τ x)
      (∫ x in (0 : ℝ)..y, ut t x) t :=
  MathlibExt.Probability.FokkerPlanck.integral_hasDerivAt u ut 0 y t
    hjoint hcont_ut hut

private lemma hasDerivAt_endpoint_integral {u ut : ℝ → ℝ → ℝ} {c c' : ℝ → ℝ}
    (t : ℝ) (hc : HasDerivAt c (c' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2) :
    HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..c τ, u τ x)
      ((∫ x in (0 : ℝ)..c t, ut t x) + u t (c t) * c' t) t := by
  have hswap : ∀ t y : ℝ,
      HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..y, u τ x)
        (∫ x in (0 : ℝ)..y, ut t x) t :=
    fun t y => hasDerivAt_fixed_integral hjoint hut hcont_ut t y
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
      hc.continuousAt.eventually_mem (Metric.ball_mem_nhds _ hδ0)
    have hco := HasDerivAt.isLittleO hc
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
    HasDerivAt.isLittleO hc
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

/-- Moving-endpoint transport (Leibniz rule), `HasDerivAt` form:
for a field `u t x` with `u` and its actual time partial `ut`
jointly continuous and endpoints `a, b` differentiable at `t`,
the moving integral has derivative
`∫_{a t}^{b t} ut t x dx + u t (b t) * b' t - u t (a t) * a' t`
at `t`. Differentiation under the fixed-limit integral is derived
from the joint-continuity data, not assumed. No ordering
`a t < b t` is needed for the oriented-integral statement. -/
theorem movingEndpoint_hasDerivAt {u ut : ℝ → ℝ → ℝ} {a b a' b' : ℝ → ℝ}
    (t : ℝ) (ha : HasDerivAt a (a' t) t) (hb : HasDerivAt b (b' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2) :
    HasDerivAt (fun τ : ℝ => ∫ x in a τ..b τ, u τ x)
      ((∫ x in a t..b t, ut t x) + u t (b t) * b' t -
        u t (a t) * a' t) t := by
  have hslice : ∀ τ : ℝ, Continuous fun x : ℝ => u τ x :=
    fun τ => slice_continuous hjoint τ
  have hslice_ut : ∀ τ : ℝ, Continuous fun x : ℝ => ut τ x :=
    fun τ => slice_continuous hcont_ut τ
  have hGb : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..b τ, u τ x)
      ((∫ x in (0 : ℝ)..b t, ut t x) + u t (b t) * b' t) t :=
    hasDerivAt_endpoint_integral t hb hjoint hut hcont_ut
  have hGa : HasDerivAt (fun τ : ℝ => ∫ x in (0 : ℝ)..a τ, u τ x)
      ((∫ x in (0 : ℝ)..a t, ut t x) + u t (a t) * a' t) t :=
    hasDerivAt_endpoint_integral t ha hjoint hut hcont_ut
  have hsplit : ∀ τ : ℝ, (∫ x in a τ..b τ, u τ x)
      = (∫ x in (0 : ℝ)..b τ, u τ x) - (∫ x in (0 : ℝ)..a τ, u τ x) := by
    intro τ
    have h1 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume (a τ) 0 :=
      (hslice τ).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun x : ℝ => u τ x) MeasureTheory.volume 0 (b τ) :=
      (hslice τ).intervalIntegrable _ _
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
  have hev : (fun τ : ℝ => ∫ x in a τ..b τ, u τ x)
      =ᶠ[nhds t] (fun τ : ℝ => (∫ x in (0 : ℝ)..b τ, u τ x)
        - (∫ x in (0 : ℝ)..a τ, u τ x)) :=
    Filter.Eventually.of_forall hsplit
  have h := (hGb.sub hGa).congr_of_eventuallyEq hev
  have hval : ((∫ x in (0 : ℝ)..b t, ut t x) + u t (b t) * b' t)
      - ((∫ x in (0 : ℝ)..a t, ut t x) + u t (a t) * a' t)
      = (∫ x in a t..b t, ut t x) + u t (b t) * b' t - u t (a t) * a' t := by
    rw [← hS]; ring
  rwa [hval] at h

/-- Moving-endpoint transport, `deriv` form (corollary of
`movingEndpoint_hasDerivAt`). -/
theorem movingEndpoint_deriv {u ut : ℝ → ℝ → ℝ} {a b a' b' : ℝ → ℝ}
    (t : ℝ) (ha : HasDerivAt a (a' t) t) (hb : HasDerivAt b (b' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2) :
    deriv (fun τ : ℝ => ∫ x in a τ..b τ, u τ x) t =
      (∫ x in a t..b t, ut t x) + u t (b t) * b' t -
        u t (a t) * a' t := by
  exact (movingEndpoint_hasDerivAt t ha hb hjoint hut hcont_ut).deriv

/-- Relative-flux form, `HasDerivAt` version: if
`ut = src - fx` where `fx t` is the spatial derivative of a flux
`f t`, the endpoint terms combine into relative fluxes
`f - u * endpointSpeed`. -/
theorem movingEndpoint_hasDerivAt_flux {u ut f fx src : ℝ → ℝ → ℝ}
    {a b a' b' : ℝ → ℝ}
    (t : ℝ) (ha : HasDerivAt a (a' t) t) (hb : HasDerivAt b (b' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2)
    (hfx : ∀ x ∈ Set.uIcc (a t) (b t),
      HasDerivAt (fun y : ℝ => f t y) (fx t x) x)
    (hcont_fx : ContinuousOn (fun x : ℝ => fx t x)
      (Set.uIcc (a t) (b t)))
    (hPDE : ∀ x ∈ Set.uIcc (a t) (b t), ut t x = src t x - fx t x)
    (hint_src : IntervalIntegrable (fun x : ℝ => src t x)
      MeasureTheory.volume (a t) (b t)) :
    HasDerivAt (fun τ : ℝ => ∫ x in a τ..b τ, u τ x)
      ((∫ x in a t..b t, src t x) -
        (f t (b t) - u t (b t) * b' t) +
          (f t (a t) - u t (a t) * a' t)) t := by
  have hmain := movingEndpoint_hasDerivAt t ha hb hjoint hut hcont_ut
  have hFTC : (∫ x in a t..b t, fx t x) = f t (b t) - f t (a t) := by
    have hderiv : ∀ x ∈ Set.uIcc (a t) (b t),
        HasDerivAt (fun y : ℝ => f t y) (fx t x) x := hfx
    have hint : IntervalIntegrable (fun x : ℝ => fx t x) MeasureTheory.volume (a t) (b t) :=
      hcont_fx.intervalIntegrable
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hsplit : (∫ x in a t..b t, ut t x)
      = (∫ x in a t..b t, src t x) - (∫ x in a t..b t, fx t x) := by
    have hfx_int : IntervalIntegrable (fun x : ℝ => fx t x) MeasureTheory.volume (a t) (b t) :=
      hcont_fx.intervalIntegrable
    have h : (∫ x in a t..b t, ut t x)
        = ∫ x in a t..b t, (src t x - fx t x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hPDE x hx
    rw [h]
    exact intervalIntegral.integral_sub hint_src hfx_int
  have hval : (∫ x in a t..b t, ut t x) + u t (b t) * b' t - u t (a t) * a' t
      = (∫ x in a t..b t, src t x) -
        (f t (b t) - u t (b t) * b' t) +
          (f t (a t) - u t (a t) * a' t) := by
    rw [hsplit, hFTC]; ring
  rwa [hval] at hmain

/-- Relative-flux form, `deriv` version (corollary). -/
theorem movingEndpoint_deriv_flux {u ut f fx src : ℝ → ℝ → ℝ}
    {a b a' b' : ℝ → ℝ}
    (t : ℝ) (ha : HasDerivAt a (a' t) t) (hb : HasDerivAt b (b' t) t)
    (hjoint : Continuous fun p : ℝ × ℝ => u p.1 p.2)
    (hut : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => u τ x) (ut t x) t)
    (hcont_ut : Continuous fun p : ℝ × ℝ => ut p.1 p.2)
    (hfx : ∀ x ∈ Set.uIcc (a t) (b t),
      HasDerivAt (fun y : ℝ => f t y) (fx t x) x)
    (hcont_fx : ContinuousOn (fun x : ℝ => fx t x)
      (Set.uIcc (a t) (b t)))
    (hPDE : ∀ x ∈ Set.uIcc (a t) (b t), ut t x = src t x - fx t x)
    (hint_src : IntervalIntegrable (fun x : ℝ => src t x)
      MeasureTheory.volume (a t) (b t)) :
    deriv (fun τ : ℝ => ∫ x in a τ..b τ, u τ x) t =
      (∫ x in a t..b t, src t x) -
        (f t (b t) - u t (b t) * b' t) +
          (f t (a t) - u t (a t) * a' t) := by
  exact (movingEndpoint_hasDerivAt_flux t ha hb hjoint hut hcont_ut hfx hcont_fx hPDE
    hint_src).deriv


/-- Moving interior jump transport: for an interface curve
`s` differentiable at `t` inside the fixed interval `[a, b]`, with left and right
fields `uL`, `uR` (time partials `vL`, `vR`), the split integral
`(∫ x in a..s t, uL t x) + (∫ x in s t..b, uR t x)` has
derivative the two classical integrals plus the interface
contribution `s' t * (uL t (s t) - uR t (s t))`. This is the
two instantiations of `movingEndpoint_hasDerivAt` (moving right
endpoint on the left piece, moving left endpoint on the right
piece) added together. As stated this is an oriented-integral
identity with no ordering hypothesis on `s t`; in the physical
interior-interface case, where `s t` lies inside `[a, b]`, the two
integrals are the genuine left and right pieces of `[a, b]`. -/
theorem movingJumpTransport {uL uR vL vR : ℝ → ℝ → ℝ}
    {s s' : ℝ → ℝ} {a b : ℝ} (t : ℝ) (hs : HasDerivAt s (s' t) t)
    (hjL : Continuous fun p : ℝ × ℝ => uL p.1 p.2)
    (hvL : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => uL τ x) (vL t x) t)
    (hcvL : Continuous fun p : ℝ × ℝ => vL p.1 p.2)
    (hjR : Continuous fun p : ℝ × ℝ => uR p.1 p.2)
    (hvR : ∀ t x : ℝ, HasDerivAt (fun τ : ℝ => uR τ x) (vR t x) t)
    (hcvR : Continuous fun p : ℝ × ℝ => vR p.1 p.2) :
    HasDerivAt
      (fun τ : ℝ => (∫ x in a..s τ, uL τ x) + (∫ x in s τ..b, uR τ x))
      ((∫ x in a..s t, vL t x) + (∫ x in s t..b, vR t x) +
        s' t * (uL t (s t) - uR t (s t))) t := by
  have hL := movingEndpoint_hasDerivAt (u := uL) (ut := vL)
    (a := fun _ : ℝ => a) (b := s) (a' := fun _ : ℝ => 0) (b' := s')
    t (hasDerivAt_const t a) hs hjL hvL hcvL
  have hR := movingEndpoint_hasDerivAt (u := uR) (ut := vR)
    (a := s) (b := fun _ : ℝ => b) (a' := s') (b' := fun _ : ℝ => 0)
    t hs (hasDerivAt_const t b) hjR hvR hcvR
  have hL' : HasDerivAt (fun τ : ℝ => ∫ x in a..s τ, uL τ x)
      ((∫ x in a..s t, vL t x) + s' t * uL t (s t)) t := by
    convert hL using 1
    ring
  have hR' : HasDerivAt (fun τ : ℝ => ∫ x in s τ..b, uR τ x)
      ((∫ x in s t..b, vR t x) - s' t * uR t (s t)) t := by
    convert hR using 1
    ring
  have h := hL'.add hR'
  convert h using 1
  ring


section FixedBox

open Set MeasureTheory
open MathlibExt.Probability.FokkerPlanck (divergence)

/-! ## B. Fixed-box balance with explicit faces -/

/-! ### B.1. Faces and the divergence theorem -/

/-- The outward flux of a vector field `F` through the boundary of the box `[a, b]` in
`ℝⁿ⁺¹ = Fin (n + 1) → ℝ`, face by face: for each coordinate `i`, the integral of `Fᵢ` over the
upper face `x i = b i` (outward normal `+eᵢ`) minus its integral over the lower face
`x i = a i` (outward normal `-eᵢ`), both over the box `[a ∘ i.succAbove, b ∘ i.succAbove]` of the
remaining coordinates. -/
noncomputable def boxOutwardFlux {n : ℕ} (a b : Fin (n + 1) → ℝ)
    (F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1),
    ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (b i) y) i) -
      ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), F (i.insertNth (a i) y) i)

/-- **Divergence theorem on a box**, in the notation of the conditional balance: for a vector
field `F` of class `C¹` on an open set `U` containing the nondegenerate box `[a, b]`,
`∫_[a, b] div F = boxOutwardFlux a b F`. -/
lemma integral_divergence_box {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    {F : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} (hF : ContDiffOn ℝ 1 F U) :
    ∫ x in Icc a b, divergence F x = boxOutwardFlux a b F := by
  have hle : a ≤ b := fun i => (hab i).le
  have hdiff : ∀ x ∈ U, HasFDerivAt F (fderiv ℝ F x) x := fun x hx =>
    (((hF.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hcont : ContinuousOn (fun x => fderiv ℝ F x) U :=
    hF.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiv : ∀ x ∈ U, divergence F x = ∑ i, fderiv ℝ F x (Pi.single i 1) i := by
    intro x hx
    unfold divergence MathlibExt.Probability.FokkerPlanck.pderiv
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [((hasFDerivAt_pi'.1 (hdiff x hx)) i).fderiv]
    simp
  rw [setIntegral_congr_fun measurableSet_Icc (fun x hx => hdiv x (hbox hx))]
  refine integral_divergence_of_hasFDerivAt_off_countable a b hle F (fderiv ℝ F) ∅
    countable_empty (hF.continuousOn.mono hbox) (fun x hx => hdiff x (hbox ?_)) ?_
  · exact ⟨fun i => (hx.1 i (Set.mem_univ i)).1.le, fun i => (hx.1 i (Set.mem_univ i)).2.le⟩
  · refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine continuousOn_finsetSum _ fun i _ => ?_
    exact ((continuous_apply i).comp_continuousOn
      ((hcont.clm_apply continuousOn_const))).mono hbox

/-! ### B.2. The balance -/

/-- **Fixed-box balance with explicit faces.** For a nondegenerate box `[a, b]`, a jointly `C¹`
density `u`, a flux `q t` of class `C¹` on an open neighbourhood of the box, an integrable source
`s t` and the local law `∂ₜu + div q = s` on the box at time `t`,
`d/dt ∫_[a, b] u = ∫_[a, b] s - boxOutwardFlux a b (q t)`. -/
lemma hasDerivAt_boxIntegral {n : ℕ} {a b : Fin (n + 1) → ℝ} (hab : ∀ i, a i < b i)
    {u s : ℝ → (Fin (n + 1) → ℝ) → ℝ} {q : ℝ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ} {t : ℝ}
    {U : Set (Fin (n + 1) → ℝ)} (hU : IsOpen U) (hbox : Icc a b ⊆ U)
    (hu : ContDiff ℝ 1 (Function.uncurry u)) (hq : ContDiffOn ℝ 1 (q t) U)
    (hs : IntegrableOn (s t) (Icc a b))
    (hlaw : ∀ x ∈ Icc a b, deriv (fun τ => u τ x) t + divergence (q t) x = s t x) :
    HasDerivAt (fun τ => ∫ x in Icc a b, u τ x)
      ((∫ x in Icc a b, s t x) - boxOutwardFlux a b (q t)) t := by
  have h := MathlibExt.Analysis.ODE.ContinuumBalances.hasDerivAt_setIntegral_of_divergence
    (Φ := fun _ => boxOutwardFlux a b (q t)) isCompact_Icc hu hs hlaw
    (integral_divergence_box hab hU hbox hq)
  rwa [neg_add_eq_sub] at h

end FixedBox

end ControlVolumes
