/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.LocalGroupLaw

import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod

@[expose] public section

open Topology

/-! The source statements, with their original binders. The source of the second statement also
assumes `0 < ρ`, `MapsTo` hypotheses for `e` and `h`, and differentiability of `h` on `B(0, s)`;
the Mathlib-style statement drops them, so they are unused here. -/

example {g : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (F : (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ))
    (hF : DifferentiableOn ℂ (fun p : (Fin g → ℂ) × (Fin g → ℂ) => F p.1 p.2)
      (Metric.ball (0 : Fin g → ℂ) ρ ×ˢ Metric.ball (0 : Fin g → ℂ) ρ))
    (hzero_left : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) ρ, F 0 v = v)
    (hzero_right : ∀ v ∈ Metric.ball (0 : Fin g → ℂ) ρ, F v 0 = v)
    (hcomm : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      w ∈ Metric.ball (0 : Fin g → ℂ) ρ → F v w = F w v)
    (hassoc : ∀ u v w : Fin g → ℂ, u ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      v ∈ Metric.ball (0 : Fin g → ℂ) ρ → w ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      F u v ∈ Metric.ball (0 : Fin g → ℂ) ρ → F v w ∈ Metric.ball (0 : Fin g → ℂ) ρ →
      F (F u v) w = F u (F v w)) :
    ∃ (r : ℝ) (_ : 0 < r) (e : (Fin g → ℂ) → (Fin g → ℂ)),
      e 0 = 0 ∧
      DifferentiableOn ℂ e (Metric.ball (0 : Fin g → ℂ) r) ∧
      HasFDerivAt e (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 ∧
      Set.InjOn e (Metric.ball (0 : Fin g → ℂ) r) ∧
      Set.MapsTo e (Metric.ball (0 : Fin g → ℂ) r) (Metric.ball (0 : Fin g → ℂ) ρ) ∧
      (∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r →
        w ∈ Metric.ball (0 : Fin g → ℂ) r → v + w ∈ Metric.ball (0 : Fin g → ℂ) r →
        e (v + w) = F (e v) (e w)) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.ball (0 : Fin g → ℂ) δ,
        ∃ v ∈ Metric.ball (0 : Fin g → ℂ) r, e v = x) :=
  LocalGroupLaw.exists_localExp_of_differentiableOn_of_comm_of_assoc hρ F hF hzero_left
    hzero_right hcomm hassoc

example {g : ℕ} {r ρ : ℝ} (hr : 0 < r) (_hρ : 0 < ρ)
    (F : (Fin g → ℂ) → (Fin g → ℂ) → (Fin g → ℂ))
    (e : (Fin g → ℂ) → (Fin g → ℂ)) (he0 : e 0 = 0)
    (he : DifferentiableOn ℂ e (Metric.ball (0 : Fin g → ℂ) r))
    (hde : HasFDerivAt e (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0)
    (hinj : Set.InjOn e (Metric.ball (0 : Fin g → ℂ) r))
    (_hmaps : Set.MapsTo e (Metric.ball (0 : Fin g → ℂ) r) (Metric.ball (0 : Fin g → ℂ) ρ))
    (hhom : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r →
      w ∈ Metric.ball (0 : Fin g → ℂ) r → v + w ∈ Metric.ball (0 : Fin g → ℂ) r →
      e (v + w) = F (e v) (e w))
    {s : ℝ} (hs : 0 < s) (h : (Fin g → ℂ) → (Fin g → ℂ)) (hh0 : h 0 = 0)
    (_hh : DifferentiableOn ℂ h (Metric.ball (0 : Fin g → ℂ) s))
    (_hhmaps : Set.MapsTo h (Metric.ball (0 : Fin g → ℂ) s) (Metric.ball (0 : Fin g → ℂ) ρ))
    (hhhom : ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) s →
      w ∈ Metric.ball (0 : Fin g → ℂ) s → v + w ∈ Metric.ball (0 : Fin g → ℂ) s →
      h (v + w) = F (h v) (h w))
    (A : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) (hA : HasFDerivAt h A 0) :
    ∃ s' : ℝ, 0 < s' ∧ s' ≤ s ∧
      ∀ v ∈ Metric.ball (0 : Fin g → ℂ) s',
        A v ∈ Metric.ball (0 : Fin g → ℂ) r ∧ h v = e (A v) :=
  LocalGroupLaw.exists_ball_eq_localExp_comp_fderiv_of_map_add hr F e he0 he hde hinj hhom hs
    h hh0 hhhom A hA

/-! Addition on `ℂ^g` is a holomorphic commutative group law, so it has a local exponential. -/

example (g : ℕ) : ∃ (r : ℝ) (_ : 0 < r) (e : (Fin g → ℂ) → (Fin g → ℂ)),
    e 0 = 0 ∧ HasFDerivAt e (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 ∧
      ∀ v w : Fin g → ℂ, v ∈ Metric.ball (0 : Fin g → ℂ) r →
        w ∈ Metric.ball (0 : Fin g → ℂ) r → v + w ∈ Metric.ball (0 : Fin g → ℂ) r →
        e (v + w) = e v + e w := by
  obtain ⟨r, hr, e, he0, -, hde, -, -, hhom, -⟩ :=
    LocalGroupLaw.exists_localExp_of_differentiableOn_of_comm_of_assoc one_pos
      (fun v w : Fin g → ℂ => v + w) (differentiable_fst.add differentiable_snd).differentiableOn
      (fun v _ => zero_add v) (fun v _ => add_zero v) (fun v w _ _ => add_comm v w)
      (fun u v w _ _ _ _ _ => add_assoc u v w)
  exact ⟨r, hr, e, he0, hde, hhom⟩
