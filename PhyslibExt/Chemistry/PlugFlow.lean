/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Plug flow in residence time

For constant positive volumetric flow, the steady plug-flow profile is the batch trajectory
written in reactor-volume coordinates.

## i. Overview

For flow `Q > 0` and reactor volume `V_R ≥ 0`, the change of variables is `V = Q * τ`.
The production law `R` takes the concentration state to its vector of production rates.
The plug-flow derivative is `Q⁻¹ • R (c V)`, equivalent to `Q • c' = R (c V)` since `Q > 0`.
The batch derivative is `R (C τ)`. Both derivatives are taken within their closed intervals;
uniqueness concerns agreement on those intervals, not arbitrary values outside them.

## ii. Key results

- `Chemistry.PlugFlow.batch_in_residence_time`: the plug-flow and batch balances are
  equivalent, the outlet is the batch endpoint, and batch uniqueness implies plug-flow
  uniqueness. For zero volume the balance reduces to the feed condition at the outlet.

## iii. Table of contents

- A. Residence-time correspondence

## iv. References

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*,
  2nd ed., 7th printing, §4.6, Eqs. 4.66 and 4.74 and the text following Eq. 4.74.
-/

@[expose] public section

namespace Chemistry.PlugFlow

open Set Function

/-! ## A. Residence-time correspondence -/

/-- With positive constant flow `Q` and nonnegative volume `V_R`, the volume-coordinate
balance for `c` is equivalent to the batch balance for `C τ = c (Q * τ)`. The outlet is the
batch endpoint `V_R / Q`, and agreement of batch solutions on their interval gives agreement
of plug-flow solutions on theirs. In the zero-volume case a within-singleton derivative
imposes no condition, so the plug-flow balance reduces to `c 0 = feed`. -/
lemma batch_in_residence_time {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q V_R : ℝ} (hQ : 0 < Q) (hV : 0 ≤ V_R) (R : E → E) (feed : E) :
    let plugFlow (c : ℝ → E) := c 0 = feed ∧ ∀ v ∈ Icc 0 V_R,
      HasDerivWithinAt c (Q⁻¹ • R (c v)) (Icc 0 V_R) v
    let batch (C : ℝ → E) := C 0 = feed ∧ ∀ τ ∈ Icc 0 (V_R / Q),
      HasDerivWithinAt C (R (C τ)) (Icc 0 (V_R / Q)) τ
    (∀ c, plugFlow c ↔ batch (fun τ ↦ c (Q * τ))) ∧
    (V_R / Q ∈ Icc 0 (V_R / Q) ∧ ∀ c : ℝ → E, c (Q * (V_R / Q)) = c V_R) ∧
    ((∀ C₁ C₂, batch C₁ → batch C₂ → EqOn C₁ C₂ (Icc 0 (V_R / Q))) →
      ∀ c₁ c₂, plugFlow c₁ → plugFlow c₂ → EqOn c₁ c₂ (Icc 0 V_R)) ∧
    (V_R = 0 → ∀ c, plugFlow c ↔ c 0 = feed) := by
  intro plugFlow batch
  have hscale (v : ℝ) : Q * (v / Q) = v := by
    rw [mul_comm, div_mul_cancel₀ _ hQ.ne']
  have hforward : MapsTo (fun τ : ℝ ↦ Q * τ) (Icc 0 (V_R / Q)) (Icc 0 V_R) := by
    intro τ hτ
    exact ⟨mul_nonneg hQ.le hτ.1,
      (mul_le_mul_of_nonneg_left hτ.2 hQ.le).trans_eq (hscale V_R)⟩
  have hback : MapsTo (fun v : ℝ ↦ v / Q) (Icc 0 V_R) (Icc 0 (V_R / Q)) := by
    intro v hv
    exact ⟨div_nonneg hv.1 hQ.le, div_le_div_of_nonneg_right hv.2 hQ.le⟩
  have hequiv (c : ℝ → E) : plugFlow c ↔ batch (fun τ ↦ c (Q * τ)) := by
    constructor
    · rintro ⟨h0, hd⟩
      refine ⟨by simpa only [mul_zero] using h0, fun τ hτ ↦ ?_⟩
      have h := (hd _ (hforward hτ)).scomp τ
        ((hasDerivAt_id τ).const_mul Q).hasDerivWithinAt hforward
      simpa only [comp_def, id_eq, mul_one, smul_smul, mul_inv_cancel₀ hQ.ne', one_smul] using h
    · rintro ⟨h0, hd⟩
      refine ⟨by simpa only [mul_zero] using h0, fun v hv ↦ ?_⟩
      have h := (hd _ (hback hv)).scomp v
        ((hasDerivAt_id v).div_const Q).hasDerivWithinAt hback
      simpa only [comp_def, id_eq, hscale, one_div] using h
  refine ⟨hequiv, ⟨⟨div_nonneg hV hQ.le, le_rfl⟩, fun c ↦ congrArg c (hscale V_R)⟩, ?_, ?_⟩
  · intro hu c₁ c₂ h₁ h₂ v hv
    have h := hu (fun τ ↦ c₁ (Q * τ)) (fun τ ↦ c₂ (Q * τ))
      ((hequiv c₁).mp h₁) ((hequiv c₂).mp h₂) (hback hv)
    simpa only [hscale] using h
  · intro hV₀ c
    constructor
    · exact And.left
    · intro hc
      refine ⟨hc, fun v hv ↦ ?_⟩
      have hv₀ : v = 0 := le_antisymm (hV₀ ▸ hv.2) hv.1
      subst v
      rw [hV₀, Icc_self, hasDerivWithinAt_iff_hasFDerivWithinAt]
      exact HasFDerivWithinAt.singleton

end Chemistry.PlugFlow

end
