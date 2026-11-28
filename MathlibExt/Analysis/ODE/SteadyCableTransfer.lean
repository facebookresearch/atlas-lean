/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Steady transfer along a uniform passive cable

On a finite interval the coupled equations `V' = -ri I`, `I' = -V / rm` have a
hyperbolic transfer formula determined by the inlet data. A zero terminal current
gives the sealed-end solution. Both passive membrane cables and steady heat fins
use this same system.
-/

@[expose] public section

open Real Set

namespace MathlibExt.Biology.Biophysics.MembraneCable

/-- A function whose derivative within `[a, b]` vanishes on `[a, b]` is constant there. -/
lemma eq_of_hasDerivWithinAt_zero {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f 0 (Icc a b) x) : ∀ x ∈ Icc a b, f x = f a :=
  constant_of_has_deriv_right_zero (fun x hx ↦ (hf x hx).continuousWithinAt) fun x hx ↦
    (hf x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)

/-- Length scale `λ = sqrt (rm / ri)` of the transfer system (positive for `rm, ri > 0`). With
`u / 0 = 0` and `sqrt u = 0` for `u < 0`, it is `0` when `ri = 0` or when `rm` and `ri` have
opposite signs. -/
noncomputable def lengthConstant (rm ri : ℝ) : ℝ := sqrt (rm / ri)

/-- Characteristic resistance `r∞ = sqrt (rm ri)` of the transfer system (positive for
`rm, ri > 0`). With `sqrt u = 0` for `u < 0`, it is `0` when `rm ri ≤ 0`. -/
noncomputable def charResistance (rm ri : ℝ) : ℝ := sqrt (rm * ri)

/-- Steady-state core-conductor equations of a passive cable on a set `s` of positions: the
voltage `V` and axial current `I` satisfy `V' = -ri I` and `I' = -V / rm` (derivatives within
`s`). At an isolated point of `s` the conditions always hold; with `u / 0 = 0`, `I' = 0` when
`rm = 0`. -/
structure IsSteadyState (rm ri : ℝ) (s : Set ℝ) (V I : ℝ → ℝ) : Prop where
  /-- Ohm's law along the core: `V' = -ri I`. -/
  hasDerivWithinAt_voltage : ∀ x ∈ s, HasDerivWithinAt V (-(ri * I x)) s x
  /-- Distributed shunt current: `I' = -V / rm`. -/
  hasDerivWithinAt_current : ∀ x ∈ s, HasDerivWithinAt I (-(V x / rm)) s x

/-- Transfer-form steady-state voltage `V(x) = V₀ cosh (x / λ) - r∞ I₀ sinh (x / λ)` with
voltage `V₀` and axial current `I₀` at `x = 0`. With `u / 0 = 0` it is the constant `V₀` when
`λ = 0`. -/
noncomputable def cableVoltage (rm ri V₀ I₀ x : ℝ) : ℝ :=
  V₀ * cosh (x / lengthConstant rm ri) - charResistance rm ri * I₀ * sinh (x / lengthConstant rm ri)

/-- Transfer-form steady-state axial current `I(x) = I₀ cosh (x / λ) - (V₀ / r∞) sinh (x / λ)`
with voltage `V₀` and axial current `I₀` at `x = 0`. With `u / 0 = 0` the second term is `0`
when `r∞ = 0`, and the current is the constant `I₀` when `λ = 0`. -/
noncomputable def cableCurrent (rm ri V₀ I₀ x : ℝ) : ℝ :=
  I₀ * cosh (x / lengthConstant rm ri) - V₀ / charResistance rm ri * sinh (x / lengthConstant rm ri)

section Cable

variable {rm ri : ℝ}

/-- The length constant of a cable with positive resistances is positive. -/
theorem lengthConstant_pos (hm : 0 < rm) (hi : 0 < ri) : 0 < lengthConstant rm ri :=
  sqrt_pos.2 (div_pos hm hi)

/-- The characteristic resistance of a cable with positive resistances is positive. -/
theorem charResistance_pos (hm : 0 < rm) (hi : 0 < ri) : 0 < charResistance rm ri :=
  sqrt_pos.2 (mul_pos hm hi)

/-- `λ² = rm / ri` for `rm, ri > 0`; equivalently `ri λ² = rm`. -/
theorem lengthConstant_sq (hm : 0 < rm) (hi : 0 < ri) : lengthConstant rm ri ^ 2 = rm / ri :=
  sq_sqrt (div_pos hm hi).le

/-- `ri λ² = rm` for `rm, ri > 0`. -/
theorem mul_lengthConstant_sq (hm : 0 < rm) (hi : 0 < ri) : ri * lengthConstant rm ri ^ 2 = rm := by
  rw [lengthConstant_sq hm hi]; field_simp

/-- `r∞ = ri λ` for `rm, ri > 0`; equivalently `r∞ = rm / λ`, since `ri λ² = rm` and
`λ > 0`. -/
theorem charResistance_eq (hm : 0 < rm) (hi : 0 < ri) :
    charResistance rm ri = ri * lengthConstant rm ri := by
  unfold charResistance lengthConstant
  rw [← sqrt_sq hi.le, ← sqrt_mul (sq_nonneg _), sqrt_sq hi.le]
  congr 1; field_simp

/-- The transfer-form voltage and current solve the steady-state core-conductor equations on any
set of positions. -/
theorem isSteadyState_cable (hm : 0 < rm) (hi : 0 < ri) (s : Set ℝ) (V₀ I₀ : ℝ) :
    IsSteadyState rm ri s (cableVoltage rm ri V₀ I₀) (cableCurrent rm ri V₀ I₀) := by
  have hl := lengthConstant_pos hm hi
  have hrm := mul_lengthConstant_sq hm hi
  have hr := charResistance_eq hm hi
  unfold cableVoltage cableCurrent
  rw [hr]
  generalize lengthConstant rm ri = l at hl hrm ⊢
  subst hrm
  have hdiv : ∀ x, HasDerivAt (fun y ↦ y / l) (1 / l) x := fun x ↦ (hasDerivAt_id x).div_const l
  refine ⟨fun x _ ↦ ?_, fun x _ ↦ ?_⟩
  · have h1 : HasDerivAt (fun y ↦ V₀ * cosh (y / l) - ri * l * I₀ * sinh (y / l))
        (V₀ * (sinh (x / l) * (1 / l)) - ri * l * I₀ * (cosh (x / l) * (1 / l))) x :=
      (((hdiv x).cosh).const_mul V₀).sub (((hdiv x).sinh).const_mul _)
    convert h1.hasDerivWithinAt using 1
    field_simp
    ring
  · have h1 : HasDerivAt (fun y ↦ I₀ * cosh (y / l) - V₀ / (ri * l) * sinh (y / l))
        (I₀ * (sinh (x / l) * (1 / l)) - V₀ / (ri * l) * (cosh (x / l) * (1 / l))) x :=
      (((hdiv x).cosh).const_mul I₀).sub (((hdiv x).sinh).const_mul _)
    convert h1.hasDerivWithinAt using 1
    field_simp
    ring

/-- **Uniqueness on a finite cable.** A steady state on `[0, L]` is the transfer-form solution
determined by its voltage `V 0` and axial current `I 0` at `x = 0`. -/
theorem IsSteadyState.eq_cable_Icc {L : ℝ} {V I : ℝ → ℝ} (h : IsSteadyState rm ri (Icc 0 L) V I)
    (hm : 0 < rm) (hi : 0 < ri) {x : ℝ} (hx : x ∈ Icc 0 L) :
    V x = cableVoltage rm ri (V 0) (I 0) x ∧ I x = cableCurrent rm ri (V 0) (I 0) x := by
  have hl := lengthConstant_pos hm hi
  have hrm := mul_lengthConstant_sq hm hi
  have hr := charResistance_eq hm hi
  set l := lengthConstant rm ri with hl_def
  have hdiv : ∀ y, HasDerivAt (fun y ↦ y / l) (1 / l) y := fun y ↦ (hasDerivAt_id y).div_const l
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hx.1.trans hx.2⟩
  -- `(V - ri λ I) e^{-x/λ}` and `(V + ri λ I) e^{x/λ}` are constant.
  have hu : ∀ y ∈ Icc 0 L, HasDerivWithinAt (fun y ↦ (V y - ri * l * I y) * exp (-(y / l))) 0
      (Icc 0 L) y := by
    intro y hy
    have := ((h.hasDerivWithinAt_voltage y hy).sub
      ((h.hasDerivWithinAt_current y hy).const_mul (ri * l))).mul
      ((hdiv y).neg.exp.hasDerivWithinAt)
    convert this using 1
    simp only [Pi.sub_apply]
    rw [← hrm]; field_simp; ring
  have hw : ∀ y ∈ Icc 0 L, HasDerivWithinAt (fun y ↦ (V y + ri * l * I y) * exp (y / l)) 0
      (Icc 0 L) y := by
    intro y hy
    have := ((h.hasDerivWithinAt_voltage y hy).add
      ((h.hasDerivWithinAt_current y hy).const_mul (ri * l))).mul
      ((hdiv y).exp.hasDerivWithinAt)
    convert this using 1
    simp only [Pi.add_apply]
    rw [← hrm]; field_simp; ring
  have hu' := eq_of_hasDerivWithinAt_zero hu x hx
  have hw' := eq_of_hasDerivWithinAt_zero hw x hx
  simp only [zero_div, neg_zero, exp_zero, mul_one] at hu' hw'
  have hE : exp (x / l) * exp (-(x / l)) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hu'' : V x - ri * l * I x = (V 0 - ri * l * I 0) * exp (x / l) := by
    linear_combination exp (x / l) * hu' - (V x - ri * l * I x) * hE
  have hw'' : V x + ri * l * I x = (V 0 + ri * l * I 0) * exp (-(x / l)) := by
    linear_combination exp (-(x / l)) * hw' - (V x + ri * l * I x) * hE
  simp only [cableVoltage, cableCurrent, cosh_eq, sinh_eq, hr, ← hl_def]
  have hril : ri * l ≠ 0 := mul_ne_zero hi.ne' hl.ne'
  constructor
  · linear_combination (hu'' + hw'') / 2
  · field_simp
    linear_combination hw'' - hu''

/-- **Sealed end.** On a finite cable `[0, L]`, `L > 0`, with no axial current through the end
`x = L` (`I L = 0`), the voltage is `V x = V 0 cosh ((L - x) / λ) / cosh (L / λ)`, and the input
voltage and current are related by `V 0 sinh (L / λ) = r∞ I 0 cosh (L / λ)`. -/
theorem IsSteadyState.sealedEnd {L : ℝ} {V I : ℝ → ℝ} (h : IsSteadyState rm ri (Icc 0 L) V I)
    (hm : 0 < rm) (hi : 0 < ri) (hL : 0 < L) (hsealed : I L = 0) :
    V 0 * sinh (L / lengthConstant rm ri) =
        charResistance rm ri * I 0 * cosh (L / lengthConstant rm ri) ∧
      ∀ x ∈ Icc 0 L, V x =
        V 0 * cosh ((L - x) / lengthConstant rm ri) / cosh (L / lengthConstant rm ri) := by
  have hr := (charResistance_pos hm hi).ne'
  have hIL := (h.eq_cable_Icc hm hi ⟨hL.le, le_rfl⟩).2
  rw [hsealed, cableCurrent] at hIL
  have hrel : V 0 * sinh (L / lengthConstant rm ri) =
      charResistance rm ri * I 0 * cosh (L / lengthConstant rm ri) := by
    field_simp at hIL
    linear_combination hIL
  refine ⟨hrel, fun x hx ↦ ?_⟩
  have hVx := (h.eq_cable_Icc hm hi hx).1
  rw [cableVoltage] at hVx
  rw [sub_div, cosh_sub, eq_div_iff (cosh_pos _).ne']
  linear_combination cosh (L / lengthConstant rm ri) * hVx + sinh (x / lengthConstant rm ri) * hrel

end Cable

end MathlibExt.Biology.Biophysics.MembraneCable
