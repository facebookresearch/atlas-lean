/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.SteadyCableTransfer

/-!
# First-order reaction and diffusion in a catalyst slab

The linear boundary-value problem on the half-slab `[0, L]` has a unique profile there. For
`k > 0`, reversing the coordinate gives the steady transfer equations with a sealed end.
For `k = 0`, both the named first derivative and the concentration have zero derivative on the
interval.
-/

open Real Set MathlibExt.Biology.Biophysics.MembraneCable

namespace Chemistry.Transport

private lemma eqOn_cosh_of_pos {D k L cs : ℝ} {c c' : ℝ → ℝ}
    (hD : 0 < D) (hk : 0 < k) (hL : 0 < L)
    (hc : ∀ x ∈ Icc 0 L, HasDerivWithinAt c (c' x) (Icc 0 L) x)
    (hc' : ∀ x ∈ Icc 0 L, HasDerivWithinAt c' (k * c x / D) (Icc 0 L) x)
    (hmid : c' 0 = 0) (hsurf : c L = cs) :
    EqOn c (fun x ↦ cs * cosh (sqrt (k / D) * x) / cosh (L * sqrt (k / D))) (Icc 0 L) := by
  have hreflect : MapsTo (fun x ↦ L - x) (Icc 0 L) (Icc 0 L) := fun _ hx ↦
    ⟨sub_nonneg.mpr hx.2, sub_le_self _ hx.1⟩
  have hderiv (x : ℝ) : HasDerivAt (fun y ↦ L - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub L
  -- The reversed voltage is the concentration, and the current is `D` times its named derivative.
  have hstate : IsSteadyState (1 / k) (1 / D) (Icc 0 L)
      (fun x ↦ c (L - x)) (fun x ↦ D * c' (L - x)) := by
    constructor
    · intro x hx
      have h : HasDerivWithinAt (fun y ↦ c (L - y)) (c' (L - x) * -1) (Icc 0 L) x :=
        (hc (L - x) (hreflect hx)).comp x (hderiv x).hasDerivWithinAt hreflect
      convert h using 1
      field_simp [hD.ne']
    · intro x hx
      have h : HasDerivWithinAt (fun y ↦ D * c' (L - y)) (D * (k * c (L - x) / D * -1))
          (Icc 0 L) x :=
        ((hc' (L - x) (hreflect hx)).comp x (hderiv x).hasDerivWithinAt hreflect).const_mul D
      convert h using 1
      field_simp [hD.ne', hk.ne']
  have hseal : D * c' (L - L) = 0 := by rw [sub_self, hmid, mul_zero]
  have hvoltage := (hstate.sealedEnd (one_div_pos.mpr hk) (one_div_pos.mpr hD) hL hseal).2
  have hlength : lengthConstant (1 / k) (1 / D) = (sqrt (k / D))⁻¹ := by
    unfold lengthConstant
    rw [← sqrt_inv]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  intro x hx
  simpa only [hlength, sub_zero, sub_sub_cancel, div_inv_eq_mul, mul_comm x (sqrt (k / D)), hsurf]
    using hvoltage (L - x) (hreflect hx)

/-- A concentration `c` solves `D c'' = k c`, with `c'(0) = 0` and `c(L) = cs`, exactly when it
agrees on `[0, L]` with the cosh profile for `k > 0` or the constant `cs` for `k = 0`. Here
`Φ = L * sqrt (k / D)` and `c'` names the first derivative. Both derivative conditions use
`HasDerivWithinAt` on the closed interval, including at its endpoints. The reverse implication
supplies a derivative witness for the displayed profile and for any extension that agrees with it
on the interval; no equality of extensions outside `[0, L]` is asserted.

Source for the slab model and boundary conditions: Rawlings and Ekerdt, *Chemical Reactor Analysis
and Design Fundamentals*, §7.4.2, the `q = 0` case of Equation 7.34. The profile is derived here. -/
public theorem firstOrderReactionDiffusion_slab_iff {D k L : ℝ} (hD : 0 < D) (hk : 0 ≤ k)
    (hL : 0 < L) (cs : ℝ) (c : ℝ → ℝ) :
    let Φ := L * sqrt (k / D)
    (∃ c' : ℝ → ℝ,
      (∀ x ∈ Icc 0 L, HasDerivWithinAt c (c' x) (Icc 0 L) x) ∧
      (∀ x ∈ Icc 0 L, HasDerivWithinAt c' (k * c x / D) (Icc 0 L) x) ∧
      c' 0 = 0 ∧ c L = cs) ↔
    EqOn c (fun x ↦ if k = 0 then cs else cs * cosh (Φ * x / L) / cosh Φ) (Icc 0 L) := by
  have hLmem : L ∈ Icc 0 L := ⟨hL.le, le_rfl⟩
  by_cases hzero : k = 0
  · subst k
    simp only [zero_mul, zero_div]
    constructor
    · rintro ⟨c', hc, hc', hmid, hsurf⟩
      have hc₀ (x : ℝ) (hx : x ∈ Icc 0 L) : HasDerivWithinAt c 0 (Icc 0 L) x := by
        simpa only [eq_of_hasDerivWithinAt_zero hc' x hx, hmid] using hc x hx
      intro x hx
      exact (eq_of_hasDerivWithinAt_zero hc₀ x hx).trans
        ((eq_of_hasDerivWithinAt_zero hc₀ L hLmem).symm.trans hsurf)
    · intro hc
      refine ⟨fun _ ↦ 0, ?_, fun x _ ↦ (hasDerivAt_const x (0 : ℝ)).hasDerivWithinAt, rfl,
        hc hLmem⟩
      intro x hx
      exact (hasDerivAt_const x cs).hasDerivWithinAt.congr hc (hc hx)
  · simp only [ite_eq_right hzero]
    have harg (x : ℝ) : L * sqrt (k / D) * x / L = sqrt (k / D) * x := by
      rw [mul_assoc, mul_comm L, mul_div_cancel_right₀ _ hL.ne']
    simp only [harg]
    constructor
    · rintro ⟨c', hc, hc', hmid, hsurf⟩
      exact eqOn_cosh_of_pos hD (lt_of_le_of_ne hk (Ne.symm hzero)) hL hc hc' hmid hsurf
    · intro hc
      let a := sqrt (k / D)
      let b := cs / cosh (L * a)
      have hsq : a ^ 2 = k / D := sq_sqrt (div_nonneg hk hD.le)
      have hprofile : EqOn c (fun x ↦ b * cosh (a * x)) (Icc 0 L) := by
        intro x hx
        simpa only [b, div_mul_eq_mul_div] using hc hx
      have hlinear (x : ℝ) : HasDerivAt (fun y ↦ a * y) a x := by
        simpa using (hasDerivAt_id x).const_mul a
      refine ⟨fun x ↦ b * (sinh (a * x) * a), ?_, ?_, by simp, ?_⟩
      · intro x hx
        exact ((hlinear x).cosh.const_mul b).hasDerivWithinAt.congr hprofile (hprofile hx)
      · intro x hx
        rw [hprofile hx]
        convert (((hlinear x).sinh.mul_const a).const_mul b).hasDerivWithinAt using 1
        rw [show k * (b * cosh (a * x)) / D = (k / D) * (b * cosh (a * x)) by ring, ← hsq]
        ring
      · rw [hprofile hLmem]
        change (cs / cosh (L * a)) * cosh (a * L) = cs
        rw [mul_comm a L, div_mul_cancel₀ _ (cosh_pos _).ne']

end Chemistry.Transport
