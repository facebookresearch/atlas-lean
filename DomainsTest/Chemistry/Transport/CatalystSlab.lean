/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.Transport.CatalystSlab

/-! # Tests for the first-order half-slab boundary-value problem -/

open Real Set Chemistry.Transport

/-- The positive-rate formula at the mid-plane, using only within-interval derivatives. -/
example {D k L cs : ℝ} (hD : 0 < D) (hk : 0 < k) (hL : 0 < L) {c c' : ℝ → ℝ}
    (hc : ∀ x ∈ Icc 0 L, HasDerivWithinAt c (c' x) (Icc 0 L) x)
    (hc' : ∀ x ∈ Icc 0 L, HasDerivWithinAt c' (k * c x / D) (Icc 0 L) x)
    (hmid : c' 0 = 0) (hsurf : c L = cs) : c 0 = cs / cosh (L * sqrt (k / D)) := by
  have h := (firstOrderReactionDiffusion_slab_iff hD hk.le hL cs c).mp ⟨c', hc, hc', hmid, hsurf⟩
  have h0 : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL.le⟩
  simpa [hk.ne'] using h h0

/-- At positive rate the explicit profile still solves the problem with an arbitrary extension. -/
example {D k L cs : ℝ} (hD : 0 < D) (hk : 0 < k) (hL : 0 < L) (outside : ℝ → ℝ) :
    let Φ := L * sqrt (k / D)
    let c : ℝ → ℝ := fun x ↦
      if x ∈ Icc 0 L then cs * cosh (Φ * x / L) / cosh Φ else outside x
    ∃ c' : ℝ → ℝ,
      (∀ x ∈ Icc 0 L, HasDerivWithinAt c (c' x) (Icc 0 L) x) ∧
      (∀ x ∈ Icc 0 L, HasDerivWithinAt c' (k * c x / D) (Icc 0 L) x) ∧
      c' 0 = 0 ∧ c L = cs := by
  classical
  dsimp only
  apply (firstOrderReactionDiffusion_slab_iff hD hk.le hL cs _).mpr
  intro x hx
  simp [hx, hk.ne']

/-- At zero rate the boundary conditions pin the constant value throughout the closed interval. -/
example {D L cs : ℝ} (hD : 0 < D) (hL : 0 < L) {c c' : ℝ → ℝ}
    (hc : ∀ x ∈ Icc 0 L, HasDerivWithinAt c (c' x) (Icc 0 L) x)
    (hc' : ∀ x ∈ Icc 0 L, HasDerivWithinAt c' 0 (Icc 0 L) x)
    (hmid : c' 0 = 0) (hsurf : c L = cs) : EqOn c (fun _ ↦ cs) (Icc 0 L) := by
  have h := (firstOrderReactionDiffusion_slab_iff hD (k := 0) le_rfl hL cs c).mp
    ⟨c', hc, by simpa only [zero_mul, zero_div] using hc', hmid, hsurf⟩
  simpa using h

/-- The constant profile genuinely solves the zero-rate problem. -/
example {D L cs : ℝ} (hD : 0 < D) (hL : 0 < L) :
    ∃ c' : ℝ → ℝ,
      (∀ x ∈ Icc 0 L, HasDerivWithinAt (fun _ ↦ cs) (c' x) (Icc 0 L) x) ∧
      (∀ x ∈ Icc 0 L, HasDerivWithinAt c' 0 (Icc 0 L) x) ∧ c' 0 = 0 := by
  obtain ⟨c', hc, hc', hmid, _⟩ :=
    (firstOrderReactionDiffusion_slab_iff hD (k := 0) le_rfl hL cs (fun _ ↦ cs)).mpr (by
      intro x _
      simp)
  exact ⟨c', hc, by simpa only [zero_mul, zero_div] using hc', hmid⟩
