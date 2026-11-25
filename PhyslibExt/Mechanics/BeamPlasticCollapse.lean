/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.LinearAlgebra.Matrix.PlasticWork
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Fixed-ended beam under uniform load: plastic hinge certificates

## i. Overview

Source lock: B. G. Neal, *The Plastic Methods of Structural Analysis*, 3rd (S.I.) edition,
Chapman and Hall, 1977, section 2.3 "Fixed-ended beam", pp. 22-27 (Fig. 2.4 on p. 22): the sign
convention, the equilibrium equation (2.2) and the elastic solution on p. 23, Fig. 2.5(d)-(e) on
p. 25, the collapse load `W_c = 16 M_p / l` on p. 26 (first obtained by Kazinczy, 1914), and
section 2.3.1, the statical and kinematical calculations of the collapse load on p. 27.
Section 2.5.1 (p. 33), equation (2.11), states the principle of virtual work behind the
mechanism calculation, and section 2.5.2 (p. 34), equation (2.12), its virtual-displacement
form. Neal's total load `W` and span `l` are `w * L` and `L` here.

- Beam: uniform cross section, span `L` (physical domain `0 < L`), both ends clamped against
  rotation; small axial end movements are permitted, so no membrane force develops. The load is
  uniformly distributed with intensity `w` per unit length, positive in the load direction.
  Plastic moment `Mp` at every section, equal in sagging and hogging (physical domain
  `0 < Mp`). For a rectangular section of width `b`, height `h` and yield stress `σy`, `Mp` is
  the fully plastic moment `σy * b * h ^ 2 / 4` of
  `Mechanics.PlasticSection.sectionMoment_fullyPlasticStress`; here `Mp` is a parameter.
- Signs: Neal's consistent convention, which is also the Atlas beam convention. Bending moments
  and hinge rotations are sagging positive (tension in the fibres on the side away from the
  load); deflections are positive in the load direction.
- Finite model: three critical sections, `0` (left end, `x = 0`), `1` (mid-span, `x = L / 2`)
  and `2` (right end, `x = L`), with moments `σ : Fin 3 → ℝ`, and one generalized coordinate,
  the central deflection (`Fin 1`). The compatibility matrix `hingeRotation L` lists the hinge
  rotations `-2 / L`, `4 / L`, `-2 / L` per unit central deflection (Fig. 2.5(e): `-θ`, `2θ`,
  `-θ` at central deflection `L * θ / 2`). The work vector `uniformLoadWork L = ![L / 2]` is
  the work of a unit load intensity per unit central deflection: the load moves on average
  half the central deflection (p. 27). The load factor is the intensity `w`.
- Canonical certificate: with `B = hingeRotation L`, `f = uniformLoadWork L`, capacities
  `y e = Mp` and load factor `w`, the data of the finite plastic work certificate
  (`PlasticWork`) read: equilibrium `Bᵀ *ᵥ σ = w • f`, capacity `|σ e| ≤ Mp`, normalization
  `f ⬝ᵥ v = 1` of a mechanism `v`, plastic dissipation `∑ e, Mp * |(B *ᵥ v) e|`, and
  complementarity `Mp * |(B *ᵥ v) e| = σ e * (B *ᵥ v) e`. This module is the first production
  consumer of `PlasticWork.loadFactor_le`.
- Mechanism deflection: `mechanismDeflection L δ x = 2 * δ / L * min x (L - x)`, two rigid
  segments hinged at the supports and at mid-span, with central deflection `δ`; physical domain
  `0 ≤ x ≤ L`.
- Totalized division (`x / 0 = 0`): at `L = 0` the matrix `hingeRotation 0`, the normalized
  mechanism `![2 / 0]`, the slope `2 * δ / 0` and `16 * Mp / 0 ^ 2` all vanish. Statements
  that need a nondegenerate span assume `0 < L`; the others hold for every real `L`.
- Units: `L`, `x` and `δ` are lengths, `w` is a force per length, `Mp` and `σ` are forces
  times lengths, and hinge rotations are dimensionless. The normalization `f ⬝ᵥ v = 1`
  measures `v` per unit area: `v = 2 / L` is in 1/length and the normalized rotations are in
  1/length², so the normalized dissipation `16 * Mp / L ^ 2` is a load intensity, the load
  intensity it certifies.

Scope: the statements concern the finite three-section model: the static and kinematic
certificates at `w = 16 * Mp / L ^ 2` and their complementarity, the identification of this
value as the greatest load intensity that admits a statically admissible moment field, the
work balance of the unit-deflection mechanism, the rejection of the elastic moment field, and
the bridges from beam statics (equation (2.2)), mechanism kinematics and the external-work
integral to the canonical data, with the admissibility of the collapse bending-moment diagram
between the hinges. This is not a collapse theorem for the continuous beam. Excluded: design
capacity or resistance factors, P-delta and other large-displacement effects, axial force and
shear interaction with the plastic moment, unequal sagging and hogging plastic moments, and any
strong-duality inference not backed by these explicit certificates.

## ii. Key results

- `Mechanics.BeamPlasticCollapse.collapseMoments_staticCertificate`: the moments
  `(-Mp, Mp, -Mp)` equilibrate the collapse intensity `16 * Mp / L ^ 2` within capacity.
- `Mechanics.BeamPlasticCollapse.collapseMechanism_kinematicCertificate`: the normalized
  three-hinge mechanism dissipates `16 * Mp / L ^ 2`.
- `Mechanics.BeamPlasticCollapse.collapseCertificates_complementary`: the two certificates are
  complementary at every hinge.
- `Mechanics.BeamPlasticCollapse.collapseLoad_isGreatest`: `16 * Mp / L ^ 2` is the greatest
  statically admissible load intensity of the finite model.
- `Mechanics.BeamPlasticCollapse.unitMechanism_work`: work balance of the unit mechanism.
- `Mechanics.BeamPlasticCollapse.elasticMoments_not_admissible`: the elastic moment field
  exceeds the plastic moment.
- `Mechanics.BeamPlasticCollapse.hingeRotation_transpose_mulVec_eq_iff`: the statics reading
  of the hinge-rotation matrix (Neal's equation (2.2)).
- `Mechanics.BeamPlasticCollapse.collapseMomentDiagram_abs_le`: the collapse moment diagram
  stays within `Mp` between the hinges.
- `Mechanics.BeamPlasticCollapse.hingeRotation_mulVec_eq_slopeJumps`: the compatibility
  reading, hinge rotations as slope jumps of the mechanism deflection.
- `Mechanics.BeamPlasticCollapse.integral_mechanismDeflection`: the mechanism deflection
  integrates to the external-work normalization.

## iii. Table of contents

- A. Finite model data
- B. Collapse certificates
- C. Statics, kinematics and work bridges

## iv. References

- B. G. Neal, *The Plastic Methods of Structural Analysis*, 3rd (S.I.) edition, Chapman and
  Hall, 1977: section 2.3, pp. 22-27, equation (2.2), Figs. 2.4-2.5; section 2.3.1, p. 27;
  section 2.5.1, equation (2.11), p. 33; section 2.5.2, equation (2.12), p. 34.
- G. Kazinczy (1914), as attributed by Neal for the collapse load of the fixed-ended beam.

-/

@[expose] public section

namespace Mechanics.BeamPlasticCollapse

open Matrix

/-! ## A. Finite model data -/

/-- Compatibility matrix of the three-hinge mechanism of a fixed-ended beam of span `L`: the sagging
hinge rotations at the left end, mid-span and right end per unit central deflection, `-2 / L`,
`4 / L` and `-2 / L` (rows: critical sections; column: central deflection). With the convention
`x / 0 = 0` it is the zero matrix at `L = 0`. -/
noncomputable def hingeRotation (L : ℝ) : Matrix (Fin 3) (Fin 1) ℝ :=
  !![-2 / L; 4 / L; -2 / L]

/-- Work vector of the uniform load: the work `L / 2` done by a unit load intensity per unit
central deflection of the three-hinge mechanism, whose average displacement over the span is
half the central deflection. -/
noncomputable def uniformLoadWork (L : ℝ) : Fin 1 → ℝ :=
  ![L / 2]

/-- Deflection at `x` of the three-hinge mechanism of a fixed-ended beam of span `L` with central
deflection `δ` (positive in the load direction): two rigid segments, linear from the supports to
mid-span, `2 * δ / L * min x (L - x)` on `0 ≤ x ≤ L`. With the convention `x / 0 = 0` it is
identically `0` when `L = 0`. -/
noncomputable def mechanismDeflection (L δ x : ℝ) : ℝ :=
  2 * δ / L * min x (L - x)

/-! ## B. Collapse certificates -/

/-- Static certificate at Kazinczy's collapse load (Neal, Fig. 2.5(d)): the moments `-Mp` at the
ends and `Mp` at mid-span are in equilibrium with the uniform load of intensity `16 * Mp / L ^ 2`
and do not exceed the plastic moment. Equilibrium holds for every real `L`: at `L = 0` the
convention `x / 0 = 0` makes the matrix, the load intensity and both sides `0`; the physical reading
is `0 < L`. -/
theorem collapseMoments_staticCertificate (L : ℝ) {Mp : ℝ} (hMp : 0 ≤ Mp) :
    (hingeRotation L)ᵀ *ᵥ ![-Mp, Mp, -Mp] = (16 * Mp / L ^ 2) • uniformLoadWork L ∧
      ∀ e : Fin 3, |![-Mp, Mp, -Mp] e| ≤ Mp := by
  constructor
  · ext i
    fin_cases i
    simp [hingeRotation, uniformLoadWork, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    by_cases hL : L = 0
    · simp [hL]
    · field_simp
      ring
  · intro e
    fin_cases e <;> simp [abs_neg, abs_of_nonneg hMp]

/-- Kinematic certificate (Neal, Fig. 2.5(e)): the three-hinge mechanism with central
deflection `2 / L` is normalized, `f ⬝ᵥ v = 1`, and its plastic dissipation over the hinge
rotations `-4 / L ^ 2`, `8 / L ^ 2`, `-4 / L ^ 2` is `16 * Mp / L ^ 2`. -/
theorem collapseMechanism_kinematicCertificate {L : ℝ} (Mp : ℝ) (hL : 0 < L) :
    uniformLoadWork L ⬝ᵥ ![2 / L] = 1 ∧
      ∑ e, Mp * |(hingeRotation L *ᵥ ![2 / L]) e| = 16 * Mp / L ^ 2 := by
  have hLne : L ≠ 0 := ne_of_gt hL
  constructor
  · simp [uniformLoadWork, dotProduct]
    field_simp
  · simp [hingeRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have h2 : (0:ℝ) < 2 / L := by positivity
    have h4 : (0:ℝ) < 4 / L := by positivity
    have hn2 : (-2 / L : ℝ) < 0 := by
      have : (0:ℝ) < 2 / L := by positivity
      linarith [show (-2 / L : ℝ) = -(2 / L) by ring]
    rw [abs_of_neg hn2, abs_of_pos h4, abs_of_pos h2]
    field_simp
    ring

/-- The static and kinematic certificates match: at each critical section, for the moments
`σ = ![-Mp, Mp, -Mp]` and the hinge rotations `θ` of the normalized mechanism,
`Mp * |θ e| = σ e * θ e` (no slack). This is the complementarity hypothesis of
`PlasticWork.loadFactor_eq_of_complementary`; it holds for all real `L` and `Mp` (at `L = 0` the
rotations are `0` by the convention `x / 0 = 0` and both sides vanish). For `L ≠ 0`,
`σ e = Mp * sign (θ e)`, so for `Mp > 0` each moment has the sign of its hinge rotation. -/
lemma collapseCertificates_complementary (L Mp : ℝ) (e : Fin 3) :
    Mp * |(hingeRotation L *ᵥ ![2 / L]) e| =
      ![-Mp, Mp, -Mp] e * (hingeRotation L *ᵥ ![2 / L]) e := by
  fin_cases e
  · simp [hingeRotation, Matrix.mulVec, dotProduct]
    rw [← abs_mul]
    have h : ((-2 / L) * (2 / L) : ℝ) ≤ 0 := by
      have hsq : (0:ℝ) ≤ (2 / L) ^ 2 := sq_nonneg _
      have heq : ((-2 / L) * (2 / L) : ℝ) = -((2 / L) ^ 2) := by ring
      linarith
    rw [abs_of_nonpos h]
    ring
  · simp [hingeRotation, Matrix.mulVec, dotProduct]
    refine Or.inl ?_
    rw [← abs_mul]
    have h : (0:ℝ) ≤ (4 / L) * (2 / L) := by
      have hsq : (0:ℝ) ≤ (2 / L) ^ 2 := sq_nonneg _
      have heq : ((4 / L) * (2 / L) : ℝ) = 2 * ((2 / L) ^ 2) := by ring
      linarith
    rw [abs_of_nonneg h]
  · simp [hingeRotation, Matrix.mulVec, dotProduct]
    rw [← abs_mul]
    have h : ((-2 / L) * (2 / L) : ℝ) ≤ 0 := by
      have hsq : (0:ℝ) ≤ (2 / L) ^ 2 := sq_nonneg _
      have heq : ((-2 / L) * (2 / L) : ℝ) = -((2 / L) ^ 2) := by ring
      linarith
    rw [abs_of_nonpos h]
    ring

/-- Collapse load of the finite model: `16 * Mp / L ^ 2` is the greatest load intensity `w` for
which a statically admissible moment field exists (equilibrium `Bᵀ *ᵥ σ = w • f` and
`|σ e| ≤ Mp` at the three critical sections). The upper bound is the canonical weak-duality
bound `PlasticWork.loadFactor_le` at this carrier, applied to the normalized mechanism. This is a statement about the three-section
model, not a collapse theorem for the continuous beam. -/
theorem collapseLoad_isGreatest
    {L Mp : ℝ} (hL : 0 < L) (hMp : 0 ≤ Mp) :
    IsGreatest {w : ℝ | ∃ σ : Fin 3 → ℝ,
        (hingeRotation L)ᵀ *ᵥ σ = w • uniformLoadWork L ∧ ∀ e, |σ e| ≤ Mp}
      (16 * Mp / L ^ 2) := by
  constructor
  · exact ⟨![-Mp, Mp, -Mp], collapseMoments_staticCertificate L hMp⟩
  · intro w hw
    obtain ⟨σ, heq, hcap⟩ := hw
    have hkin := collapseMechanism_kinematicCertificate Mp hL
    have hub := PlasticWork.loadFactor_le (hingeRotation L) σ (fun _ => Mp) (uniformLoadWork L) ![2 / L] w
      heq hcap hkin.1
    have hub2 : w ≤ ∑ e, Mp * |(hingeRotation L *ᵥ ![2 / L]) e| := hub
    rw [hkin.2] at hub2
    exact hub2

/-- Work balance of the unit mechanism (Neal, p. 27): at unit central deflection the hinge
rotations `-2 / L`, `4 / L`, `-2 / L` absorb the plastic work `8 * Mp / L`, the uniform load
of intensity `w` does the work `w * L / 2`, and the two balance exactly when
`w = 16 * Mp / L ^ 2`. -/
theorem unitMechanism_work {L : ℝ} (Mp w : ℝ) (hL : 0 < L) :
    ∑ e, Mp * |(hingeRotation L *ᵥ ![1]) e| = 8 * Mp / L ∧
      (w • uniformLoadWork L) ⬝ᵥ ![1] = w * L / 2 ∧
      (∑ e, Mp * |(hingeRotation L *ᵥ ![1]) e| = (w • uniformLoadWork L) ⬝ᵥ ![1] ↔
        w = 16 * Mp / L ^ 2) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hA : ∑ e, Mp * |(hingeRotation L *ᵥ ![1]) e| = 8 * Mp / L := by
    simp [hingeRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    have h4 : (0:ℝ) < 4 / L := by positivity
    have hn2 : (-2 / L : ℝ) < 0 := by
      have : (0:ℝ) < 2 / L := by positivity
      linarith [show (-2 / L : ℝ) = -(2 / L) by ring]
    rw [abs_of_neg hn2, abs_of_pos h4]
    field_simp
    ring
  have hB : (w • uniformLoadWork L) ⬝ᵥ ![1] = w * L / 2 := by
    simp [uniformLoadWork, dotProduct]
    ring
  refine ⟨hA, hB, ?_⟩
  rw [hA, hB]
  constructor
  · intro h
    field_simp at h ⊢
    nlinarith [h]
  · intro h
    rw [h]
    field_simp
    ring

/-- An inadmissible moment field is rejected: the elastic moments at the collapse load (Neal, p. 23:
`-W l / 12` at the ends and `W l / 24` at mid-span, with `W l = 16 * Mp`) are in equilibrium with
the load intensity `16 * Mp / L ^ 2` but exceed the plastic moment at the ends, so they are not a
static certificate. Equilibrium holds for every real `L` (at `L = 0` both sides are `0` by the
convention `x / 0 = 0`). -/
lemma elasticMoments_not_admissible (L : ℝ) {Mp : ℝ} (hMp : 0 < Mp) :
    (hingeRotation L)ᵀ *ᵥ ![-(4 * Mp / 3), 2 * Mp / 3, -(4 * Mp / 3)] =
        (16 * Mp / L ^ 2) • uniformLoadWork L ∧
      ¬ ∀ e : Fin 3, |![-(4 * Mp / 3), 2 * Mp / 3, -(4 * Mp / 3)] e| ≤ Mp := by
  constructor
  · ext i
    fin_cases i
    simp [hingeRotation, uniformLoadWork, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    by_cases hL : L = 0
    · simp [hL]
    · field_simp
      ring
  · intro hall
    have h0 := hall 0
    simp only [Matrix.cons_val_zero] at h0
    rw [abs_neg] at h0
    have hnn : (0:ℝ) ≤ 4 * Mp / 3 := by positivity
    rw [abs_of_nonneg hnn] at h0
    linarith

/-! ## C. Statics, kinematics and work bridges -/

/-- Statics bridge: the canonical equilibrium equation of the finite model is the statical
equation of the uniformly loaded fixed-ended beam, the mid-span moment minus the mean end
moment equals `w * L ^ 2 / 8` (Neal, equation (2.2), `M₂ - M₁ = W l / 8`, written there for
equal end moments). -/
theorem hingeRotation_transpose_mulVec_eq_iff {L : ℝ} (σ : Fin 3 → ℝ) (w : ℝ) (hL : 0 < L) :
    (hingeRotation L)ᵀ *ᵥ σ = w • uniformLoadWork L ↔
      σ 1 - (σ 0 + σ 2) / 2 = w * L ^ 2 / 8 := by
  have hLne : L ≠ 0 := ne_of_gt hL
  rw [funext_iff, Fin.forall_fin_one]
  simp [hingeRotation, uniformLoadWork, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  constructor <;> intro h <;> field_simp at h ⊢ <;> linarith

/-- Admissibility between the hinges (Neal, Fig. 2.5(d)): the bending-moment diagram at collapse,
the free moment `(w / 2) * (L * x - x ^ 2)` of the load intensity `w = 16 * Mp / L ^ 2` plus the end
moments `-Mp`, stays within `± Mp` on the whole span `[0, L]`. For `0 < L` it takes the static
certificate's values `-Mp`, `Mp`, `-Mp` at `x = 0`, `L / 2` and `L`. The statement holds for every
real `L` (for `L < 0` the interval is empty; at `L = 0` it is `{0}`, where the value is `-Mp`, with
`w = 0` by the convention `x / 0 = 0`); the physical reading is `0 < L`. -/
lemma collapseMomentDiagram_abs_le (L : ℝ) {Mp : ℝ} (hMp : 0 ≤ Mp) :
    ∀ x ∈ Set.Icc 0 L, |(16 * Mp / L ^ 2 / 2) * (L * x - x ^ 2) - Mp| ≤ Mp := by
  intro x hx
  rw [Set.mem_Icc] at hx
  obtain ⟨hx0, hxL⟩ := hx
  by_cases hL : 0 < L
  · have hLne : L ≠ 0 := ne_of_gt hL
    have hL2 : (0:ℝ) < L ^ 2 := by positivity
    have hxLx : (0:ℝ) ≤ x * (L - x) := by
      apply mul_nonneg hx0
      linarith
    have hSq : (0:ℝ) ≤ (L - 2 * x) ^ 2 := sq_nonneg _
    rw [abs_le]
    constructor
    · have hA : (0:ℝ) ≤ (16 * Mp / L ^ 2 / 2) * (L * x - x ^ 2) := by
        have e1 : (L * x - x ^ 2 : ℝ) = x * (L - x) := by ring
        rw [e1]
        apply mul_nonneg _ hxLx
        positivity
      linarith
    · have hB : (16 * Mp / L ^ 2 / 2) * (L * x - x ^ 2) ≤ 2 * Mp := by
        have e2 : ((16 * Mp / L ^ 2 / 2) * (L * x - x ^ 2) - 2 * Mp : ℝ) =
            -((2 * Mp / L ^ 2) * (L - 2 * x) ^ 2) := by
          field_simp
          ring
        have hnn : (0:ℝ) ≤ (2 * Mp / L ^ 2) * (L - 2 * x) ^ 2 := by
          apply mul_nonneg _ hSq
          positivity
        linarith
      linarith
  · have hL' : L ≤ 0 := le_of_not_gt hL
    have hx0' : x = 0 := by linarith
    have hL0 : L = 0 := by linarith
    subst hx0'
    subst hL0
    simp
    rw [abs_of_nonneg hMp]

/-- Compatibility bridge: the hinge rotations `hingeRotation L *ᵥ ![δ]` are the slope jumps of the
mechanism deflection. Its segments have slopes `s₁` on `(0, L / 2)` and `s₂` on `(L / 2, L)`; with
zero slope at the clamped supports, each sagging hinge rotation is the slope on its left minus the
slope on its right. For `0 < L` the slopes are `2 * δ / L` and `-(2 * δ / L)`; for `L ≤ 0` the two
intervals are empty and the derivative conditions are vacuous. -/
lemma hingeRotation_mulVec_eq_slopeJumps (L δ : ℝ) :
    ∃ s₁ s₂ : ℝ, (∀ x ∈ Set.Ioo 0 (L / 2), HasDerivAt (mechanismDeflection L δ) s₁ x) ∧
      (∀ x ∈ Set.Ioo (L / 2) L, HasDerivAt (mechanismDeflection L δ) s₂ x) ∧
      hingeRotation L *ᵥ ![δ] = ![0 - s₁, s₁ - s₂, s₂ - 0] := by
  refine ⟨2 * δ / L, -(2 * δ / L), ?_, ?_, ?_⟩
  · intro x hx
    rw [Set.mem_Ioo] at hx
    have hlin : HasDerivAt (fun y : ℝ => (2 * δ / L) * y) (2 * δ / L) x :=
      hasDerivAt_const_mul (2 * δ / L)
    have heq : (fun y : ℝ => (2 * δ / L) * y) =ᶠ[nhds x] mechanismDeflection L δ := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      rw [Set.mem_Ioo] at hy
      have hlt : y < L - y := by linarith
      have hmin : min y (L - y) = y := min_eq_left (le_of_lt hlt)
      simp [mechanismDeflection, hmin]
    exact hlin.congr_of_eventuallyEq heq.symm
  · intro x hx
    rw [Set.mem_Ioo] at hx
    have hinner : HasDerivAt (fun y : ℝ => L - y) (-1) x := by
      have h := (hasDerivAt_id' x).const_sub L
      simpa using h
    have houter : HasDerivAt (fun y : ℝ => (2 * δ / L) * (L - y)) ((2 * δ / L) * (-1)) x :=
      hinner.const_mul (2 * δ / L)
    have hsimp : (2 * δ / L) * (-1) = -(2 * δ / L) := by ring
    rw [hsimp] at houter
    have heq : (fun y : ℝ => (2 * δ / L) * (L - y)) =ᶠ[nhds x]
        mechanismDeflection L δ := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      rw [Set.mem_Ioo] at hy
      have hlt : L - y < y := by linarith
      have hmin : min y (L - y) = L - y := min_eq_right (le_of_lt hlt)
      simp [mechanismDeflection, hmin]
    exact houter.congr_of_eventuallyEq heq.symm
  · ext i
    fin_cases i <;> simp [hingeRotation, Matrix.mulVec, dotProduct] <;> ring

/-- Work bridge: the work of the uniform load of intensity `w` through the mechanism
deflection with central deflection `δ` is `(w • f) ⬝ᵥ ![δ]`, that is `w * (L / 2) * δ`
(Neal, p. 27: the load moves on average half the central deflection). -/
lemma integral_mechanismDeflection {L : ℝ} (w δ : ℝ) (hL : 0 < L) :
    ∫ x in (0 : ℝ)..L, w * mechanismDeflection L δ x = (w • uniformLoadWork L) ⬝ᵥ ![δ] := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hL2nn : (0:ℝ) ≤ L / 2 := by linarith
  have hL2L : L / 2 ≤ L := by linarith
  have hcont : Continuous (fun x : ℝ => w * mechanismDeflection L δ x) := by
    unfold mechanismDeflection
    fun_prop
  have h1 : IntervalIntegrable (fun x : ℝ => w * mechanismDeflection L δ x) MeasureTheory.volume
      0 (L / 2) := hcont.intervalIntegrable 0 (L / 2)
  have h2 : IntervalIntegrable (fun x : ℝ => w * mechanismDeflection L δ x) MeasureTheory.volume
      (L / 2) L := hcont.intervalIntegrable (L / 2) L
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have e1 : Set.EqOn (fun x : ℝ => w * mechanismDeflection L δ x)
      (fun x : ℝ => (w * (2 * δ / L)) * x) (Set.uIcc 0 (L / 2)) := by
    intro x hx
    rw [Set.uIcc_of_le hL2nn] at hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hle : x ≤ L - x := by linarith
    have hmin : min x (L - x) = x := min_eq_left hle
    show w * mechanismDeflection L δ x = (w * (2 * δ / L)) * x
    simp only [mechanismDeflection, hmin]
    ring
  have e2 : Set.EqOn (fun x : ℝ => w * mechanismDeflection L δ x)
      (fun x : ℝ => (w * (2 * δ / L)) * L - (w * (2 * δ / L)) * x) (Set.uIcc (L / 2) L) := by
    intro x hx
    rw [Set.uIcc_of_le hL2L] at hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hle : L - x ≤ x := by linarith
    have hmin : min x (L - x) = L - x := min_eq_right hle
    show w * mechanismDeflection L δ x = (w * (2 * δ / L)) * L - (w * (2 * δ / L)) * x
    simp only [mechanismDeflection, hmin]
    ring
  have hconst : IntervalIntegrable (fun _ : ℝ => (w * (2 * δ / L)) * L) MeasureTheory.volume
      (L / 2) L := continuous_const.intervalIntegrable _ _
  have hinter : IntervalIntegrable (fun x : ℝ => (w * (2 * δ / L)) * x) MeasureTheory.volume
      (L / 2) L := by
    apply Continuous.intervalIntegrable _ _ _
    fun_prop
  have p1 : ∫ x in (0:ℝ)..(L / 2), w * mechanismDeflection L δ x
      = (w * (2 * δ / L)) * (((L / 2) ^ 2 - 0 ^ 2) / 2) := by
    rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_const_mul, integral_id]
  have p2 : ∫ x in (L / 2)..L, w * mechanismDeflection L δ x
      = (L - L / 2) * ((w * (2 * δ / L)) * L)
        - (w * (2 * δ / L)) * ((L ^ 2 - (L / 2) ^ 2) / 2) := by
    rw [intervalIntegral.integral_congr e2, intervalIntegral.integral_sub hconst hinter,
      intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul,
      integral_id]
  rw [← hsplit, p1, p2]
  simp [uniformLoadWork, dotProduct]
  field_simp
  ring

end Mechanics.BeamPlasticCollapse
