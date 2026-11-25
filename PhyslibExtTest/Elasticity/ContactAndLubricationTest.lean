/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Elasticity.ContactAndLubrication
import PhyslibExt.CondensedMatter.Elasticity.StressStrain
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Contact and lubrication checks

Concrete consumers of `PhyslibExt.Elasticity.ContactAndLubrication`. Plane slider: the
converging film `h0 = 2`, `hL = 1`, `μ = U = L = 1` (existence, uniqueness, positive pressure,
the load `6 log 2 - 4 > 0`), the diverging film `h0 = 1`, `hL = 2` (pressure `-2/9` at the
midpoint) and the film that closes at the outlet (no solution). Scalar contact: loaded contact
`k = 2`, `g = 1`, `f = 4` (the hypotheses of Stampacchia's theorem, existence, uniqueness and
complementarity), separation `f = 1`, and the failure of coercivity at `k = 0`. Coulomb
friction at `μ = 1/2`, `N = 10`: nonzero slip in each direction with its nonpositive power,
non-unique stick forces and the static-equilibrium criterion; and the negative coefficient
`μ = -1/2`, which admits no stick force and makes slip supply power. Contact admission: the
public shapes of Section D, separated and closed contact at friction coefficient `1`, the
non-convex admissible set, the frictionless bridge to Section B, and invalid controls
(negative friction coefficient, tension excluded by the cone at `μ = 0`, a non-unit normal).
Coulomb sliding and sticking: the public shapes of Section E, nonzero slip `(3, 4)` with
power `-25`, sticking without division by zero, the `μ = 0` slice, invalid-sign and
rejection controls, the tangent-line reduction to Section C, and the open/stick/slip frame
fixture in `ℝ³` with power `-50`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Plane-slider lubrication
- B. Scalar unilateral contact
- C. Coulomb friction
- D. Unilateral contact with Coulomb friction
- E. Coulomb sliding and sticking at a unilateral interface

## iv. References

- `PhyslibExt.Elasticity.ContactAndLubrication`
-/

open Elasticity.ContactAndLubrication

/-! ## A. Plane-slider lubrication -/

/-- End-to-end consumer for the converging slider `h0 = 2`, `hL = 1`, `μ = U = L = 1`: the film
is open at the outlet, the closed-form pressure solves the Reynolds model, every solution takes
the value `2/9` at the midpoint, the pressure there is positive, and so is the load per unit
width. -/
example {p p' : ℝ → ℝ} (hp : IsReynoldsSolution 1 1 2 1 1 p p') :
    0 < sliderFilm 2 1 1 1 ∧
      IsReynoldsSolution 1 1 2 1 1 (sliderPressure 1 1 2 1 1) (sliderPressureGradient 1 1 2 1 1) ∧
      p (1 / 2) = 2 / 9 ∧ 0 < sliderPressure 1 1 2 1 1 (1 / 2) ∧ 0 < sliderLoad 1 1 2 1 1 := by
  refine ⟨sliderFilm_pos (by norm_num) (by norm_num) (by norm_num) ⟨by norm_num, le_rfl⟩,
    sliderPressure_isReynoldsSolution (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    ?_, sliderPressure_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ⟨by norm_num, by norm_num⟩,
    sliderLoad_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩
  rw [isReynoldsSolution_unique (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp
    (1 / 2) ⟨by norm_num, by norm_num⟩]
  norm_num [sliderPressure, sliderFilm]

/-- The model only sees values on `[0, L]`: the closed-form pressure of the converging slider,
changed to `1` for `x < 0`, still solves the Reynolds model, although the changed pressure jumps
at the inlet and so has no derivative there. -/
example :
    IsReynoldsSolution 1 1 2 1 1 (fun x => if x < 0 then 1 else sliderPressure 1 1 2 1 1 x)
        (sliderPressureGradient 1 1 2 1 1) ∧
      ¬ DifferentiableAt ℝ (fun x => if x < 0 then 1 else sliderPressure 1 1 2 1 1 x) 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := sliderPressure_isReynoldsSolution (μ := 1) (U := 1) (h0 := 2)
    (hL := 1) (L := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have heq : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      (if y < 0 then 1 else sliderPressure 1 1 2 1 1 y) = sliderPressure 1 1 2 1 1 y :=
    fun y hy => by simp [not_lt.mpr hy.1]
  refine ⟨⟨fun x hx => (h1 x hx).congr_of_mem heq hx, h2, ?_, ?_⟩, ?_⟩
  · have h00 : ¬ (0 : ℝ) < 0 := lt_irrefl 0
    simpa [h00] using h3
  · have h10 : ¬ (1 : ℝ) < 0 := by norm_num
    simpa [h10] using h4
  · intro hd
    have hleft : Filter.Tendsto (fun x => if x < 0 then 1 else sliderPressure 1 1 2 1 1 x)
        (nhdsWithin 0 (Set.Iio 0)) (nhds 1) :=
      tendsto_const_nhds.congr'
        (eventually_nhdsWithin_of_forall fun x hx => by simp [Set.mem_Iio.mp hx])
    have hcont := hd.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio 0))
    have hval := tendsto_nhds_unique hleft hcont
    have h00 : ¬ (0 : ℝ) < 0 := lt_irrefl 0
    simp only [h00, ↓reduceIte] at hval
    rw [h3] at hval
    norm_num at hval

/-- Nonzero load for a converging film: `h0 = 2`, `hL = 1` and `μ = U = L = 1` give the load per
unit width `6 log 2 - 4`, which is positive. -/
example :
    sliderLoad 1 1 2 1 1 = 6 * Real.log 2 - 4 ∧ 0 < 6 * Real.log 2 - 4 := by
  have h := sliderLoad_eq (μ := 1) (U := 1) (h0 := 2) (hL := 1) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · rw [h]
    have e1 : (2 : ℝ) / 1 = 2 := by norm_num
    rw [e1]
    norm_num
    ring
  · have hlog := Real.log_two_gt_d9
    linarith

/-- Diverging-film fixture: `h0 = 1`, `hL = 2` and `μ = U = L = 1` give the pressure `-2/9` at
the midpoint. -/
example :
    sliderPressure 1 1 1 2 1 (1 / 2) = -2 / 9 := by
  unfold sliderPressure sliderFilm
  norm_num

/-- Outside the converging regime the model fails: for the diverging film `h0 = 1`, `hL = 2` with
`μ = U = L = 1` the no-cavitation pressure is negative at the midpoint, and a film that closes at
the outlet (`hL = 0`) admits no solution of the Reynolds model. -/
example (p p' : ℝ → ℝ) :
    sliderPressure 1 1 1 2 1 (1 / 2) < 0 ∧ ¬ IsReynoldsSolution 1 1 1 0 1 p p' :=
  ⟨sliderPressure_neg_of_diverging (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ⟨by norm_num, by norm_num⟩,
    not_isReynoldsSolution_of_hL_eq_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

/-! ## B. Scalar unilateral contact -/

open scoped InnerProductSpace

/-- End-to-end consumer for loaded contact `k = 2`, `g = 1`, `f = 4`: the hypotheses of
Stampacchia's theorem hold, the contact variational inequality has exactly one solution, every
solution is the obstacle position `1`, and it satisfies complementarity with contact force `2`. -/
example {u : ℝ}
    (hu : u ∈ admissibleSet 1 ∧ ∀ v ∈ admissibleSet 1, 0 ≤ ⟪stiffnessMap 2 u - 4, v - u⟫_ℝ) :
    (admissibleSet 1).Nonempty ∧ IsClosed (admissibleSet 1) ∧ Convex ℝ (admissibleSet 1) ∧
      (∃ α : ℝ, 0 < α ∧ ∀ w : ℝ, α * ‖w‖ ^ 2 ≤ ⟪stiffnessMap 2 w, w⟫_ℝ) ∧
      (∃! w, w ∈ admissibleSet 1 ∧ ∀ v ∈ admissibleSet 1, 0 ≤ ⟪stiffnessMap 2 w - 4, v - w⟫_ℝ) ∧
      u = 1 ∧ contactForce 2 4 u = 2 ∧ 0 ≤ contactGap 1 u ∧
      contactForce 2 4 u * contactGap 1 u = 0 := by
  have hu1 : u = 1 := by
    rw [(contact_vi_iff (by norm_num) 1 4 u).mp hu]
    norm_num [contactDisplacement]
  obtain ⟨_, hgap, hprod⟩ := complementarity_of_vi hu
  refine ⟨admissibleSet_nonempty 1, isClosed_admissibleSet 1, convex_admissibleSet 1,
    stiffnessMap_coercive (by norm_num), existsUnique_contact (by norm_num) 1 4, hu1, ?_, hgap,
    hprod⟩
  rw [hu1]
  norm_num [contactForce]

/-- Separation `k = 2`, `g = 1`, `f = 1`: the displacement `1 / 2` solves the contact
variational inequality, the contact displacement satisfies complementarity, and on `ℝ` the
inequality's inner product is a product, for example `⟪2 · 3 - 1, 2⟫ = 10`. -/
example :
    ((1 / 2 : ℝ) ∈ admissibleSet 1 ∧
        ∀ v ∈ admissibleSet 1, 0 ≤ ⟪stiffnessMap 2 (1 / 2) - 1, v - 1 / 2⟫_ℝ) ∧
      ⟪stiffnessMap 2 3 - 1, 2⟫_ℝ = 10 ∧
      0 ≤ contactForce 2 1 (contactDisplacement 2 1 1) ∧
      0 ≤ contactGap 1 (contactDisplacement 2 1 1) ∧
      contactForce 2 1 (contactDisplacement 2 1 1) * contactGap 1 (contactDisplacement 2 1 1) =
        0 := by
  refine ⟨(contact_vi_iff (by norm_num) 1 1 (1 / 2)).mpr ?_, ?_,
    contactDisplacement_complementarity (by norm_num) 1 1⟩
  · norm_num [contactDisplacement]
  · rw [inner_stiffnessMap_sub]
    norm_num

/-- Loaded contact: `k = 2`, `g = 1`, `f = 4` give `u = 1` on the obstacle, the positive contact
force `λ = 2` and zero gap. -/
example :
    contactDisplacement 2 1 4 = 1 ∧ contactForce 2 4 (contactDisplacement 2 1 4) = 2 ∧
      contactGap 1 (contactDisplacement 2 1 4) = 0 := by
  have h42 : (4 : ℝ) / 2 = 2 := by norm_num
  have h1 : contactDisplacement 2 1 4 = 1 := by
    show min (1 : ℝ) ((4 : ℝ) / 2) = 1
    rw [h42]
    exact min_eq_left (by norm_num)
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]
    simp only [contactForce]
    norm_num
  · rw [h1]
    simp only [contactGap]
    norm_num

/-- Separation: `k = 2`, `g = 1`, `f = 1` give `u = 1 / 2` below the obstacle, zero contact
force and the positive gap `1 / 2`. -/
example :
    contactDisplacement 2 1 1 = 1 / 2 ∧ contactForce 2 1 (contactDisplacement 2 1 1) = 0 ∧
      contactGap 1 (contactDisplacement 2 1 1) = 1 / 2 := by
  have h1 : contactDisplacement 2 1 1 = 1 / 2 := by
    show min (1 : ℝ) ((1 : ℝ) / 2) = 1 / 2
    exact min_eq_right (by norm_num)
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]
    simp only [contactForce]
    norm_num
  · rw [h1]
    simp only [contactGap]
    norm_num

/-- At zero stiffness the coercivity hypothesis fails for every `α > 0`. -/
example :
    ¬ ∃ α : ℝ, 0 < α ∧ ∀ u : ℝ, α * ‖u‖ ^ 2 ≤ ⟪stiffnessMap 0 u, u⟫_ℝ := by
  rintro ⟨α, hα, h⟩
  have h1 := h 1
  have hmap : stiffnessMap (0 : ℝ) (1 : ℝ) = 0 := by simp [stiffnessMap]
  rw [hmap, inner_zero_left] at h1
  simp only [norm_one, one_pow, mul_one] at h1
  linarith

/-! ## C. Coulomb friction -/

/-- Nonzero slip in each direction, `μ = 1/2`, `N = 10`: at `v = 2` the only admissible force is
`-5` (power `-10`), at `v = -3` it is `5` (power `-15`). -/
example :
    (∀ F, IsCoulombFriction (1 / 2) 10 2 F ↔ F = -5) ∧
      ∀ F, IsCoulombFriction (1 / 2) 10 (-3) F ↔ F = 5 := by
  constructor
  · intro F
    rw [isCoulombFriction_of_ne_zero (by norm_num : (2:ℝ) ≠ 0),
      Real.sign_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num
  · intro F
    rw [isCoulombFriction_of_ne_zero (by norm_num : (-3:ℝ) ≠ 0),
      Real.sign_of_neg (by norm_num : (-3:ℝ) < 0)]
    norm_num

/-- Friction power on the slip fixture `μ = 1/2`, `N = 10`: every graph force at `v = 2` delivers
the power `-μ N |v| = -10`, which is nonpositive. -/
example : ∀ F, IsCoulombFriction (1 / 2) 10 2 F → F * 2 = -10 ∧ F * 2 ≤ 0 := by
  intro F h
  refine ⟨?_, coulomb_power_nonpos (by norm_num) (by norm_num) h⟩
  rw [coulomb_power_eq h]
  norm_num

/-- At rest, `μ = 1/2`, `N = 10`: the forces `0` and `5` are both admissible and `6` is not; the
applied force `4` is held in static equilibrium and `6` is not. -/
example :
    IsCoulombFriction (1 / 2) 10 0 0 ∧ IsCoulombFriction (1 / 2) 10 0 5 ∧
      ¬ IsCoulombFriction (1 / 2) 10 0 6 ∧
      (∃ F, IsCoulombFriction (1 / 2) 10 0 F ∧ 4 + F = 0) ∧
      ¬ ∃ F, IsCoulombFriction (1 / 2) 10 0 F ∧ 6 + F = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [isCoulombFriction_zero]
    norm_num [Set.mem_Icc]
  · rw [isCoulombFriction_zero]
    norm_num [Set.mem_Icc]
  · rw [isCoulombFriction_zero]
    norm_num [Set.mem_Icc]
  · exact coulomb_static_equilibrium_iff.mpr (by norm_num [Set.mem_Icc])
  · intro h
    have hFa := coulomb_static_equilibrium_iff.mp h
    norm_num [Set.mem_Icc] at hFa

/-- At rest the friction force is not determined: for `μ = 1/2`, `N = 10` two different forces
are admissible at `v = 0`. -/
example :
    ∃ F₁ F₂ : ℝ, F₁ ≠ F₂ ∧ IsCoulombFriction (1 / 2) 10 0 F₁ ∧ IsCoulombFriction (1 / 2) 10 0 F₂ :=
  coulomb_stick_not_unique (by norm_num) (by norm_num)

/-- A negative coefficient, `μ = -1/2`, `N = 10`: no force is admissible at rest, and at `v = 1`
the only graph force is `5`, along the motion, which supplies the power `5`. -/
example :
    (¬ ∃ F, IsCoulombFriction (-1 / 2) 10 0 F) ∧
      ∀ F, IsCoulombFriction (-1 / 2) 10 1 F ↔ F = 5 := by
  constructor
  · exact coulomb_not_exists_stick_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)
      (by norm_num : (0:ℝ) < 10)
  · intro F
    rw [isCoulombFriction_of_ne_zero (by norm_num : (1:ℝ) ≠ 0),
      Real.sign_of_pos (by norm_num : (0:ℝ) < 1)]
    norm_num

/-- A negative coefficient makes slip supply power: for `μ = -1/2`, `N = 10` every graph force at
`v = 1` delivers positive power. -/
example : ∀ F, IsCoulombFriction (-1 / 2) 10 1 F → 0 < F * 1 :=
  fun _ h => coulomb_slip_power_pos_of_neg (by norm_num) (by norm_num) one_ne_zero h

/-! ## D. Unilateral contact with Coulomb friction -/

/-- The public statement shape of the frame bridge. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n τ t : E} {N : ℝ}
    (hn : ‖n‖ = 1) :
    (τ = t - N • n ∧ ⟪t, n⟫_ℝ = 0) ↔ (N = -⟪τ, n⟫_ℝ ∧ t = τ - ⟪τ, n⟫_ℝ • n) :=
  normal_tangent_decomposition_iff hn

/-- The public statement shapes of the cone results. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : ℝ} (hμ : 0 ≤ μ) :
    Convex ℝ (frictionCone (E := E) μ) ∧
      ¬ Convex ℝ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 * p.2 = 0} :=
  ⟨convex_frictionCone hμ, not_convex_complementarity⟩

/-- Frame coordinates directly from a traction: `N = -⟪τ, n⟫` and
`t = τ - ⟪τ, n⟫ • n` give the decomposition `τ = t - N • n` with `t` orthogonal to `n`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n τ : E}
    (hn : ‖n‖ = 1) :
    τ = (τ - ⟪τ, n⟫_ℝ • n) - (-⟪τ, n⟫_ℝ) • n ∧ ⟪τ - ⟪τ, n⟫_ℝ • n, n⟫_ℝ = 0 :=
  (normal_tangent_decomposition_iff hn).mpr ⟨rfl, rfl⟩

/-- Separated contact: the state `N = 0`, `g = 1`, `t = 0` over `ℝ` is admissible at
friction coefficient `1`, and every admissible state with `0 < g` has zero force. -/
example : IsAdmissibleContact 1 0 1 (0 : ℝ) ∧
    ∀ {μ N g : ℝ} {t : ℝ}, IsAdmissibleContact μ N g t → 0 < g → N = 0 ∧ t = 0 :=
  ⟨by norm_num [IsAdmissibleContact], fun h hg =>
    IsAdmissibleContact.eq_zero_of_gap_pos h hg⟩

/-- Closed loaded contact at `g = 0` (the removed pin target, as a test): at zero gap,
admission is exactly cone membership. At `μ = 1`, `N = 1` the stick
state `t = 1 / 2` and the slip threshold `t = 1` are admissible over `ℝ`, and `t = 2` is not. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ N : ℝ} {t : E} :
    (IsAdmissibleContact μ N 0 t ↔ (N, t) ∈ frictionCone μ) ∧
      IsAdmissibleContact 1 1 0 (1 / 2 : ℝ) ∧ IsAdmissibleContact 1 1 0 (1 : ℝ) ∧
      ¬ IsAdmissibleContact 1 1 0 (2 : ℝ) := by
  refine ⟨?_, by norm_num [IsAdmissibleContact], by norm_num [IsAdmissibleContact],
    by norm_num [IsAdmissibleContact]⟩
  simp [IsAdmissibleContact, frictionCone, and_comm]

/-- At `μ = 0` the cone is the nonnegative normal ray; tension is excluded by the cone and
by admission: `(-1, 0)` is outside `frictionCone 0`, `(1, 0)` is inside, and the state
with `N = -1` is not admissible. Universally, `frictionCone 0` is the ray
`{p | 0 ≤ p.1 ∧ p.2 = 0}`. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ((-1, 0) : ℝ × ℝ) ∉ frictionCone 0 ∧ ((1, 0) : ℝ × ℝ) ∈ frictionCone 0 ∧
      ¬ IsAdmissibleContact 0 (-1) 0 (0 : ℝ) ∧
      frictionCone (E := E) 0 = {p | 0 ≤ p.1 ∧ p.2 = 0} := by
  refine ⟨by norm_num [frictionCone], by norm_num [frictionCone],
    by norm_num [IsAdmissibleContact], ?_⟩
  ext ⟨N, t⟩
  simp only [frictionCone, Set.mem_ofPred_eq, zero_mul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, norm_le_zero_iff.mp h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h2, norm_zero], h1⟩

/-- The full admissible set in `(N, g, t)` over `ℝ` at `μ = 1` is not convex: the midpoint
of the closed state `(1, 0, 0)` and the separated state `(0, 1, 0)` has `N * g = 1 / 4`. -/
example : ¬ Convex ℝ {p : ℝ × ℝ × ℝ | IsAdmissibleContact 1 p.1 p.2.1 p.2.2} := by
  intro h
  have hx : ((1, 0, 0) : ℝ × ℝ × ℝ) ∈ {p : ℝ × ℝ × ℝ | IsAdmissibleContact 1 p.1 p.2.1 p.2.2} := by
    norm_num [IsAdmissibleContact]
  have hy : ((0, 1, 0) : ℝ × ℝ × ℝ) ∈ {p : ℝ × ℝ × ℝ | IsAdmissibleContact 1 p.1 p.2.1 p.2.2} := by
    norm_num [IsAdmissibleContact]
  have hm := h hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, IsAdmissibleContact]
    at hm
  norm_num at hm

/-- Frictionless bridge to Section B: the scalar contact solution's complementarity triple is
an admissible Section D state with zero tangent traction, for every `0 ≤ μ`. -/
example {k g f u μ : ℝ} (hμ : 0 ≤ μ)
    (hu : u ∈ admissibleSet g ∧ ∀ v ∈ admissibleSet g, 0 ≤ ⟪stiffnessMap k u - f, v - u⟫_ℝ) :
    IsAdmissibleContact μ (contactForce k f u) (contactGap g u) (0 : ℝ) :=
  (isAdmissibleContact_zero_tangent_iff hμ).mpr (complementarity_of_vi hu)

/-- Compression-positive traction sign binding: `compressionPositiveTraction` is the negative
of the Cauchy traction, the sign behind `N = -⟪τ, n⟫`. -/
example {n : ℕ} (σ : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Elasticity.compressionPositiveTraction σ v = -Elasticity.traction σ v := rfl

/-- Invalid controls: a negative friction coefficient admits no zero-tangent state with
`N = 1`; the frame formulas need a unit normal (`n = 2` over `ℝ` satisfies the left side of
the decomposition for `τ = -2`, `t = 0`, `N = 1`, but `N ≠ -⟪τ, n⟫ = 4`). -/
example : ¬ IsAdmissibleContact (-1) 1 0 (0 : ℝ) ∧
    ((-(2 : ℝ)) = (0 : ℝ) - (1 : ℝ) • (2 : ℝ) ∧ ⟪(0 : ℝ), (2 : ℝ)⟫_ℝ = 0) ∧
      (1 : ℝ) ≠ -⟪(-(2 : ℝ)), (2 : ℝ)⟫_ℝ := by
  norm_num [IsAdmissibleContact, RCLike.inner_apply]

/-! ## E. Coulomb sliding and sticking at a unilateral interface -/

/-- The public statement shapes of Section E. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ N : ℝ} {v t : E}
    (hμ : 0 ≤ μ) (hN : 0 ≤ N) (h : IsCoulombTraction μ N v t) :
    (⟪t, v⟫_ℝ = -(μ * N * ‖v‖) ∧ ⟪t, v⟫_ℝ ≤ 0) ∧ IsAdmissibleContact μ N 0 t :=
  ⟨h.inner_eq_and_nonpos hμ hN, h.isAdmissibleContact hμ hN⟩

/-- The public statement shapes of the sign control and the tangent-line bridge. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ N : ℝ} {v t : E}
    (hμN : μ * N < 0) (h : IsCoulombTraction μ N v t) :
    0 < ⟪t, v⟫_ℝ ∧ ∀ {μ' N' v' F : ℝ}, IsCoulombTraction μ' N' v' F ↔ IsCoulombFriction μ' N' v' F :=
  ⟨h.inner_pos_of_mul_neg hμN, isCoulombTraction_iff_isCoulombFriction⟩

/-- Nonzero slip in the plane, `μ = 1/2`, `N = 10`, `v = (3, 4)`: the traction is `(-3, -4)`,
at the slip threshold `‖t‖ = μ N = 5`, with power `-25 = -μ N ‖v‖ < 0`. -/
example : IsCoulombTraction (1 / 2) 10 (!₂[3, 4] : EuclideanSpace ℝ (Fin 2)) !₂[-3, -4] ∧
    ⟪(!₂[-3, -4] : EuclideanSpace ℝ (Fin 2)), !₂[3, 4]⟫_ℝ = -25 ∧
    ‖(!₂[-3, -4] : EuclideanSpace ℝ (Fin 2))‖ = 1 / 2 * 10 := by
  have h34 : ‖(!₂[3, 4] : EuclideanSpace ℝ (Fin 2))‖ = 5 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
    rw [show (3:ℝ) ^ 2 + 4 ^ 2 = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hv : (!₂[3, 4] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [h34, norm_zero] at this
    norm_num at this
  have hlaw : IsCoulombTraction (1 / 2) 10 (!₂[3, 4] : EuclideanSpace ℝ (Fin 2)) !₂[-3, -4] := by
    refine ⟨fun _ => ?_, fun h => absurd h hv⟩
    rw [h34]
    ext i
    fin_cases i <;> simp <;> norm_num
  refine ⟨hlaw, ?_, ?_⟩
  · rw [(hlaw.inner_eq_and_nonpos (by norm_num) (by norm_num)).1, h34]
    norm_num
  · rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
    rw [show (3:ℝ) ^ 2 + 4 ^ 2 = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num

/-- Sticking does not divide by zero: at `v = 0` the stick rule is the Coulomb bound itself;
the totalized slip formula would give only `t = 0`, while the stick traction `(1, 0)` is
admissible at `μ = 1/2`, `N = 10` and does no work. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ N : ℝ} {t : E} :
    (IsCoulombTraction μ N (0 : E) t ↔ ‖t‖ ≤ μ * N) ∧
      -(μ * N) • (‖(0 : E)‖⁻¹ • (0 : E)) = 0 ∧
      IsCoulombTraction (1 / 2) 10 (0 : EuclideanSpace ℝ (Fin 2)) !₂[1, 0] ∧
      ⟪(!₂[1, 0] : EuclideanSpace ℝ (Fin 2)), 0⟫_ℝ = 0 := by
  have h10 : ‖(!₂[1, 0] : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
  refine ⟨⟨fun h => h.2 rfl, fun h => ⟨fun h0 => absurd rfl h0, fun _ => h⟩⟩, by simp,
    ⟨fun h => absurd rfl h, fun _ => by rw [h10]; norm_num⟩, inner_zero_right _⟩

/-- `μ = 0`: the only Coulomb traction is `0`, for every `N` and `v`, so the power is zero. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (N : ℝ) (v t : E) :
    IsCoulombTraction 0 N v t ↔ t = 0 := by
  constructor
  · intro h
    by_cases hv : v = 0
    · have := h.2 hv
      rw [zero_mul] at this
      exact norm_le_zero_iff.mp this
    · rw [h.1 hv]
      simp
  · rintro rfl
    exact ⟨fun _ => by simp, fun _ => by simp⟩

/-- Invalid controls on a tangent line, `v = 1`: `μ = -1/2 < 0 < N = 10` and
`N = -10 < 0 < μ = 1/2` give Coulomb tractions with positive power; `μ = -1`, `N = 1` and
`μ = 1`, `N = -1` give Coulomb tractions that are not admissible. -/
example : 0 < ⟪(5 : ℝ), 1⟫_ℝ ∧ IsCoulombTraction (-1 / 2) 10 (1 : ℝ) 5 ∧
    IsCoulombTraction (1 / 2) (-10) (1 : ℝ) 5 ∧
    (IsCoulombTraction (-1) 1 (1 : ℝ) 1 ∧ ¬ IsAdmissibleContact (-1) 1 0 (1 : ℝ)) ∧
    (IsCoulombTraction 1 (-1) (1 : ℝ) 1 ∧ ¬ IsAdmissibleContact 1 (-1) 0 (1 : ℝ)) := by
  refine ⟨by simp, ⟨fun _ => by norm_num, fun h => absurd h one_ne_zero⟩,
    ⟨fun _ => by norm_num, fun h => absurd h one_ne_zero⟩,
    ⟨⟨fun _ => by norm_num, fun h => absurd h one_ne_zero⟩, ?_⟩,
    ⟨⟨fun _ => by norm_num, fun h => absurd h one_ne_zero⟩, ?_⟩⟩
  · norm_num [IsAdmissibleContact]
  · norm_num [IsAdmissibleContact]

/-- Section C on a tangent line: the scalar fixture `μ = 1/2`, `N = 10`, `v = 2`, `F = -5` is a
Coulomb traction, and Section C's power identity follows from the vector one. -/
example {μ N v F : ℝ} (hμ : 0 ≤ μ) (hN : 0 ≤ N) (h : IsCoulombFriction μ N v F) :
    IsCoulombTraction (1 / 2) 10 (2 : ℝ) (-5) ∧ F * v = -(μ * N * |v|) := by
  refine ⟨isCoulombTraction_iff_isCoulombFriction.mpr
    ((isCoulombFriction_of_ne_zero two_ne_zero).mpr (by rw [Real.sign_of_pos two_pos]; norm_num)),
    ?_⟩
  have h1 := ((isCoulombTraction_iff_isCoulombFriction.mpr h).inner_eq_and_nonpos hμ hN).1
  have hi : ⟪F, v⟫_ℝ = F * v := by simp [mul_comm]
  rw [hi, Real.norm_eq_abs] at h1
  exact h1

/-- Open, stick and slip at `μ = 1/2` over the Section D frame in `ℝ³` with `n = e₃`: an open
gap carries no force; `τ = (3, 4, -10)` has `N = 10` and tangent part `t = (3, 4, 0)`, the
Coulomb traction for the slip `v = (-6, -8, 0)`, with power `-50`. -/
example : (∀ {N g : ℝ} {t : EuclideanSpace ℝ (Fin 3)},
      IsAdmissibleContact (1 / 2) N g t → 0 < g → N = 0 ∧ t = 0) ∧
    (!₂[3, 4, -10] : EuclideanSpace ℝ (Fin 3)) = !₂[3, 4, 0] - (10 : ℝ) • !₂[0, 0, 1] ∧
    IsCoulombTraction (1 / 2) 10 (!₂[-6, -8, 0] : EuclideanSpace ℝ (Fin 3)) !₂[3, 4, 0] ∧
    ⟪(!₂[3, 4, 0] : EuclideanSpace ℝ (Fin 3)), !₂[-6, -8, 0]⟫_ℝ = -50 := by
  have hn : ‖(!₂[0, 0, 1] : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp
  have hv : ‖(!₂[-6, -8, 0] : EuclideanSpace ℝ (Fin 3))‖ = 10 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp
    rw [show (6:ℝ) ^ 2 + 8 ^ 2 = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hlaw : IsCoulombTraction (1 / 2) 10 (!₂[-6, -8, 0] : EuclideanSpace ℝ (Fin 3))
      !₂[3, 4, 0] := by
    refine ⟨fun _ => ?_, fun h => ?_⟩
    · rw [hv]
      ext i
      fin_cases i <;> simp <;> norm_num
    · have := congrArg norm h
      rw [hv, norm_zero] at this
      norm_num at this
  refine ⟨fun h hg => h.eq_zero_of_gap_pos hg, ?_, hlaw, ?_⟩
  · exact ((normal_tangent_decomposition_iff (τ := (!₂[3, 4, -10] : EuclideanSpace ℝ (Fin 3)))
      (t := !₂[3, 4, 0]) (N := 10) hn).mpr ⟨by simp [PiLp.inner_apply, Fin.sum_univ_three],
      by ext i; fin_cases i <;> simp [PiLp.inner_apply, Fin.sum_univ_three]⟩).1
  · rw [(hlaw.inner_eq_and_nonpos (by norm_num) (by norm_num)).1, hv]
    norm_num
/-- Boundary and rejection controls: for `μ * N < 0` no stick traction exists; the stick
traction `(6, 8)` violates the cone at `μ = 1/2`, `N = 10`; at slip `v = (3, 4)` the
tractions `(1, 0)` and `(3, 4)` are rejected; and at `μ * N = 0` the power is `0`, not
positive, so the sign control is strict. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ N : ℝ} {t : E} :
    (μ * N < 0 → ¬ IsCoulombTraction μ N (0 : E) t) ∧
      ¬ IsCoulombTraction (1 / 2) 10 (0 : EuclideanSpace ℝ (Fin 2)) !₂[6, 8] ∧
      ¬ IsCoulombTraction (1 / 2) 10 (!₂[3, 4] : EuclideanSpace ℝ (Fin 2)) !₂[1, 0] ∧
      ¬ IsCoulombTraction (1 / 2) 10 (!₂[3, 4] : EuclideanSpace ℝ (Fin 2)) !₂[3, 4] ∧
      ⟪(0 : ℝ), 1⟫_ℝ = 0 ∧ IsCoulombTraction 0 1 (1 : ℝ) 0 := by
  have h34 : ‖(!₂[3, 4] : EuclideanSpace ℝ (Fin 2))‖ = 5 := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp
    rw [show (3:ℝ) ^ 2 + 4 ^ 2 = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hv : (!₂[3, 4] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [h34, norm_zero] at this
    norm_num at this
  refine ⟨fun hμN h => absurd (h.2 rfl) (not_le.mpr (lt_of_lt_of_le hμN (norm_nonneg t))),
    ?_, ?_, ?_, by simp, ⟨fun _ => by norm_num, fun h => absurd h one_ne_zero⟩⟩
  · intro h
    have h68 : ‖(!₂[6, 8] : EuclideanSpace ℝ (Fin 2))‖ = 10 := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      simp
      rw [show (6:ℝ) ^ 2 + 8 ^ 2 = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have := h.2 rfl
    rw [h68] at this
    norm_num at this
  · intro h
    have h1 := h.1 hv
    rw [h34] at h1
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h1
    simp at this
    norm_num at this
  · intro h
    have h1 := h.1 hv
    rw [h34] at h1
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h1
    simp at this
    norm_num at this

#print axioms Elasticity.ContactAndLubrication.IsCoulombTraction.inner_eq_and_nonpos
#print axioms Elasticity.ContactAndLubrication.IsCoulombTraction.inner_pos_of_mul_neg
#print axioms Elasticity.ContactAndLubrication.IsCoulombTraction.isAdmissibleContact
#print axioms Elasticity.ContactAndLubrication.isCoulombTraction_iff_isCoulombFriction
