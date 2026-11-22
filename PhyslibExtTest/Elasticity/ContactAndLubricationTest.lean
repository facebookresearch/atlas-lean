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
friction: the public shapes of Section C, separated and closed contact at friction
coefficient `1`, the non-convex admissible set, the frictionless bridge to Section B, and
invalid controls (negative friction coefficient, tension admitted by the cone alone, a
non-unit normal).

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Plane-slider lubrication
- B. Scalar unilateral contact
- C. Unilateral contact with Coulomb friction

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

/-! ## C. Unilateral contact with Coulomb friction -/

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

/-- Closed loaded contact at `g = 0` (the removed pin target, as a test): admission is a
nonnegative normal force with `(N, t)` in the friction cone. At `μ = 1`, `N = 1` the stick
state `t = 1 / 2` and the slip threshold `t = 1` are admissible over `ℝ`, and `t = 2` is not. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ N : ℝ} {t : E} :
    (IsAdmissibleContact μ N 0 t ↔ 0 ≤ N ∧ (N, t) ∈ frictionCone μ) ∧
      IsAdmissibleContact 1 1 0 (1 / 2 : ℝ) ∧ IsAdmissibleContact 1 1 0 (1 : ℝ) ∧
      ¬ IsAdmissibleContact 1 1 0 (2 : ℝ) := by
  refine ⟨?_, by norm_num [IsAdmissibleContact], by norm_num [IsAdmissibleContact],
    by norm_num [IsAdmissibleContact]⟩
  simp [IsAdmissibleContact, frictionCone]

/-- Tension is excluded by admission, not by the cone: `(-1, 0)` lies in `frictionCone 0`
over `ℝ`, but the state with `N = -1` is not admissible. -/
example : ((-1, 0) : ℝ × ℝ) ∈ frictionCone 0 ∧ ¬ IsAdmissibleContact 0 (-1) 0 (0 : ℝ) := by
  norm_num [frictionCone, IsAdmissibleContact]

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
an admissible Section C state with zero tangent traction, for every `0 ≤ μ`. -/
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
