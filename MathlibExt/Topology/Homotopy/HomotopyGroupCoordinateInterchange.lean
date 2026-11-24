/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>
module

public import MathlibExt.Topology.Homotopy.HomotopyGroupMap
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FunProp

/-!
# The actual square-coordinate interchange and reflection homotopy

The path of invertible real matrices interpolating between reflection and
coordinate interchange is radially normalized in the square norm. This
keeps the complete square boundary in the boundary at every time. Its
application to generalized loops therefore gives a homotopy relative to
the full cube boundary, rather than an identity only at selected points.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open scoped Topology unitInterval

namespace HomotopyGroup.CoordinateInterchange

/-- The actual invertible linear interpolation from reflection to interchange. -/
def rawTurn (q : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (-(1 - q.1) * q.2.1 + q.1 * q.2.2,
    q.1 * q.2.1 + (1 - q.1) * q.2.2)

/-- The entire interpolating matrix is invertible at every time. -/
theorem rawTurn_eq_zero_iff (q : ℝ × (ℝ × ℝ)) : rawTurn q = 0 ↔ q.2 = 0 := by
  rcases q with ⟨t, x, y⟩
  constructor
  · intro h
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    change -(1 - t) * x + t * y = 0 at ha
    change t * x + (1 - t) * y = 0 at hb
    have hd : 0 < t * t + (1 - t) * (1 - t) := by
      nlinarith [sq_nonneg (t - 1 / 2)]
    have hx : (t * t + (1 - t) * (1 - t)) * x = 0 := by
      linear_combination -(1 - t) * ha + t * hb
    have hy : (t * t + (1 - t) * (1 - t)) * y = 0 := by
      linear_combination t * ha + (1 - t) * hb
    exact Prod.ext ((mul_eq_zero.mp hx).resolve_left hd.ne')
      ((mul_eq_zero.mp hy).resolve_left hd.ne')
  · intro h
    change (x, y) = (0, 0) at h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    change x = 0 at hx
    change y = 0 at hy
    simp [rawTurn, hx, hy]

/-- The original matrix path is jointly continuous in its time and both coordinates. -/
theorem continuous_rawTurn : Continuous rawTurn := by
  unfold rawTurn
  fun_prop

/-- Normalize by the actual square radius, with the genuine total division at the center. -/
def turn (q : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (‖q.2‖ / ‖rawTurn q‖) • rawTurn q

/-- Every whole radial image retains exactly the original square radius. -/
theorem turn_norm (q : ℝ × (ℝ × ℝ)) : ‖turn q‖ = ‖q.2‖ := by
  by_cases h : rawTurn q = 0
  · have hp := (rawTurn_eq_zero_iff q).mp h
    simp [turn, h, hp]
  · rw [turn, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr h)]

/-- The radial interpolation is continuous even at the actual center of the square. -/
theorem continuous_turn : Continuous turn := by
  rw [continuous_iff_continuousAt]
  intro q
  by_cases h : rawTurn q = 0
  · have hp := (rawTurn_eq_zero_iff q).mp h
    have ht : turn q = 0 := by simp [turn, h]
    rw [ContinuousAt, ht]
    apply (tendsto_zero_iff_norm_tendsto_zero).mpr
    simpa only [turn_norm, hp, norm_zero] using continuous_snd.norm.tendsto q
  · exact ((continuous_snd.norm.continuousAt.div continuous_rawTurn.norm.continuousAt
      (norm_ne_zero_iff.mpr h)).smul continuous_rawTurn.continuousAt)

/-- The time-zero matrix is the original first-coordinate reflection. -/
theorem rawTurn_zero (p : ℝ × ℝ) : rawTurn (0, p) = (-p.1, p.2) := by
  simp [rawTurn]

/-- The time-one matrix is the original full coordinate interchange. -/
theorem rawTurn_one (p : ℝ × ℝ) : rawTurn (1, p) = (p.2, p.1) := by
  simp [rawTurn]

/-- Radial normalization retains the complete first-coordinate reflection endpoint. -/
theorem turn_zero (p : ℝ × ℝ) : turn (0, p) = (-p.1, p.2) := by
  change (‖p‖ / ‖rawTurn (0, p)‖) • rawTurn (0, p) = _
  rw [rawTurn_zero]
  have hn : ‖(-p.1, p.2)‖ = ‖p‖ := by simp [Prod.norm_def, Real.norm_eq_abs]
  rw [hn]
  by_cases hp : p = 0
  · simp [hp]
    rfl
  · rw [div_self (norm_ne_zero_iff.mpr hp), one_smul]

/-- Radial normalization retains the complete coordinate-interchange endpoint. -/
theorem turn_one (p : ℝ × ℝ) : turn (1, p) = (p.2, p.1) := by
  change (‖p‖ / ‖rawTurn (1, p)‖) • rawTurn (1, p) = _
  rw [rawTurn_one]
  have hn : ‖(p.2, p.1)‖ = ‖p‖ := by
    simp only [Prod.norm_def, Real.norm_eq_abs, max_comm]
  rw [hn]
  by_cases hp : p = 0
  · simp [hp]
    rfl
  · rw [div_self (norm_ne_zero_iff.mpr hp), one_smul]

/-- The actual affine centered coordinates of a point of the original unit square. -/
def centered (p : unitInterval × unitInterval) : ℝ × ℝ :=
  (2 * (p.1 : ℝ) - 1, 2 * (p.2 : ℝ) - 1)

/-- Both original centered coordinates depend continuously on the original unit-square point. -/
@[fun_prop]
theorem continuous_centered : Continuous centered := by
  unfold centered
  fun_prop

/-- Centering the entire original unit square lands in its closed square ball. -/
theorem centered_norm_le_one (p : unitInterval × unitInterval) : ‖centered p‖ ≤ 1 := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · change |2 * (p.1 : ℝ) - 1| ≤ 1
    exact abs_le.mpr ⟨by nlinarith [p.1.property.1], by nlinarith [p.1.property.2]⟩
  · change |2 * (p.2 : ℝ) - 1| ≤ 1
    exact abs_le.mpr
      ⟨by nlinarith [p.2.property.1], by nlinarith [p.2.property.2]⟩

/-- A centered coordinate with its full closed-interval bound returns to the unit interval. -/
def uncenter (x : ℝ) (hx : |x| ≤ 1) : unitInterval :=
  ⟨(x + 1) / 2, by
    exact ⟨by nlinarith [(abs_le.mp hx).1], by nlinarith [(abs_le.mp hx).2]⟩⟩

/-- The full radially normalized square map at every original time. -/
def squareTurn (q : unitInterval × (unitInterval × unitInterval)) :
    unitInterval × unitInterval :=
  let z := turn ((q.1 : ℝ), centered q.2)
  let hz : ‖z‖ ≤ 1 := (turn_norm _).le.trans (centered_norm_le_one q.2)
  (uncenter z.1 (by
      exact (le_max_left _ _).trans
        (by simpa only [Prod.norm_def, Real.norm_eq_abs] using hz)),
    uncenter z.2 (by
      exact (le_max_right _ _).trans (by simpa only [Prod.norm_def, Real.norm_eq_abs] using hz)))

/-- The actual square map is jointly continuous in time and both entire original coordinates. -/
theorem continuous_squareTurn : Continuous squareTurn := by
  have h : Continuous fun q : unitInterval × (unitInterval × unitInterval) =>
      turn ((q.1 : ℝ), centered q.2) := continuous_turn.comp (by fun_prop)
  apply Continuous.prodMk
  · exact ((h.fst.add continuous_const).div_const 2).subtype_mk _
  · exact ((h.snd.add continuous_const).div_const 2).subtype_mk _

/-- The time-zero square map reflects its actual first coordinate and keeps the second. -/
theorem squareTurn_zero (p : unitInterval × unitInterval) :
    squareTurn (0, p) = (σ p.1, p.2) := by
  apply Prod.ext
  · apply Subtype.ext
    change ((turn (0, centered p)).1 + 1) / 2 = 1 - (p.1 : ℝ)
    rw [turn_zero]
    dsimp [centered]
    ring
  · apply Subtype.ext
    change ((turn (0, centered p)).2 + 1) / 2 = (p.2 : ℝ)
    rw [turn_zero]
    dsimp [centered]
    ring

/-- The time-one square map exchanges both entire original coordinates. -/
theorem squareTurn_one (p : unitInterval × unitInterval) : squareTurn (1, p) = (p.2, p.1) := by
  apply Prod.ext
  · apply Subtype.ext
    change ((turn (1, centered p)).1 + 1) / 2 = (p.2 : ℝ)
    rw [turn_one]
    dsimp [centered]
    ring
  · apply Subtype.ext
    change ((turn (1, centered p)).2 + 1) / 2 = (p.1 : ℝ)
    rw [turn_one]
    dsimp [centered]
    ring

private theorem uncenter_endpoint {x : ℝ} (hx : |x| ≤ 1) (h : |x| = 1) :
    uncenter x hx = 0 ∨ uncenter x hx = 1 := by
  rcases abs_eq_abs.mp (show |x| = |(1 : ℝ)| by simpa using h) with h | h
  · right
    apply Subtype.ext
    change (x + 1) / 2 = 1
    rw [h]
    norm_num
  · left
    apply Subtype.ext
    change (x + 1) / 2 = 0
    rw [h]
    norm_num

/-- The centered radius of every original boundary point is exactly one. -/
theorem centered_norm_eq_one_of_boundary (p : unitInterval × unitInterval)
    (hp : p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) : ‖centered p‖ = 1 := by
  apply le_antisymm (centered_norm_le_one p)
  rcases hp with h | h | h | h
  · have h1 : ‖(centered p).1‖ = 1 := by norm_num [centered, h]
    rw [← h1]
    exact le_max_left _ _
  · have h1 : ‖(centered p).1‖ = 1 := by norm_num [centered, h]
    rw [← h1]
    exact le_max_left _ _
  · have h2 : ‖(centered p).2‖ = 1 := by norm_num [centered, h]
    rw [← h2]
    exact le_max_right _ _
  · have h2 : ‖(centered p).2‖ = 1 := by norm_num [centered, h]
    rw [← h2]
    exact le_max_right _ _

/-- At every time the entire original square boundary remains in the boundary. -/
theorem squareTurn_boundary (q : unitInterval × (unitInterval × unitInterval))
    (hq : q.2.1 = 0 ∨ q.2.1 = 1 ∨ q.2.2 = 0 ∨ q.2.2 = 1) :
    (squareTurn q).1 = 0 ∨ (squareTurn q).1 = 1 ∨
      (squareTurn q).2 = 0 ∨ (squareTurn q).2 = 1 := by
  let z := turn ((q.1 : ℝ), centered q.2)
  have hn : ‖z‖ = 1 := (turn_norm _).trans (centered_norm_eq_one_of_boundary q.2 hq)
  have hz : ‖z‖ ≤ 1 := hn.le
  have hx : |z.1| ≤ 1 := (le_max_left _ _).trans
    (by simpa only [Prod.norm_def, Real.norm_eq_abs] using hz)
  have hy : |z.2| ≤ 1 := (le_max_right _ _).trans
    (by simpa only [Prod.norm_def, Real.norm_eq_abs] using hz)
  rcases le_total |z.1| |z.2| with h | h
  · have hy1 : |z.2| = 1 := by
      simpa only [Prod.norm_def, Real.norm_eq_abs, max_eq_right h] using hn
    rcases uncenter_endpoint hy hy1 with h0 | h1
    · exact Or.inr (Or.inr (Or.inl h0))
    · exact Or.inr (Or.inr (Or.inr h1))
  · have hx1 : |z.1| = 1 := by
      simpa only [Prod.norm_def, Real.norm_eq_abs, max_eq_left h] using hn
    rcases uncenter_endpoint hx hx1 with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)

section Cubes

universe uN uX
variable {N : Type uN} [DecidableEq N]

/-- Turn exactly the two selected original cube coordinates, retaining every other coordinate. -/
def cubeTurn (i j : N) (q : unitInterval × (N → unitInterval)) : N → unitInterval :=
  Function.update (Function.update q.2 i (squareTurn (q.1, q.2 i, q.2 j)).1)
    j (squareTurn (q.1, q.2 i, q.2 j)).2

/-- The entire first selected coordinate follows the original square homotopy. -/
theorem cubeTurn_first (i j : N) (hij : i ≠ j) (q : unitInterval × (N → unitInterval)) :
    cubeTurn i j q i = (squareTurn (q.1, q.2 i, q.2 j)).1 := by
  simp [cubeTurn, hij]

/-- The entire second selected coordinate follows that same square homotopy. -/
theorem cubeTurn_second (i j : N) (q : unitInterval × (N → unitInterval)) :
    cubeTurn i j q j = (squareTurn (q.1, q.2 i, q.2 j)).2 := by
  simp [cubeTurn]

/-- Every unselected original coordinate is unchanged at every time. -/
theorem cubeTurn_other (i j a : N) (hai : a ≠ i) (haj : a ≠ j)
    (q : unitInterval × (N → unitInterval)) : cubeTurn i j q a = q.2 a := by
  simp [cubeTurn, hai, haj]

/-- The complete original cube turn is continuous in time and all original coordinates. -/
theorem continuous_cubeTurn (i j : N) : Continuous (cubeTurn i j) := by
  have h : Continuous fun q : unitInterval × (N → unitInterval) =>
      squareTurn (q.1, q.2 i, q.2 j) := continuous_squareTurn.comp (by fun_prop)
  apply continuous_pi
  intro a
  by_cases haj : a = j
  · subst a
    simpa only [cubeTurn_second] using h.snd
  · by_cases hai : a = i
    · subst a
      simpa only [cubeTurn_first i j haj] using h.fst
    · simpa only [cubeTurn_other i j a hai haj, Function.comp_def] using
        (continuous_apply a).comp continuous_snd

/-- The time-zero full cube map is the original single-coordinate reversal. -/
theorem cubeTurn_zero (i j : N) (hij : i ≠ j) (p : N → unitInterval) :
    cubeTurn i j (0, p) = Function.update p i (σ (p i)) := by
  funext a
  by_cases haj : a = j
  · subst a
    rw [cubeTurn_second, squareTurn_zero]
    simp [hij.symm]
  · by_cases hai : a = i
    · subst a
      rw [cubeTurn_first i j hij, squareTurn_zero]
      simp
    · rw [cubeTurn_other i j a hai haj]
      simp [hai]

/-- The time-one full cube map is the original entire two-coordinate transposition. -/
theorem cubeTurn_one (i j : N) (hij : i ≠ j) (p : N → unitInterval) :
    cubeTurn i j (1, p) = p ∘ Equiv.swap i j := by
  funext a
  by_cases haj : a = j
  · subst a
    rw [cubeTurn_second, squareTurn_one]
    simp
  · by_cases hai : a = i
    · subst a
      rw [cubeTurn_first i j hij, squareTurn_one]
      simp
    · rw [cubeTurn_other i j a hai haj]
      simp [Equiv.swap_apply_of_ne_of_ne hai haj]

/-- The entire original cube boundary stays in the boundary under the actual turn. -/
theorem cubeTurn_boundary (i j : N) (hij : i ≠ j)
    (q : unitInterval × (N → unitInterval)) (hq : q.2 ∈ Cube.boundary N) :
    cubeTurn i j q ∈ Cube.boundary N := by
  rcases hq with ⟨a, ha⟩
  by_cases hai : a = i
  · subst a
    have h := squareTurn_boundary (q.1, q.2 i, q.2 j)
      (ha.elim Or.inl (fun h => Or.inr (Or.inl h)))
    rcases h with h | h | h | h
    · exact ⟨i, Or.inl ((cubeTurn_first i j hij q).trans h)⟩
    · exact ⟨i, Or.inr ((cubeTurn_first i j hij q).trans h)⟩
    · exact ⟨j, Or.inl ((cubeTurn_second i j q).trans h)⟩
    · exact ⟨j, Or.inr ((cubeTurn_second i j q).trans h)⟩
  · by_cases haj : a = j
    · subst a
      have h := squareTurn_boundary (q.1, q.2 i, q.2 j)
        (Or.inr (Or.inr ha))
      rcases h with h | h | h | h
      · exact ⟨i, Or.inl ((cubeTurn_first i j hij q).trans h)⟩
      · exact ⟨i, Or.inr ((cubeTurn_first i j hij q).trans h)⟩
      · exact ⟨j, Or.inl ((cubeTurn_second i j q).trans h)⟩
      · exact ⟨j, Or.inr ((cubeTurn_second i j q).trans h)⟩
    · exact ⟨a, (cubeTurn_other i j a hai haj q) ▸ ha⟩

variable {X : Type uX} [TopologicalSpace X] {x : X}

/-- Turning the original two coordinates gives a homotopy relative to the complete cube boundary. -/
def reflectionSwapHomotopy (i j : N) (hij : i ≠ j) (p : GenLoop N X x) :
    ContinuousMap.HomotopyRel (GenLoop.symmAt i p).1
      (GenLoop.congr x (Equiv.swap i j) p).1 (Cube.boundary N) where
  toFun q := p (cubeTurn i j q)
  continuous_toFun := p.1.continuous.comp (continuous_cubeTurn i j)
  map_zero_left q := by
    rw [cubeTurn_zero i j hij]
    change p (Function.update q i (σ (q i))) =
      p (fun a => if a = i then σ (q i) else q a)
    exact congrArg p (by ext a; simp [Function.update_apply])
  map_one_left q := by
    rw [cubeTurn_one i j hij]
    rfl
  prop' t q hq :=
    (GenLoop.boundary p (cubeTurn i j (t, q)) (cubeTurn_boundary i j hij (t, q) hq)).trans
      (GenLoop.boundary (GenLoop.symmAt i p) q hq).symm

/-- The full original transposition acts by inversion on the actual cube homotopy group. -/
theorem swap_class_eq_inverse [Nonempty N] (i j : N) (hij : i ≠ j) (p : GenLoop N X x) :
    HomotopyGroup.mk (GenLoop.congr x (Equiv.swap i j) p) =
      (HomotopyGroup.mk p)⁻¹ := by
  calc
    _ = HomotopyGroup.mk (GenLoop.symmAt i p) :=
      Quotient.sound ⟨(reflectionSwapHomotopy i j hij p).symm⟩
    _ = _ := (HomotopyGroup.inv_spec (i := i) (p := p)).symm

end Cubes

end HomotopyGroup.CoordinateInterchange
