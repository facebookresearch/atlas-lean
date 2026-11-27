/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.LocalInverseColeHopf
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field

open Set ColeHopf
open scoped ContDiff

-- A profile singular at zero: every hypothesis is restricted to positive time.
private noncomputable def reciprocalProfile (t _x : ℝ) : ℝ := t⁻¹

private theorem reciprocal_smooth :
    ContDiffOn ℝ 3 (Function.uncurry reciprocalProfile) (Ioi 0 ×ˢ (univ : Set ℝ)) :=
  contDiffOn_fst.inv (fun _ hp => ne_of_gt hp.1)

private theorem reciprocal_heat (ν t x : ℝ) (ht : 0 < t) :
    deriv (fun s => reciprocalProfile s x) t =
      ν * iteratedDeriv 2 (reciprocalProfile t) x + (-t⁻¹) * reciprocalProfile t x := by
  change deriv (fun s : ℝ => s⁻¹) t =
    ν * iteratedDeriv 2 (fun _ : ℝ => t⁻¹) x + (-t⁻¹) * t⁻¹
  rw [(hasDerivAt_inv (ne_of_gt ht)).deriv]
  norm_num [iteratedDeriv_const]
  ring

example (ν : ℝ) (hν : ν ≠ 0) (t x : ℝ) (ht : 0 < t) :
    forcedInverseProfile ν (classicalTransform ν reciprocalProfile) (fun s _ => -s⁻¹)
      1 0 t x = t⁻¹ := by
  have h := OnInterval.forcedInverseProfile_classicalTransform isOpen_Ioi isOpen_univ
    ordConnected_Ioi ordConnected_univ ν hν reciprocalProfile (fun s _ => -s⁻¹)
    reciprocal_smooth (fun s hs _ _ => inv_pos.mpr hs)
    (fun s hs y _ => reciprocal_heat ν s y hs) 1 0 t x
    (by norm_num) (mem_univ 0) ht (mem_univ x)
  simpa [reciprocalProfile] using h

-- This witness really is singular at the excluded endpoint; global C³ is unavailable.
example : ¬ ContinuousAt (fun t => reciprocalProfile t 0) 0 := by
  intro hc
  exact not_tendsto_nhds_of_tendsto_atTop
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)) (reciprocalProfile 0 0)
    (hc.mono_left inf_le_left)

-- Reversing the time anchor is allowed; normalization is at an interior point.
example : forcedInverseProfile (-1) (classicalTransform (-1) reciprocalProfile)
    (fun s _ => -s⁻¹) 2 3 1 (-2) = 2 := by
  have h := OnInterval.forcedInverseProfile_classicalTransform isOpen_Ioi isOpen_univ
    ordConnected_Ioi ordConnected_univ (-1) (by norm_num) reciprocalProfile (fun s _ => -s⁻¹)
    reciprocal_smooth (fun s hs _ _ => inv_pos.mpr hs)
    (fun s hs y _ => reciprocal_heat (-1) s y hs) 2 3 1 (-2)
    (by norm_num) (mem_univ _) (by norm_num) (mem_univ _)
  norm_num [reciprocalProfile] at h ⊢
  exact h

private noncomputable def singularVelocity (t _x : ℝ) : ℝ := 2 * t⁻¹
private noncomputable def singularPotential (t x : ℝ) : ℝ := x * (t⁻¹) ^ 2

private theorem singular_velocity_smooth :
    ContDiffOn ℝ 2 (Function.uncurry singularVelocity) (Ioi 0 ×ˢ Ioo (-4) 4) :=
  contDiffOn_const.mul (contDiffOn_fst.inv (fun _ hp => ne_of_gt hp.1))

private theorem singular_potential_smooth :
    ContDiffOn ℝ 1 (Function.uncurry singularPotential) (Ioi 0 ×ˢ Ioo (-4) 4) :=
  contDiffOn_snd.mul ((contDiffOn_fst.inv
    (fun p (hp : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-4 : ℝ) 4) => ne_of_gt hp.1)).pow 2)

private theorem singular_burgers (t x : ℝ) (ht : 0 < t) :
    deriv (fun s => singularVelocity s x) t +
        singularVelocity t x * deriv (singularVelocity t) x =
      1 * iteratedDeriv 2 (singularVelocity t) x - 2 * 1 * deriv (singularPotential t) x := by
  change deriv (fun s : ℝ => 2 * s⁻¹) t +
      (2 * t⁻¹) * deriv (fun _ : ℝ => 2 * t⁻¹) x =
    1 * iteratedDeriv 2 (fun _ : ℝ => 2 * t⁻¹) x -
      2 * 1 * deriv (fun y : ℝ => y * (t⁻¹) ^ 2) x
  rw [((hasDerivAt_inv (ne_of_gt ht)).const_mul 2).deriv]
  norm_num [iteratedDeriv_const]

-- Both anchors exceed the evaluation coordinates. The potential has nonzero Fₓ.
example :
    deriv (fun s => forcedInverseProfile 1 singularVelocity singularPotential 2 3 s (-1)) 1 =
      iteratedDeriv 2 (forcedInverseProfile 1 singularVelocity singularPotential 2 3 1) (-1) +
        singularPotential 1 (-1) *
          forcedInverseProfile 1 singularVelocity singularPotential 2 3 1 (-1) := by
  simpa only [one_mul] using OnInterval.forcedInverseProfile_heat
    isOpen_Ioi isOpen_Ioo ordConnected_Ioi ordConnected_Ioo 1 (by norm_num)
    singularVelocity singularPotential singular_velocity_smooth singular_potential_smooth
    2 3 1 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun y _ => singular_burgers 1 y (by norm_num))

-- Recovery needs only spatial continuity, including for singular time dependence.
example (t x : ℝ) (hx : x ∈ Ioo (-4 : ℝ) 4) :
    classicalTransform 1 (forcedInverseProfile 1 singularVelocity singularPotential 2 3) t x =
      2 * t⁻¹ :=
  OnInterval.classicalTransform_forcedInverseProfile isOpen_Ioo ordConnected_Ioo
    1 (by norm_num) singularVelocity singularPotential 2 3 t x (by norm_num) hx
    continuousOn_const

-- A discontinuous extension is harmless: only its values inside the product matter.
private noncomputable def outsideField (t x : ℝ) : ℝ :=
  if 0 < t ∧ x ∈ Ioo (-4 : ℝ) 4 then singularVelocity t x else x

example (t x : ℝ) (ht : 0 < t) (hx : x ∈ Ioo (-4 : ℝ) 4) :
    forcedInverseProfile 1 outsideField singularPotential 2 3 t x =
      forcedInverseProfile 1 singularVelocity singularPotential 2 3 t x := by
  apply OnInterval.forcedInverseProfile_congr isOpen_Ioo ordConnected_Ioi ordConnected_Ioo
    1 outsideField singularVelocity singularPotential singularPotential ?_ (fun _ _ => rfl)
    2 3 t x (by norm_num) (by norm_num) ht hx
  intro p hp
  simp [Function.uncurry, outsideField, show 0 < p.1 from hp.1, hp.2]

-- Neither zero viscosity nor an excluded anchor can be silently treated as admissible.
example : classicalTransform 0
    (forcedInverseProfile 0 singularVelocity singularPotential 2 3) 1 0 ≠
      singularVelocity 1 0 := by
  norm_num [classicalTransform, singularVelocity]

example : (0 : ℝ) ∉ Ioi 0 := by simp

-- An unforced local inverse uses exactly the existing unforced definition.
example (t x : ℝ) (ht : 0 < t) :
    deriv (fun s => inverseProfile 1 (fun _ _ => 2) 1 0 s x) t =
      iteratedDeriv 2 (inverseProfile 1 (fun _ _ => 2) 1 0 t) x := by
  have h := OnInterval.forcedInverseProfile_heat isOpen_Ioi isOpen_univ
    ordConnected_Ioi ordConnected_univ 1 (by norm_num) (fun _ _ => 2) (fun _ _ => 0)
    contDiffOn_const contDiffOn_const 1 0 t x (by norm_num) (mem_univ _) ht (mem_univ _)
    (by intro y _; norm_num [iteratedDeriv_const])
  have hz : forcedInverseProfile 1 (fun _ _ => 2) (fun _ _ => 0) 1 0 =
      inverseProfile 1 (fun _ _ => 2) 1 0 := by
    funext s y
    exact forcedInverseProfile_zero _ _ _ _ _ _
  rw [hz] at h
  simpa only [one_mul, zero_mul, add_zero] using h

private noncomputable def cutProfile (c t x : ℝ) : ℝ := if 0 < t then c else x

private theorem cut_smooth (c : ℝ) :
    ContDiffOn ℝ 3 (Function.uncurry (cutProfile c)) (Ioi 0 ×ˢ (univ : Set ℝ)) := by
  apply (contDiffOn_const (c := c)).congr
  intro p hp
  simp [Function.uncurry, cutProfile, show 0 < p.1 from hp.1]

private theorem cut_heat (c t x : ℝ) (ht : 0 < t) :
    deriv (fun s => cutProfile c s x) t =
      1 * iteratedDeriv 2 (cutProfile c t) x + 0 * cutProfile c t x := by
  have he : (fun s => cutProfile c s x) =ᶠ[nhds t] (fun _ => c) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    simp [cutProfile, show 0 < s from hs]
  rw [he.deriv_eq]
  have hx : cutProfile c t = fun _ => c := by funext y; simp [cutProfile, ht]
  rw [hx]
  norm_num [iteratedDeriv_const]

private theorem cut_transform (c t x : ℝ) (ht : 0 < t) :
    classicalTransform 1 (cutProfile c) t x = 0 := by
  have hx : cutProfile c t = fun _ => c := by funext y; simp [cutProfile, ht]
  simp [classicalTransform, hx]

-- Uniqueness uses equality of transforms only on positive time, not on the plane.
example : ∃! c : ℝ, 0 < c ∧ ∀ t ∈ Ioi (0 : ℝ), ∀ x ∈ (univ : Set ℝ),
    cutProfile 3 t x = c * (1 : ℝ) := by
  apply OnInterval.potentialProfiles_existsUnique_scale isOpen_Ioi isOpen_univ
    ordConnected_Ioi ordConnected_univ 1 (by norm_num) (cutProfile 3) (fun _ _ => 1)
    (fun _ _ => 0) (cut_smooth 3) contDiffOn_const
    (by intro t ht x _; simp [cutProfile, show 0 < t from ht]) (by intros; norm_num)
    (fun t ht x _ => cut_heat 3 t x ht)
    (by intros; norm_num [iteratedDeriv_const]) ?_ 1 0 (by norm_num) (mem_univ _)
  intro p hp
  change classicalTransform 1 (cutProfile 3) p.1 p.2 =
    classicalTransform 1 (fun _ _ => 1) p.1 p.2
  rw [cut_transform 3 p.1 p.2 hp.1]
  simp [classicalTransform]

-- A fixed base value gives equality on the domain; the extensions actually disagree.
example : EqOn (Function.uncurry (cutProfile 1)) (fun _ => (1 : ℝ))
    (Ioi 0 ×ˢ (univ : Set ℝ)) := by
  apply OnInterval.potentialProfiles_eqOn_of_base_eq isOpen_Ioi isOpen_univ
    ordConnected_Ioi ordConnected_univ 1 (by norm_num) (cutProfile 1) (fun _ _ => 1)
    (fun _ _ => 0) (cut_smooth 1) contDiffOn_const
    (by intro t ht x _; simp [cutProfile, show 0 < t from ht]) (by intros; norm_num)
    (fun t ht x _ => cut_heat 1 t x ht)
    (by intros; norm_num [iteratedDeriv_const]) ?_ 1 0 (by norm_num) (mem_univ _) (by
      norm_num [cutProfile])
  intro p hp
  change classicalTransform 1 (cutProfile 1) p.1 p.2 =
    classicalTransform 1 (fun _ _ => 1) p.1 p.2
  rw [cut_transform 1 p.1 p.2 hp.1]
  simp [classicalTransform]

example : cutProfile 1 (-1) 2 ≠ 1 ∧
    classicalTransform 1 (cutProfile 1) (-1) 2 ≠ classicalTransform 1 (fun _ _ => 1) (-1) 2 := by
  have he : cutProfile 1 (-1) = fun y => y := by funext y; norm_num [cutProfile]
  norm_num [classicalTransform, he, cutProfile]
