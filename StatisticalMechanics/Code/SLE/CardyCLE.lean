/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Mathlib
import Code.SLE.Defs
import Code.SLE.Cardy

open scoped UpperHalfPlane NNReal
open Complex Filter Topology

namespace StatMech.SLE























def HasConformalRadius (z : ℂ) (φ : ℂ → ℂ) (r : ℝ) : Prop :=
  φ 0 = z ∧ HasDerivAt φ (r : ℂ) 0 ∧ 0 < r





noncomputable def discConformalRadius (r : ℝ) : ℝ := r

@[simp] lemma discConformalRadius_apply (r : ℝ) : discConformalRadius r = r := rfl




noncomputable def discRiemannMap (z : ℂ) (r : ℝ) : ℂ → ℂ := fun w => z + (r : ℂ) * w

@[simp] lemma discRiemannMap_apply (z : ℂ) (r : ℝ) (w : ℂ) :
    discRiemannMap z r w = z + (r : ℂ) * w := rfl


@[simp] lemma discRiemannMap_zero (z : ℂ) (r : ℝ) : discRiemannMap z r 0 = z := by
  simp [discRiemannMap]


lemma hasDerivAt_discRiemannMap (z : ℂ) (r : ℝ) :
    HasDerivAt (discRiemannMap z r) (r : ℂ) 0 := by
  unfold discRiemannMap
  have h : HasDerivAt (fun w : ℂ => z + (r : ℂ) * w) ((r : ℂ) * 1) 0 :=
    ((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)).const_add z
  simpa using h




lemma hasConformalRadius_disc (z : ℂ) {r : ℝ} (hr : 0 < r) :
    HasConformalRadius z (discRiemannMap z r) r :=
  ⟨discRiemannMap_zero z r, hasDerivAt_discRiemannMap z r, hr⟩


lemma HasConformalRadius.pos {z : ℂ} {φ : ℂ → ℂ} {r : ℝ}
    (h : HasConformalRadius z φ r) : 0 < r := h.2.2



lemma HasConformalRadius.map_zero {z : ℂ} {φ : ℂ → ℂ} {r : ℝ}
    (h : HasConformalRadius z φ r) : φ 0 = z := h.1



lemma HasConformalRadius.unique {z : ℂ} {φ : ℂ → ℂ} {r₁ r₂ : ℝ}
    (h₁ : HasConformalRadius z φ r₁) (h₂ : HasConformalRadius z φ r₂) : r₁ = r₂ := by
  have := h₁.2.1.unique h₂.2.1
  exact_mod_cast this





lemma discConformalRadius_strictMono : StrictMono discConformalRadius :=
  strictMono_id



lemma discConformalRadius_mono : Monotone discConformalRadius :=
  monotone_id


lemma discConformalRadius_pos {r : ℝ} (hr : 0 < r) : 0 < discConformalRadius r := hr














inductive SLEPhase where
  
  | simple : SLEPhase
  

  | selfTouching : SLEPhase
  
  | spaceFilling : SLEPhase
  deriving DecidableEq, Repr



noncomputable def slePhase (κ : ℝ) : SLEPhase :=
  if κ ≤ 4 then SLEPhase.simple
  else if κ < 8 then SLEPhase.selfTouching
  else SLEPhase.spaceFilling


lemma slePhase_of_le_four {κ : ℝ} (h : κ ≤ 4) : slePhase κ = SLEPhase.simple := by
  simp [slePhase, h]



lemma slePhase_of_mem_Ioo {κ : ℝ} (h1 : 4 < κ) (h2 : κ < 8) :
    slePhase κ = SLEPhase.selfTouching := by
  have : ¬ κ ≤ 4 := by linarith
  simp [slePhase, this, h2]



lemma slePhase_of_eight_le {κ : ℝ} (h : 8 ≤ κ) :
    slePhase κ = SLEPhase.spaceFilling := by
  have h1 : ¬ κ ≤ 4 := by linarith
  have h2 : ¬ κ < 8 := by linarith
  simp [slePhase, h1, h2]



@[simp] lemma slePhase_four : slePhase 4 = SLEPhase.simple :=
  slePhase_of_le_four le_rfl



@[simp] lemma slePhase_eight : slePhase 8 = SLEPhase.spaceFilling :=
  slePhase_of_eight_le le_rfl


@[simp] lemma slePhase_zero : slePhase 0 = SLEPhase.simple :=
  slePhase_of_le_four (by norm_num)



@[simp] lemma slePhase_six : slePhase 6 = SLEPhase.selfTouching :=
  slePhase_of_mem_Ioo (by norm_num) (by norm_num)



lemma slePhase_eq_simple_iff {κ : ℝ} (hκ : 0 ≤ κ) :
    slePhase κ = SLEPhase.simple ↔ IsSimplePhase κ := by
  unfold slePhase IsSimplePhase
  constructor
  · intro h
    by_cases hc : κ ≤ 4
    · exact ⟨hκ, hc⟩
    · simp only [hc, if_false] at h
      split at h <;> simp_all
  · rintro ⟨_, h4⟩
    simp [h4]



lemma slePhase_eq_selfTouching_iff {κ : ℝ} :
    slePhase κ = SLEPhase.selfTouching ↔ IsSelfTouchingPhase κ := by
  unfold slePhase IsSelfTouchingPhase
  constructor
  · intro h
    by_cases hc : κ ≤ 4
    · simp [hc] at h
    · by_cases hc' : κ < 8
      · exact ⟨lt_of_not_ge hc, hc'⟩
      · simp [hc, hc'] at h
  · rintro ⟨h4, h8⟩
    have : ¬ κ ≤ 4 := by linarith
    simp [this, h8]



lemma slePhase_eq_spaceFilling_iff {κ : ℝ} :
    slePhase κ = SLEPhase.spaceFilling ↔ IsSpaceFillingPhase κ := by
  unfold slePhase IsSpaceFillingPhase
  constructor
  · intro h
    by_cases hc : κ ≤ 4
    · simp [hc] at h
    · by_cases hc' : κ < 8
      · simp [hc, hc'] at h
      · exact le_of_not_gt hc'
  · intro h
    have h1 : ¬ κ ≤ 4 := by linarith
    have h2 : ¬ κ < 8 := by linarith
    simp [h1, h2]



lemma slePhase_kappaPercolation : slePhase kappaPercolation = SLEPhase.selfTouching :=
  slePhase_eq_selfTouching_iff.mpr kappaPercolation_selfTouching


lemma slePhase_kappaIsing : slePhase kappaIsing = SLEPhase.simple :=
  (slePhase_eq_simple_iff kappaIsing_simple.1).mpr kappaIsing_simple













lemma cardyCrossing_eq (s : ℝ) :
    cardyCrossing s =
      cardyPrefactor * s ^ ((1 : ℝ) / 3) *
        ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3) (4 / 3) s := rfl




lemma cardyCrossing_factor_pos {s : ℝ} (hs : 0 < s) :
    0 < cardyPrefactor * s ^ ((1 : ℝ) / 3) :=
  mul_pos cardyPrefactor_pos (Real.rpow_pos_of_pos hs _)




lemma cardyHypergeometric_zero :
    ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3) (4 / 3) (0 : ℝ) = 1 :=
  ordinaryHypergeometric_zero _ _ _












def cleParameterSet : Set ℝ := {κ | 8 / 3 < κ ∧ κ ≤ 8}


@[simp] lemma mem_cleParameterSet {κ : ℝ} : κ ∈ cleParameterSet ↔ IsCLEParameter κ :=
  Iff.rfl


lemma cleParameterSet_subset_pos : cleParameterSet ⊆ {κ : ℝ | 0 < κ} :=
  fun _ hκ => IsCLEParameter.pos hκ




lemma kappaPercolation_mem_cleParameterSet : kappaPercolation ∈ cleParameterSet := by
  refine ⟨?_, ?_⟩ <;> norm_num [kappaPercolation]



lemma kappaFKIsing_mem_cleParameterSet : kappaFKIsing ∈ cleParameterSet := by
  refine ⟨?_, ?_⟩ <;> norm_num [kappaFKIsing]



lemma kappaIsing_mem_cleParameterSet : kappaIsing ∈ cleParameterSet := by
  refine ⟨?_, ?_⟩ <;> norm_num [kappaIsing]










def IsConformallyInvariantLoopLaw {Ω : Type*} [MeasurableSpace Ω]
    (loops : Ω → Set (Set ℂ)) (μ : MeasureTheory.Measure Ω) : Prop :=
  ∀ (m : Mobius ℂ) (relabel : Ω → Ω), Measurable relabel →
    (∀ ω, loops (relabel ω) = (fun S => m.apply '' S) '' (loops ω)) →
    MeasureTheory.Measure.map relabel μ = μ





lemma idLoopLaw_invariant_under_id {Ω : Type*} [MeasurableSpace Ω]
    (loops : Ω → Set (Set ℂ)) (μ : MeasureTheory.Measure Ω) :
    Measurable (id : Ω → Ω) ∧
      (∀ ω, loops (id ω) = (fun S => (Mobius.id ℂ).apply '' S) '' (loops ω)) →
      MeasureTheory.Measure.map id μ = μ := by
  rintro ⟨_, _⟩
  simp

end StatMech.SLE
