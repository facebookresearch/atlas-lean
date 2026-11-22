/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryRLPCalculus

/-!
# The actual comparison maps for two successive restrictions

The three vertical maps and two commuting restriction squares specify all
pullbacks and comparison maps below. Pasting preserves both projections.
Boundary lifting cancels using genuine categorical fibrations; reflection
of the first comparison uses a boundary-trivial base restriction.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MorphismProperty

namespace SSet.RelativePullback

variable {X₀ X₁ X₂ B₀ B₁ B₂ : SSet.{u}}

/-- The comparison into the original pullback of one commuting square. -/
def comparison (f : X₁ ⟶ X₀) (p₀ : X₀ ⟶ B₀) (p₁ : X₁ ⟶ B₁)
    (b : B₁ ⟶ B₀) (h : f ≫ p₀ = p₁ ≫ b) : X₁ ⟶ pullback p₀ b :=
  pullback.lift f p₁ h

@[reassoc (attr := simp)]
theorem comparison_fst (f : X₁ ⟶ X₀) (p₀ : X₀ ⟶ B₀) (p₁ : X₁ ⟶ B₁)
    (b : B₁ ⟶ B₀) (h : f ≫ p₀ = p₁ ≫ b) :
    comparison f p₀ p₁ b h ≫ pullback.fst p₀ b = f := by
  simp [comparison]

@[reassoc (attr := simp)]
theorem comparison_snd (f : X₁ ⟶ X₀) (p₀ : X₀ ⟶ B₀) (p₁ : X₁ ⟶ B₁)
    (b : B₁ ⟶ B₀) (h : f ≫ p₀ = p₁ ≫ b) :
    comparison f p₀ p₁ b h ≫ pullback.snd p₀ b = p₁ := by
  simp [comparison]

/-- The actual base map between the pullbacks for the first and total restrictions. -/
def baseMap (p₀ : X₀ ⟶ B₀) (b : B₁ ⟶ B₀) (c : B₂ ⟶ B₁) :
    pullback p₀ (c ≫ b) ⟶ pullback p₀ b :=
  pullback.lift (pullback.fst p₀ (c ≫ b)) (pullback.snd p₀ (c ≫ b) ≫ c)
    (by simp only [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
theorem baseMap_fst (p₀ : X₀ ⟶ B₀) (b : B₁ ⟶ B₀) (c : B₂ ⟶ B₁) :
    baseMap p₀ b c ≫ pullback.fst p₀ b = pullback.fst p₀ (c ≫ b) := by
  simp [baseMap]

@[reassoc (attr := simp)]
theorem baseMap_snd (p₀ : X₀ ⟶ B₀) (b : B₁ ⟶ B₀) (c : B₂ ⟶ B₁) :
    baseMap p₀ b c ≫ pullback.snd p₀ b = pullback.snd p₀ (c ≫ b) ≫ c := by
  simp [baseMap]

/-- The base map is the pullback of the original second base restriction. -/
theorem baseMap_isPullback (p₀ : X₀ ⟶ B₀) (b : B₁ ⟶ B₀) (c : B₂ ⟶ B₁) :
    IsPullback (baseMap p₀ b c) (pullback.snd p₀ (c ≫ b))
      (pullback.snd p₀ b) c := by
  have hout : IsPullback (baseMap p₀ b c ≫ pullback.fst p₀ b)
      (pullback.snd p₀ (c ≫ b)) p₀ (c ≫ b) := by
    simpa only [baseMap_fst] using IsPullback.of_hasPullback p₀ (c ≫ b)
  exact hout.of_right (baseMap_snd p₀ b c) (IsPullback.of_hasPullback p₀ b)

/-- The actual second stage of the comparison for successive restrictions. -/
def step (f : X₁ ⟶ X₀) (p₀ : X₀ ⟶ B₀) (p₁ : X₁ ⟶ B₁)
    (b : B₁ ⟶ B₀) (c : B₂ ⟶ B₁) (h : f ≫ p₀ = p₁ ≫ b) :
    pullback p₁ c ⟶ pullback p₀ (c ≫ b) :=
  pullback.lift (pullback.fst p₁ c ≫ f) (pullback.snd p₁ c) (by
    rw [Category.assoc, h, ← Category.assoc, pullback.condition, Category.assoc])

@[reassoc (attr := simp)]
theorem step_fst (f : X₁ ⟶ X₀) (p₀ : X₀ ⟶ B₀) (p₁ : X₁ ⟶ B₁)
    (b : B₁ ⟶ B₀) (c : B₂ ⟶ B₁) (h : f ≫ p₀ = p₁ ≫ b) :
    step f p₀ p₁ b c h ≫ pullback.fst p₀ (c ≫ b) = pullback.fst p₁ c ≫ f := by
  simp [step]

@[reassoc (attr := simp)]
theorem step_snd (f : X₁ ⟶ X₀) (p₀ : X₀ ⟶ B₀) (p₁ : X₁ ⟶ B₁)
    (b : B₁ ⟶ B₀) (c : B₂ ⟶ B₁) (h : f ≫ p₀ = p₁ ≫ b) :
    step f p₀ p₁ b c h ≫ pullback.snd p₀ (c ≫ b) = pullback.snd p₁ c := by
  simp [step]

/-- The second stage is a literal pullback of the first comparison. -/
theorem step_isPullback (f : X₁ ⟶ X₀) (p₀ : X₀ ⟶ B₀) (p₁ : X₁ ⟶ B₁)
    (b : B₁ ⟶ B₀) (c : B₂ ⟶ B₁) (h : f ≫ p₀ = p₁ ≫ b) :
    IsPullback (pullback.fst p₁ c) (step f p₀ p₁ b c h)
      (comparison f p₀ p₁ b h) (baseMap p₀ b c) := by
  have hout : IsPullback (pullback.fst p₁ c)
      (step f p₀ p₁ b c h ≫ pullback.snd p₀ (c ≫ b))
      (comparison f p₀ p₁ b h ≫ pullback.snd p₀ b) c := by
    simpa only [step_snd, comparison_snd] using IsPullback.of_hasPullback p₁ c
  have hcomm : pullback.fst p₁ c ≫ comparison f p₀ p₁ b h =
      step f p₀ p₁ b c h ≫ baseMap p₀ b c := by
    apply pullback.hom_ext <;> simp [Category.assoc, pullback.condition]
  exact hout.of_bot hcomm (baseMap_isPullback p₀ b c)

/-- Pasting gives exactly the comparison for the composite restrictions. -/
theorem comparison_comp_step (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁)
    (p₀ : X₀ ⟶ B₀) (p₁ : X₁ ⟶ B₁) (p₂ : X₂ ⟶ B₂)
    (b : B₁ ⟶ B₀) (c : B₂ ⟶ B₁)
    (hf : f ≫ p₀ = p₁ ≫ b) (hg : g ≫ p₁ = p₂ ≫ c) :
    comparison g p₁ p₂ c hg ≫ step f p₀ p₁ b c hf =
      comparison (g ≫ f) p₀ p₂ (c ≫ b) (by
        rw [Category.assoc, hf, ← Category.assoc, hg, Category.assoc]) := by
  apply pullback.hom_ext <;> simp [Category.assoc, pullback.condition]

/-- A boundary-trivial first comparison makes total and second comparison lifting equivalent. -/
theorem rlp_I_total_iff_second (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁)
    (p₀ : X₀ ⟶ B₀) (p₁ : X₁ ⟶ B₁) (p₂ : X₂ ⟶ B₂)
    (b : B₁ ⟶ B₀) (c : B₂ ⟶ B₁)
    (hf : f ≫ p₀ = p₁ ≫ b) (hg : g ≫ p₁ = p₂ ≫ c)
    (hfirst : modelCategoryQuillen.I.rlp (comparison f p₀ p₁ b hf))
    (hsecond : categoricalFibrations (comparison g p₁ p₂ c hg)) :
    modelCategoryQuillen.I.rlp
      (comparison (g ≫ f) p₀ p₂ (c ≫ b) (by
        rw [Category.assoc, hf, ← Category.assoc, hg, Category.assoc])) ↔
      modelCategoryQuillen.I.rlp (comparison g p₁ p₂ c hg) := by
  rw [← comparison_comp_step f g p₀ p₁ p₂ b c hf hg]
  apply rlp_I_comp_iff_of_postcomp _ _ hsecond
  exact IsStableUnderBaseChange.of_isPullback (step_isPullback f p₀ p₁ b c hf) hfirst

/-- Trivial second comparison and base restriction detect the first comparison. -/
theorem rlp_I_total_iff_first (f : X₁ ⟶ X₀) (g : X₂ ⟶ X₁)
    (p₀ : X₀ ⟶ B₀) (p₁ : X₁ ⟶ B₁) (p₂ : X₂ ⟶ B₂)
    (b : B₁ ⟶ B₀) (c : B₂ ⟶ B₁)
    (hf : f ≫ p₀ = p₁ ≫ b) (hg : g ≫ p₁ = p₂ ≫ c)
    (hfirst : categoricalFibrations (comparison f p₀ p₁ b hf))
    (hsecond : modelCategoryQuillen.I.rlp (comparison g p₁ p₂ c hg))
    (hbase : modelCategoryQuillen.I.rlp c) :
    modelCategoryQuillen.I.rlp
      (comparison (g ≫ f) p₀ p₂ (c ≫ b) (by
        rw [Category.assoc, hf, ← Category.assoc, hg, Category.assoc])) ↔
      modelCategoryQuillen.I.rlp (comparison f p₀ p₁ b hf) := by
  rw [← comparison_comp_step f g p₀ p₁ p₂ b c hf hg]
  have hstep : categoricalFibrations (step f p₀ p₁ b c hf) :=
    IsStableUnderBaseChange.of_isPullback (step_isPullback f p₀ p₁ b c hf) hfirst
  rw [rlp_I_comp_iff_of_precomp _ _ hsecond hstep]
  apply rlp_I_iff_of_trivial_baseChange (step_isPullback f p₀ p₁ b c hf) hfirst
  exact IsStableUnderBaseChange.of_isPullback (baseMap_isPullback p₀ b c).flip hbase

end SSet.RelativePullback
