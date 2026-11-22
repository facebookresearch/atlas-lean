/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningOriginalHomotopyClasses
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeWeakClassComparison
import Mathlib.AlgebraicTopology.ModelCategory.FibrantObjectHomotopy

/-!
# Original coherent-model weakness and actual fibrant homotopy tests

The original coherent model has the actual coefficient weak class.
Every coefficient retains its unchanged marked point-slice projection.
The full original relative homotopy tests detect that same coefficient
weakness. Bijectivity of both full composite tests therefore reflects
weakness to each original component, without a supplied saturated class
or a model-fibration-class comparison.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

private theorem coefficientWeakOfBothComposites {A D : Marked.{u}}
    (f : A ⟶ D) (g : D ⟶ A)
    (hfg : WeakEquivalence (f ≫ g)) (hgf : WeakEquivalence (g ≫ f)) :
    WeakEquivalence f := by
  let B : SSet.{u} := Δ[0]
  let E := coefficientPointEquivalence.{u}.functor
  let P := relativeIntervalCylinder (max B)
  let a := E.map f
  let b := E.map g
  have hab := (weakEquivalence_iff (f ≫ g)).mp hfg
  have hba := (weakEquivalence_iff (g ≫ f)).mp hgf
  change cartesianWeakEquivalences B (E.map (f ≫ g)) at hab
  change cartesianWeakEquivalences B (E.map (g ≫ f)) at hba
  have hab' : cartesianWeakEquivalences B (a ≫ b) := (E.map_comp f g).symm ▸ hab
  have hba' : cartesianWeakEquivalences B (b ≫ a) := (E.map_comp g f).symm ▸ hba
  apply (weakEquivalence_iff f).mpr
  change cartesianWeakEquivalences B a
  rw [cartesianWeakEquivalences_eq_relativeHomotopyTesting B]
  apply (cartesianRelativeHomotopyTesting_iff a).mpr
  intro T hT
  have h₁ : Function.Bijective (P.homotopyClassPrecomp (a ≫ b) T) :=
    (cartesianRelativeHomotopyTesting_iff (a ≫ b)).mp
      (cartesianWeakEquivalences_le_relativeHomotopyTesting B _ hab') T hT
  have h₂ : Function.Bijective (P.homotopyClassPrecomp (b ≫ a) T) :=
    (cartesianRelativeHomotopyTesting_iff (b ≫ a)).mp
      (cartesianWeakEquivalences_le_relativeHomotopyTesting B _ hba') T hT
  constructor
  · intro x y h
    apply h₂.1
    change P.homotopyQuotientFunctor.map (b ≫ a) ≫ x =
      P.homotopyQuotientFunctor.map (b ≫ a) ≫ y
    rw [P.homotopyQuotientFunctor.map_comp b a, Category.assoc, Category.assoc]
    exact congrArg (fun t => P.homotopyQuotientFunctor.map b ≫ t) h
  · intro z
    obtain ⟨x, hx⟩ := h₁.2 z
    refine ⟨P.homotopyQuotientFunctor.map b ≫ x, ?_⟩
    change P.homotopyQuotientFunctor.map a ≫ (P.homotopyQuotientFunctor.map b ≫ x) = z
    exact (Category.assoc (P.homotopyQuotientFunctor.map a)
      (P.homotopyQuotientFunctor.map b) x).symm.trans
        ((congrArg (fun t => t ≫ x) (P.homotopyQuotientFunctor.map_comp a b).symm).trans hx)

/-- The actual original coherent coefficient weak class reflects weakness from both entire composite maps, by the
original point-slice homotopy tests at every coefficient. -/
theorem nativeCoherentWeakOfBothComposites (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) (r : G ⟶ F) :
    let _ := coherentDiagramModelCategory B
    WeakEquivalence (q ≫ r) → WeakEquivalence (r ≫ q) → WeakEquivalence q := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hqr hrq
  have h₁ := (weakEquivalence_iff (q ≫ r)).mp hqr
  have h₂ := (weakEquivalence_iff (r ≫ q)).mp hrq
  change coherentDiagramWeakEquivalences B (q ≫ r) at h₁
  change coherentDiagramWeakEquivalences B (r ≫ q) at h₂
  let evs := fun c : (realization B)ᵒᵖ => enrichedDiagramEvaluation _ c
  have h₁' := (EvaluationTransfer.evaluationProperty_iff evs (weakEquivalences Marked.{u}) (q ≫ r)).mp h₁
  have h₂' := (EvaluationTransfer.evaluationProperty_iff evs (weakEquivalences Marked.{u}) (r ≫ q)).mp h₂
  apply (weakEquivalence_iff q).mpr
  change coherentDiagramWeakEquivalences B q
  apply (EvaluationTransfer.evaluationProperty_iff evs (weakEquivalences Marked.{u}) q).mpr
  intro c
  exact (weakEquivalence_iff (q.app c)).mp
    (coefficientWeakOfBothComposites (q.app c) (r.app c)
      ((weakEquivalence_iff _).mpr (h₁' c)) ((weakEquivalence_iff _).mpr (h₂' c)))

/-- Every original coherent arrow between actual cofibrant objects is weak when its actual right homotopy classes
test bijectively into every actual fibrant coherent diagram. The proof keeps the whole original resolution square
and uses original coefficient weak tests. -/
theorem nativeCoherentFibrantHomotopyTesting_weak (B : SSet.{u})
    {X Y : EnrichedDiagram (realization B)ᵒᵖ} (f : X ⟶ Y) :
    let _ := coherentDiagramModelCategory B
    IsCofibrant X → IsCofibrant Y →
      (∀ F : EnrichedDiagram (realization B)ᵒᵖ, IsFibrant F →
        Function.Bijective (fun c : RightHomotopyClass Y F => c.precomp f)) →
          WeakEquivalence f := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hX hY htest
  let _ : IsCofibrant X := hX
  let _ : IsCofibrant Y := hY
  let X' := FibrantObject.HoCat.resolutionObj X
  let Y' := FibrantObject.HoCat.resolutionObj Y
  let iX : X ⟶ X' := FibrantObject.HoCat.iResolutionObj X
  let iY : Y ⟶ Y' := FibrantObject.HoCat.iResolutionObj Y
  let f' : X' ⟶ Y' := FibrantObject.HoCat.resolutionMap f
  have hfac : iX ≫ f' = f ≫ iY := FibrantObject.HoCat.resolutionMap_fac f
  have htest' : ∀ F : EnrichedDiagram (realization B)ᵒᵖ, IsFibrant F →
      Function.Bijective (fun c : RightHomotopyClass Y' F => c.precomp f') := by
    intro F hF
    let _ : IsFibrant F := hF
    have hix := RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence F iX
    have hiy := RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence F iY
    have hcomm (c : RightHomotopyClass Y' F) :
        (c.precomp f').precomp iX = (c.precomp iY).precomp f := by
      obtain ⟨g, rfl⟩ := RightHomotopyClass.mk_surjective c
      simp only [RightHomotopyClass.precomp_mk]
      exact congrArg RightHomotopyClass.mk
        ((Category.assoc iX f' g).symm.trans
          ((congrArg (fun t => t ≫ g) hfac).trans (Category.assoc f iY g)))
    constructor
    · intro a b hab
      apply hiy.1
      apply (htest F hF).1
      exact (hcomm a).symm.trans
        ((congrArg (fun t : RightHomotopyClass X' F => t.precomp iX) hab).trans (hcomm b))
    · intro c
      obtain ⟨d, hd⟩ := (htest F hF).2 (c.precomp iX)
      obtain ⟨a, ha⟩ := hiy.2 d
      refine ⟨a, hix.1 ?_⟩
      exact (hcomm a).trans ((congrArg (fun t : RightHomotopyClass Y F => t.precomp f) ha).trans hd)
  obtain ⟨k, hk⟩ := (htest' X' inferInstance).2 (RightHomotopyClass.mk (𝟙 X'))
  obtain ⟨k, rfl⟩ := RightHomotopyClass.mk_surjective k
  have h₀ : RightHomotopyRel (f' ≫ k) (𝟙 X') := (RightHomotopyClass.mk_eq_mk_iff _ _).mp hk
  have h₁ : RightHomotopyRel (k ≫ f') (𝟙 Y') := by
    apply (RightHomotopyClass.mk_eq_mk_iff _ _).mp
    apply (htest' Y' inferInstance).1
    simp only [RightHomotopyClass.precomp_mk, Category.comp_id]
    apply RightHomotopyClass.sound
    have hh := h₀.leftHomotopyRel.postcomp f'
    have hh' : LeftHomotopyRel (f' ≫ (k ≫ f')) f' := by
      simpa only [Category.assoc, Category.id_comp] using hh
    exact hh'.rightHomotopyRel
  have hweak₀ : WeakEquivalence (f' ≫ k) := by
    obtain ⟨P, ⟨H⟩⟩ := h₀.leftHomotopyRel
    exact H.weakEquivalence_iff.mpr (inferInstanceAs (WeakEquivalence (𝟙 X')))
  have hweak₁ : WeakEquivalence (k ≫ f') := by
    obtain ⟨P, ⟨H⟩⟩ := h₁.leftHomotopyRel
    exact H.weakEquivalence_iff.mpr (inferInstanceAs (WeakEquivalence (𝟙 Y')))
  have hf' : WeakEquivalence f' := nativeCoherentWeakOfBothComposites B f' k hweak₀ hweak₁
  exact (FibrantObject.HoCat.weakEquivalence_resolutionMap_iff f).mp hf'

end SSet.Marked
