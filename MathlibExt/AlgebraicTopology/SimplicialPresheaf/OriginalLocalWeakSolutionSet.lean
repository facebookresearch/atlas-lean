/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalWeakSubarrow
import Mathlib.CategoryTheory.Comma.LocallySmall
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems

/-!
# Strict solution sets for the original local weak arrows

The original bounded weak-subarrow theorem supplies one regular point/rank
budget before every ambient arrow. Public original bounded representatives
and native small-IN-property selection retain actual local weakness and both
endpoint bounds. Every original incoming Hom label is enumerated through its
working-universe equivalence, preserving strict whole-Arrow factorization.
-/

set_option autoImplicit false
noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits
open SimplicialPresheaf.KanWeakInterpolation

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

omit [Small.{u} I] in
/-- Select original representatives IN the actual weak/point/rank property.
The public all-point-bounded cover is used without an iso-stability premise
for the point-bound predicate or a private normalization helper. -/
private theorem existsBoundedLocalWeakRepresentatives
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (γ δ : Cardinal.{u}) [Fact δ.IsRegular] :
    ∃ (K : Type u) (R : K → Arrow (SimplicialPresheaf.{u} D)),
      (∀ k, originalLocalEquivalences S (R k).hom ∧
        originalArrowPointBound (D := D) γ (R k) ∧
        IsCardinalPresentable (R k).left δ ∧ IsCardinalPresentable (R k).right δ) ∧
      ∀ B : Arrow (SimplicialPresheaf.{u} D),
        originalLocalEquivalences S B.hom → originalArrowPointBound (D := D) γ B →
        IsCardinalPresentable B.left δ → IsCardinalPresentable B.right δ →
        ∃ k, Nonempty (B ≅ R k) := by
  let P : ObjectProperty (Arrow (SimplicialPresheaf.{u} D)) := fun B =>
    originalLocalEquivalences S B.hom ∧ originalArrowPointBound (D := D) γ B ∧
      IsCardinalPresentable B.left δ ∧ IsCardinalPresentable B.right δ
  obtain ⟨K₀, R₀, _, hcover₀⟩ := exists_originalArrowPointBound_representatives (D := D) γ
  let : ObjectProperty.EssentiallySmall.{u} P := by
    refine ⟨⟨ObjectProperty.ofObj R₀, inferInstance, ?_⟩⟩
    intro B hB
    obtain ⟨k, ⟨ek⟩⟩ := hcover₀ B hB.2.1
    exact ⟨R₀ k, ObjectProperty.ofObj_apply R₀ k, ⟨ek⟩⟩
  obtain ⟨Q, hQ, hQP, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  let _ := hQ
  obtain ⟨K, R, hR⟩ := ObjectProperty.Small.exists_eq_ofObj Q
  refine ⟨K, R, ?_, ?_⟩
  · intro k
    apply hQP
    rw [hR]
    exact ObjectProperty.ofObj_apply R k
  · intro B hw hb hL hRδ
    obtain ⟨B', hB', ⟨ek⟩⟩ := hPQ B ⟨hw, hb, hL, hRδ⟩
    rw [hR, ObjectProperty.ofObj_iff] at hB'
    obtain ⟨k, rfl⟩ := hB'
    exact ⟨k, ⟨ek⟩⟩

/-- A strict working-universe-small weakly initial family for EVERY original
incoming Arrow, with all original Hom labels, literal bounded subarrows, both
point bounds/ranks, and both strict component factor equations retained. -/
theorem originalLocalWeakArrowInterpolation
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (a : Arrow (SimplicialPresheaf.{u} D)) :
    ∃ (γ δ : Cardinal.{u}) (regularγ : Fact γ.IsRegular) (regularδ : Fact δ.IsRegular)
      (J : Type u) (F : J → Arrow (SimplicialPresheaf.{u} D))
      (incoming : ∀ j, a ⟶ F j),
      let _ := regularγ
      let _ := regularδ
      (originalLocalCellData S).κ < γ ∧ γ < δ ∧
      (∀ j, originalLocalEquivalences S (F j).hom ∧
        originalArrowPointBound (D := D) γ (F j) ∧
        IsCardinalPresentable (F j).left δ ∧ IsCardinalPresentable (F j).right δ) ∧
      ∀ {X Y : SimplicialPresheaf.{u} D} (f : X ⟶ Y),
        originalLocalEquivalences S f → ∀ β : a ⟶ Arrow.mk f,
        ∃ (j : J) (outgoing : F j ⟶ Arrow.mk f) (s : Subdiagram f)
          (e : F j ≅ Subdiagram.arrow f s),
          originalLocalEquivalences S (Subdiagram.hom f s) ∧
          originalArrowPointBound (D := D) γ (Subdiagram.arrow f s) ∧
          IsCardinalPresentable (Subdiagram.arrow f s).left δ ∧
          IsCardinalPresentable (Subdiagram.arrow f s).right δ ∧
          outgoing = e.hom ≫ Subdiagram.inclusion f s ∧
          incoming j ≫ outgoing = β ∧
          (incoming j).left ≫ outgoing.left = β.left ∧
          (incoming j).right ≫ outgoing.right = β.right := by
  let : LocallySmall.{u} (SimplicialPresheaf.{u} D) := SimplicialPresheaf.locallySmall
  let : LocallySmall.{u} (Arrow (SimplicialPresheaf.{u} D)) :=
    Comma.locallySmall (𝟭 (SimplicialPresheaf.{u} D)) (𝟭 (SimplicialPresheaf.{u} D))
  let d := originalLocalCellData S
  let : Fact d.κ.IsRegular := d.regular
  obtain ⟨γ, δ, regularγ, regularδ, _, _, hκ, hγδ, hwitness⟩ :=
    exists_originalLocalWeakSubarrow S a d.κ (le_refl _) 0
  let _ := regularγ
  let _ := regularδ
  obtain ⟨K, R, hR, hcover⟩ := existsBoundedLocalWeakRepresentatives S γ δ
  let J : Type u := Σ k : K, Shrink.{u} (a ⟶ R k)
  let F : J → Arrow (SimplicialPresheaf.{u} D) := fun j => R j.1
  let incoming : ∀ j : J, a ⟶ F j := fun j =>
    (equivShrink.{u} (a ⟶ R j.1)).symm j.2
  refine ⟨γ, δ, regularγ, regularδ, J, F, incoming, hκ, hγδ,
    fun j => hR j.1, ?_⟩
  intro X Y f hf β
  obtain ⟨s, α, hs, hL, hRγ, hLδ, hRδ, hwhole, _, _⟩ := hwitness f hf β
  obtain ⟨k, ⟨ek⟩⟩ := hcover (Subdiagram.arrow f s) hs ⟨hL, hRγ⟩ hLδ hRδ
  let label : a ⟶ R k := α ≫ ek.hom
  let j : J := ⟨k, equivShrink.{u} (a ⟶ R k) label⟩
  let e : F j ≅ Subdiagram.arrow f s := ek.symm
  let outgoing : F j ⟶ Arrow.mk f := e.hom ≫ Subdiagram.inclusion f s
  have hin : incoming j = label := by
    dsimp only [incoming, j]
    exact Equiv.symm_apply_apply _ _
  have hfactor : incoming j ≫ outgoing = β := by
    rw [hin]
    change (α ≫ ek.hom) ≫ (ek.inv ≫ Subdiagram.inclusion f s) = β
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hwhole
  exact ⟨j, outgoing, s, e, hs, ⟨hL, hRγ⟩, hLδ, hRδ, rfl, hfactor,
    congrArg Arrow.Hom.left hfactor, congrArg Arrow.Hom.right hfactor⟩

/-- The ACTUAL original weak-Arrow inclusion satisfies the native all-object
strict solution-set condition. Its evaluation at each original generator is
exactly the solution_set field required by Smith recognition. -/
theorem originalLocalWeakArrowInclusion_solutionSetCondition
    (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    SolutionSetCondition.{u} (originalLocalEquivalences S).arrowObjectProperty.ι := by
  intro a
  obtain ⟨γ, δ, regularγ, regularδ, J, F, incoming, _, _, hF, hfactor⟩ :=
    originalLocalWeakArrowInterpolation S a
  let _ := regularγ
  let _ := regularδ
  let X : J → (originalLocalEquivalences S).arrowObjectProperty.FullSubcategory :=
    fun j => ⟨F j, (hF j).1⟩
  refine ⟨J, X, incoming, ?_⟩
  intro Y h
  obtain ⟨j, outgoing, _, _, _, _, _, _, _, hwhole, _, _⟩ :=
    hfactor Y.obj.hom Y.property h
  exact ⟨j, ObjectProperty.homMk outgoing, hwhole⟩

end SimplicialPresheaf.InjectiveKan
