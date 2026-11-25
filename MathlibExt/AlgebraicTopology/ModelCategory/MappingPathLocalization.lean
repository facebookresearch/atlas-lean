/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.MappingPath
import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy
import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Mapping-path choices in the actual localization

A section of the far endpoint gives its original source map an actual
right-inverse homotopy. Any functor inverting the path unit sends that
homotopy to equality. If the original arrow is weak, its localized inverse
determines the source map independently of the chosen path and section.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra.MappingPath

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The retained original path supplies the right-inverse homotopy of any endpoint section. -/
def sectionHomotopy {X Y : C} (f : X ⟶ Y) (P : PrepathObject Y)
    (s : Y ⟶ Object f P) (hs : s ≫ target f P = 𝟙 Y) :
    P.RightHomotopy ((s ≫ source f P) ≫ f) (𝟙 Y) where
  h := s ≫ path f P
  h₀ := by rw [Category.assoc, path_start, Category.assoc]
  h₁ := by
    rw [Category.assoc]
    exact hs

section Localization

variable [CategoryWithWeakEquivalences C] {E : Type w} [Category.{t} E]
    (Q : C ⥤ E) (hQ : (weakEquivalences C).IsInvertedBy Q)

include hQ

/-- A true path unit forces the original section's right-inverse law after localization. -/
theorem section_source_rightInverse {X Y : C} (f : X ⟶ Y) (P : PathObject Y)
    (s : Y ⟶ Object f P.toPrepathObject)
    (hs : s ≫ target f P.toPrepathObject = 𝟙 Y) :
    Q.map (s ≫ source f P.toPrepathObject) ≫ Q.map f = 𝟙 (Q.obj Y) := by
  let _ : IsIso (Q.map P.ι) := hQ P.ι ((weakEquivalence_iff P.ι).mp inferInstance)
  have endpoints : Q.map P.p₀ = Q.map P.p₁ := by
    apply (cancel_epi (Q.map P.ι)).mp
    simp only [← Q.map_comp, P.ι_p₀, P.ι_p₁]
  let h := sectionHomotopy f P.toPrepathObject s hs
  calc
    Q.map (s ≫ source f P.toPrepathObject) ≫ Q.map f =
        Q.map ((s ≫ source f P.toPrepathObject) ≫ f) := (Q.map_comp _ _).symm
    _ = Q.map (h.h ≫ P.p₀) := congrArg Q.map h.h₀.symm
    _ = Q.map h.h ≫ Q.map P.p₀ := Q.map_comp _ _
    _ = Q.map h.h ≫ Q.map P.p₁ := by rw [endpoints]
    _ = Q.map (h.h ≫ P.p₁) := (Q.map_comp _ _).symm
    _ = Q.map (𝟙 Y) := congrArg Q.map h.h₁
    _ = 𝟙 (Q.obj Y) := Q.map_id Y

/-- The section's original source is exactly the inverse of the same localized weak arrow. -/
theorem section_source_eq_inverse {X Y : C} (f : X ⟶ Y) [WeakEquivalence f]
    (P : PathObject Y) (s : Y ⟶ Object f P.toPrepathObject)
    (hs : s ≫ target f P.toPrepathObject = 𝟙 Y) :
    let _ : IsIso (Q.map f) := hQ f ((weakEquivalence_iff f).mp inferInstance)
    Q.map (s ≫ source f P.toPrepathObject) = inv (Q.map f) := by
  dsimp only
  let _ : IsIso (Q.map f) := hQ f ((weakEquivalence_iff f).mp inferInstance)
  apply (cancel_mono (Q.map f)).mp
  rw [section_source_rightInverse Q hQ f P s hs, IsIso.inv_hom_id]

/-- Two allowed original path objects and endpoint sections give the same localized source map. -/
theorem section_source_choice_invariant {X Y : C} (f : X ⟶ Y) [WeakEquivalence f]
    (P P' : PathObject Y)
    (s : Y ⟶ Object f P.toPrepathObject) (s' : Y ⟶ Object f P'.toPrepathObject)
    (hs : s ≫ target f P.toPrepathObject = 𝟙 Y)
    (hs' : s' ≫ target f P'.toPrepathObject = 𝟙 Y) :
    Q.map (s ≫ source f P.toPrepathObject) = Q.map (s' ≫ source f P'.toPrepathObject) :=
  (section_source_eq_inverse Q hQ f P s hs).trans
    (section_source_eq_inverse Q hQ f P' s' hs').symm

end Localization

section Model

variable [ModelCategory C]

/-- The same localized inverse gives a genuine homotopy between the two original source maps. -/
theorem section_sources_rightHomotopic {X Y : C} [IsCofibrant Y] [IsFibrant X]
    (f : X ⟶ Y) [WeakEquivalence f] (P P' : PathObject Y)
    (s : Y ⟶ Object f P.toPrepathObject) (s' : Y ⟶ Object f P'.toPrepathObject)
    (hs : s ≫ target f P.toPrepathObject = 𝟙 Y)
    (hs' : s' ≫ target f P'.toPrepathObject = 𝟙 Y) :
    RightHomotopyRel (s ≫ source f P.toPrepathObject) (s' ≫ source f P'.toPrepathObject) := by
  let Q := (weakEquivalences C).Q
  apply (RightHomotopyRel.iff_map_eq Q Y X).mpr
  exact section_source_choice_invariant Q (Localization.inverts Q (weakEquivalences C))
    f P P' s s' hs hs'

/-- Any given good original source path object realizes the complete section-choice homotopy. -/
def sectionSourceHomotopy {X Y : C} [IsCofibrant Y] [IsFibrant X]
    (f : X ⟶ Y) [WeakEquivalence f] (P P' : PathObject Y)
    (s : Y ⟶ Object f P.toPrepathObject) (s' : Y ⟶ Object f P'.toPrepathObject)
    (hs : s ≫ target f P.toPrepathObject = 𝟙 Y)
    (hs' : s' ≫ target f P'.toPrepathObject = 𝟙 Y) (R : PathObject X) [R.IsGood] :
    R.RightHomotopy (s ≫ source f P.toPrepathObject) (s' ≫ source f P'.toPrepathObject) := by
  let hrel := section_sources_rightHomotopic f P P' s s' hs hs'
  let hp := hrel.exists_very_good_pathObject
  let P'' : PathObject X := hp.choose
  let _ : P''.IsVeryGood := hp.choose_spec.1
  let h : P''.RightHomotopy (s ≫ source f P.toPrepathObject)
      (s' ≫ source f P'.toPrepathObject) := Classical.choice hp.choose_spec.2
  let _ : HasLiftingProperty P''.ι R.p := inferInstance
  let sq : CommSq R.ι P''.ι R.p P''.p := ⟨by
    apply prod.hom_ext <;> simp [Category.assoc]⟩
  have first : sq.lift ≫ R.p₀ = P''.p₀ := by
    simpa only [Category.assoc, PrepathObject.p_fst] using
      congrArg (fun k => k ≫ prod.fst) sq.fac_right
  have second : sq.lift ≫ R.p₁ = P''.p₁ := by
    simpa only [Category.assoc, PrepathObject.p_snd] using
      congrArg (fun k => k ≫ prod.snd) sq.fac_right
  refine ⟨h.h ≫ sq.lift, ?_, ?_⟩
  · rw [Category.assoc, first]
    exact h.h₀
  · rw [Category.assoc, second]
    exact h.h₁

end Model

end HomotopicalAlgebra.MappingPath
