/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSuspensionForward
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSuspensionUnits

/-!
# Actual enriched suspension functors of original Hom maps

A supplied original simplicial map into one enriched Hom extends to a
genuine enriched functor from its free two-object suspension. The actual
free universal property gives every original path map and both whole
inverse readbacks. Object labels and original cells are retained.
-/

noncomputable section
universe u v
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.CoherentRealization.HomSuspensionFunctor
open SimplicialEnrichment SimplicialQuiver HomSuspensionGenerators
variable (K : SSet.{u}) (C : Type v) (x y : C)

/-- The supplied original source and target as the two actual suspension object images. -/
def objectMap (a : Objects.{u}) : C := if a = left then x else y

/-- The original source object label is sent to the supplied individual target source. -/
theorem objectMap_left : objectMap.{u, v} C x y left = x := by simp only [objectMap, ite_true]

/-- The original right object label is sent to the supplied individual target target. -/
theorem objectMap_right : objectMap.{u, v} C x y right = y := by
  simp only [objectMap, ite_eq_right left_ne_right.symm]

variable [EnrichedCategory SSet.{u} C]

/-- Interpret the sole original simplicial generator by the supplied actual Hom map. -/
def interpretation (f : K ⟶ (x ⟶[SSet.{u}] y)) : Interpretation (quiver K) C where
  obj := objectMap.{u, v} C x y
  map a b := by
    classical
    by_cases h : a = left ∧ b = right
    · obtain ⟨rfl, rfl⟩ := h
      exact eqToHom (quiver_forward K) ≫ f ≫
        eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (objectMap_left.{u, v} C x y).symm
          (objectMap_right.{u, v} C x y).symm)
    · exact {
        app n := ↾fun a => False.elim (h (generator_endpoints K a))
        naturality n m θ := by ext a; exact False.elim (h (generator_endpoints K a)) }

/-- The actual enriched functor extending the supplied original simplicial Hom map and
object labels. -/
def functor (f : K ⟶ (x ⟶[SSet.{u}] y)) : EnrichedFunctor SSet.{u} (carrier K) C :=
  (interpretation K C x y f).extend

/-- The genuine suspension functor keeps the supplied individual original source image. -/
theorem functor_left (f : K ⟶ (x ⟶[SSet.{u}] y)) : (functor K C x y f).obj left = x :=
  objectMap_left.{u, v} C x y

/-- The genuine suspension functor keeps the supplied individual original target image. -/
theorem functor_right (f : K ⟶ (x ⟶[SSet.{u}] y)) : (functor K C x y f).obj right = y :=
  objectMap_right.{u, v} C x y

/-- The entire original simplicial generating map is the actual Hom readback of the
suspension functor. -/
theorem generator_readback (f : K ⟶ (x ⟶[SSet.{u}] y)) :
    HomSuspensionForward.generator K ≫ (functor K C x y f).map left right ≫
      eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (functor_left K C x y f)
        (functor_right K C x y f)) = f := by
  have h := Interpretation.generator_eval (interpretation K C x y f) left right
  change (eqToHom _ ≫ SimplicialQuiver.generator (quiver K) left right) ≫ _ ≫ _ = _
  have hI : (interpretation K C x y f).map left right =
      eqToHom (quiver_forward K) ≫ f ≫
        eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (objectMap_left.{u, v} C x y).symm
          (objectMap_right.{u, v} C x y).symm) := by
    simp only [interpretation, and_self, dite_eq_left True.intro]
  let A := eqToHom (quiver_forward K).symm
  let B := SimplicialQuiver.generator (quiver K) left right
  let V := (functor K C x y f).map left right
  let E := eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (functor_left K C x y f)
    (functor_right K C x y f))
  let D := eqToHom (quiver_forward K)
  let E' := eqToHom (congrArg₂ (fun a b : C => a ⟶[SSet.{u}] b) (objectMap_left.{u, v} C x y).symm
    (objectMap_right.{u, v} C x y).symm)
  have hB : B ≫ V = D ≫ f ≫ E' := h.trans hI
  have hAD : A ≫ D = 𝟙 K := eqToHom_trans _ _
  have hEE : E' ≫ E = 𝟙 (x ⟶[SSet.{u}] y) := eqToHom_trans _ _
  change (A ≫ B) ≫ (V ≫ E) = f
  have hs₀ : (A ≫ B) ≫ (V ≫ E) = A ≫ ((B ≫ V) ≫ E) :=
    (Category.assoc A B _).trans (congrArg (fun t => A ≫ t) (Category.assoc B V E).symm)
  have hs₁ : A ≫ ((B ≫ V) ≫ E) = A ≫ ((D ≫ (f ≫ E')) ≫ E) := congrArg (fun t => A ≫ (t ≫ E)) hB
  have hs₂ : A ≫ ((D ≫ (f ≫ E')) ≫ E) = (A ≫ D) ≫ (f ≫ (E' ≫ E)) :=
    (congrArg (fun t => A ≫ t) (Category.assoc D (f ≫ E') E)).trans
      ((congrArg (fun t => A ≫ (D ≫ t)) (Category.assoc f E' E)).trans
        (Category.assoc A D (f ≫ (E' ≫ E))).symm)
  have hs₃ : (A ≫ D) ≫ (f ≫ (E' ≫ E)) = f := by
    exact (congrArg₂ (fun a e => a ≫ (f ≫ e)) hAD hEE).trans
      ((Category.id_comp _).trans (Category.comp_id f))
  exact hs₀.trans (hs₁.trans (hs₂.trans hs₃))

end CategoryTheory.CoherentRealization.HomSuspensionFunctor
