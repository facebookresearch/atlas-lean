/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwoEquivalence

/-!
# Degree-two stage equivalence consumer tests

Focused downstream checks for the public `stageTwoEquivalence` API through its
forward functor, functor-then-inverse roundtrip, and released equivalence counit
directly through `(stageTwoEquivalence C).counitIso`:
object orientation at `(0,1)`/`(0,2)`/`(1,2)`, diagonal zero transport, morphism
component orientation, recovery of the two generating maps, and stage-side
`(0,1)`/diagonal recovery. No projection restatement, no new API, simplicial
object, nerve, realization, weak equivalence, or K/G-theory definition.
-/

open CategoryTheory
open CategoryTheory.Limits
open ZeroObject
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageTwoEquivalenceTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Forward object orientation at `(0,1)`/`(0,2)`/`(1,2)`; catches swapped `X`/`Y`/`Z`. -/
example (S : CofiberSequenceCategory C) (h01 : (0 : Fin 3) ≤ 1)
    (h02 : (0 : Fin 3) ≤ 2) (h12 : (1 : Fin 3) ≤ 2) :
    ((stageTwoEquivalence C).functor.obj S).obj.obj (interval 0 1 h01) = S.obj.obj' 0 ∧
      ((stageTwoEquivalence C).functor.obj S).obj.obj (interval 0 2 h02) = S.obj.obj' 1 ∧
      ((stageTwoEquivalence C).functor.obj S).obj.obj (interval 1 2 h12) = S.obj.obj' 2 := by
  rw [stageTwoEquivalence_functor]
  exact ⟨stageTwoFunctor_obj_01 C S h01, stageTwoFunctor_obj_02 C S h02,
    stageTwoFunctor_obj_12 C S h12⟩

/-- Forward diagonal is the chosen zero; catches a non-zero diagonal transport. -/
example (S : CofiberSequenceCategory C) (i : Fin 3) :
    ((stageTwoEquivalence C).functor.obj S).obj.obj (diag i) = (Zero.zero : C) := by
  rw [stageTwoEquivalence_functor]
  exact stageTwoFunctor_obj_diag C S i

/-- Forward morphism components preserve orientation; catches swapped `app'` indices. -/
example {S T : CofiberSequenceCategory C} (φ : S ⟶ T) :
    ((stageTwoEquivalence C).functor.map φ).hom.app
        (interval (0 : Fin 3) 1 (by decide)) = ComposableArrows.app' φ.hom 0 ∧
      ((stageTwoEquivalence C).functor.map φ).hom.app
        (interval (0 : Fin 3) 2 (by decide)) = ComposableArrows.app' φ.hom 1 ∧
      ((stageTwoEquivalence C).functor.map φ).hom.app
        (interval (1 : Fin 3) 2 (by decide)) = ComposableArrows.app' φ.hom 2 := by
  show ((stageTwoFunctor C).map φ).hom.app
        (interval (0 : Fin 3) 1 (by decide)) = ComposableArrows.app' φ.hom 0 ∧
      ((stageTwoFunctor C).map φ).hom.app
        (interval (0 : Fin 3) 2 (by decide)) = ComposableArrows.app' φ.hom 1 ∧
      ((stageTwoFunctor C).map φ).hom.app
        (interval (1 : Fin 3) 2 (by decide)) = ComposableArrows.app' φ.hom 2
  exact ⟨stageTwoFunctor_map_01 C φ, stageTwoFunctor_map_02 C φ,
    stageTwoFunctor_map_12 C φ⟩

/-- Functor-then-inverse recovers the two generating maps;
    catches broken forward/inverse object wiring. -/
example (S : CofiberSequenceCategory C) :
    (((stageTwoEquivalence C).inverse.obj
      ((stageTwoEquivalence C).functor.obj S)).obj.map' 0 1) = S.obj.map' 0 1 ∧
    (((stageTwoEquivalence C).inverse.obj
      ((stageTwoEquivalence C).functor.obj S)).obj.map' 1 2) = S.obj.map' 1 2 := by
  show (((stageTwoFunctor C ⋙ stageTwoExtraction C).obj S).obj.map' 0 1) =
      S.obj.map' 0 1 ∧
    (((stageTwoFunctor C ⋙ stageTwoExtraction C).obj S).obj.map' 1 2) =
      S.obj.map' 1 2
  exact ⟨stageTwoRoundtrip_map01 C S, stageTwoRoundtrip_map12 C S⟩

/-- Stage-side counit component at `(0,1)` is the roundtrip identification;
    fails if counit wiring is broken. -/
example (A : Stage C 2) :
    (((stageTwoEquivalence C).counitIso.hom.app A).hom.app
        (interval (0 : Fin 3) 1 (by decide))) =
      eqToHom (stageTwoRoundtrip_obj_eq_01 C A) := by
  change (stageTwoCounitAppIso C A (interval (0 : Fin 3) 1 (by decide))).hom = _
  have hb : ¬ (interval (0 : Fin 3) 1 (by decide) : Ar 2).left =
      (interval (0 : Fin 3) 1 (by decide) : Ar 2).right := by decide
  have hb01 : (interval (0 : Fin 3) 1 (by decide) : Ar 2).left.val = 0 ∧
      (interval (0 : Fin 3) 1 (by decide) : Ar 2).right.val = 1 := ⟨rfl, rfl⟩
  simp only [stageTwoCounitAppIso, dite_eq_right hb, dite_eq_left hb01, eqToIso.hom]

/-- Stage-side counit component on diagonals factors through the zero identification;
    fails if counit wiring is broken. -/
example (A : Stage C 2) (i : Fin 3) :
    (((stageTwoEquivalence C).counitIso.hom.app A).hom.app (diag i)) =
      eqToHom (stageTwoRoundtrip_obj_eq_zero_of_diag C A (rfl : (diag i).left = (diag i).right)) ≫
        ((isZero_zero C).iso (A.property.diag_isZero i)).hom := by
  change (stageTwoCounitAppIso C A (diag i)).hom = _
  have hb : (diag i).left = (diag i).right := rfl
  simp only [stageTwoCounitAppIso, dite_eq_left hb, eqToIso.hom, Iso.trans_hom]

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageTwoEquivalenceTests
