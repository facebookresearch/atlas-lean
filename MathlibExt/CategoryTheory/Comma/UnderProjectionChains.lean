/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Entire native undercategory chains over arbitrary original words

A full native chain over an arbitrary original base word is determined
by its SAME first original arrow. The actual arrows at every later vertex
are the original composites, including all nonidentity base arrows.
The complete native precomposition and postcomposition formulas retain
every ordinal restriction and every original functor map.
-/

noncomputable section
universe u v u' v'
open CategoryTheory

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C] {X : C} {n m : ℕ}

/-- An entire original undercategory word from its SAME first arrow and full base chain. -/
def chainFromInitialArrow (F : Fin (n + 1) ⥤ C) (e : X ⟶ F.obj 0) :
    Fin (n + 1) ⥤ Under X where
  obj i := Under.mk (e ≫ F.map (homOfLE (Fin.zero_le i)))
  map {i j} f := Under.homMk (F.map f) (by
    change (e ≫ F.map (homOfLE (Fin.zero_le i))) ≫ F.map f = e ≫ F.map (homOfLE (Fin.zero_le j))
    rw [Category.assoc, ← F.map_comp]
    exact congrArg (fun g => e ≫ F.map g) (Subsingleton.elim _ _))
  map_id i := by
    apply Under.UnderMorphism.ext
    exact F.map_id i
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact F.map_comp f g

/-- Every original under-object is the SAME first arrow followed by its whole original base
arrow. -/
theorem chainFromInitialArrow_obj (F : Fin (n + 1) ⥤ C) (e : X ⟶ F.obj 0) (i : Fin (n + 1)) :
    (chainFromInitialArrow F e).obj i = Under.mk (e ≫ F.map (homOfLE (Fin.zero_le i))) := rfl

/-- Every full native original target object is literally the supplied base object. -/
theorem chainFromInitialArrow_right (F : Fin (n + 1) ⥤ C) (e : X ⟶ F.obj 0) (i : Fin (n + 1)) :
    ((chainFromInitialArrow F e).obj i).right = F.obj i := rfl

/-- Every full native original under-arrow has precisely the supplied original base coefficient. -/
theorem chainFromInitialArrow_map (F : Fin (n + 1) ⥤ C) (e : X ⟶ F.obj 0)
    {i j : Fin (n + 1)} (f : i ⟶ j) : ((chainFromInitialArrow F e).map f).right = F.map f := rfl

/-- The whole native forgetful projection retains the exact original base word. -/
theorem chainFromInitialArrow_forget (F : Fin (n + 1) ⥤ C) (e : X ⟶ F.obj 0) :
    chainFromInitialArrow F e ⋙ Under.forget X = F :=
  Functor.hext (fun _ => rfl) (fun _ _ _ => HEq.rfl)

/-- The actual first original arrow, transported only by its proved original target equality. -/
def projectionInitialArrow (U : Fin (n + 1) ⥤ Under X) (F : Fin (n + 1) ⥤ C)
    (h : U ⋙ Under.forget X = F) : X ⟶ F.obj 0 :=
  (U.obj 0).hom ≫ eqToHom (Functor.congr_obj h 0)

/-- Every actual original under-object over the full base word is the composite
of the SAME original first arrow with the SAME entire base map. -/
theorem projectionChain_obj (U : Fin (n + 1) ⥤ Under X) (F : Fin (n + 1) ⥤ C)
    (h : U ⋙ Under.forget X = F) (i : Fin (n + 1)) :
    U.obj i = (chainFromInitialArrow F (projectionInitialArrow U F h)).obj i := by
  let hi := Functor.congr_obj h i
  let h₀ := Functor.congr_obj h 0
  let k := U.map (homOfLE (Fin.zero_le i))
  have hk : k.right ≫ eqToHom hi = eqToHom h₀ ≫ F.map (homOfLE (Fin.zero_le i)) := by
    have he := Functor.congr_hom h (homOfLE (Fin.zero_le i))
    change k.right = eqToHom h₀ ≫ F.map (homOfLE (Fin.zero_le i)) ≫ eqToHom hi.symm at he
    exact (congrArg (fun a => a ≫ eqToHom hi) he).trans (by simp)
  apply StructuredArrow.obj_ext (U.obj i) ((chainFromInitialArrow F (projectionInitialArrow
    U F h)).obj i) hi
  change (U.obj i).hom ≫ eqToHom hi = projectionInitialArrow U F h ≫ F.map (homOfLE (Fin.zero_le i))
  exact (congrArg (fun a => a ≫ eqToHom hi) k.w).symm.trans
    ((Category.assoc _ _ _).trans ((congrArg (fun a => (U.obj 0).hom ≫ a) hk).trans
      (Category.assoc _ _ _).symm))

/-- The SAME entire original native undercategory chain is reconstructed from
its first arrow and the complete original base word. -/
theorem projectionChain (U : Fin (n + 1) ⥤ Under X) (F : Fin (n + 1) ⥤ C)
    (h : U ⋙ Under.forget X = F) :
    U = chainFromInitialArrow F (projectionInitialArrow U F h) := by
  refine Functor.ext (F := U) (G := chainFromInitialArrow F (projectionInitialArrow U F h))
    (projectionChain_obj U F h) ?_
  intro i j f
  apply Under.UnderMorphism.ext
  simpa only [Under.comp_right, Under.eqToHom_right, Under.forget_obj, Under.forget_map,
    Functor.comp_map, Functor.comp_obj, chainFromInitialArrow_map, chainFromInitialArrow_right]
    using Functor.congr_hom h f

/-- All full lifts of the SAME original word are exactly its original initial arrows. -/
theorem projection_eq_iff (U : Fin (n + 1) ⥤ Under X) (F : Fin (n + 1) ⥤ C) :
    U ⋙ Under.forget X = F ↔ ∃ e : X ⟶ F.obj 0, chainFromInitialArrow F e = U := by
  constructor
  · intro h
    exact ⟨projectionInitialArrow U F h, (projectionChain U F h).symm⟩
  · rintro ⟨e, rfl⟩
    exact chainFromInitialArrow_forget F e

/-- The SAME original first arrow is recovered from the entire lifted word. -/
theorem chainFromInitialArrow_zero (F : Fin (n + 1) ⥤ C) (e : X ⟶ F.obj 0) :
    ((chainFromInitialArrow F e).obj 0).hom = e := by
  change e ≫ F.map (homOfLE (Fin.zero_le (0 : Fin (n + 1)))) = e
  have h : homOfLE (Fin.zero_le (0 : Fin (n + 1))) = 𝟙 (0 : Fin (n + 1)) := Subsingleton.elim _ _
  rw [h, F.map_id, Category.comp_id]

/-- Every original first arrow is uniquely retained by its complete native word. -/
theorem chainFromInitialArrow_injective (F : Fin (n + 1) ⥤ C) :
    Function.Injective (chainFromInitialArrow (X := X) F) := by
  intro e e' h
  have ho := Functor.congr_obj h 0
  change Under.mk (e ≫ F.map (homOfLE (Fin.zero_le (0 : Fin (n + 1))))) =
    Under.mk (e' ≫ F.map (homOfLE (Fin.zero_le (0 : Fin (n + 1))))) at ho
  have hc : e ≫ F.map (homOfLE (Fin.zero_le (0 : Fin (n + 1)))) =
      e' ≫ F.map (homOfLE (Fin.zero_le (0 : Fin (n + 1)))) := by injection ho
  have hId : F.map (homOfLE (Fin.zero_le (0 : Fin (n + 1)))) = 𝟙 (F.obj 0) :=
    (congrArg F.map (Subsingleton.elim _ (𝟙 (0 : Fin (n + 1))))).trans (F.map_id 0)
  simpa only [hId, Category.comp_id] using hc

/-- Every full ordinal restriction retains the SAME first-arrow transport along
the exact original base edge selected by that restriction. -/
theorem chainFromInitialArrow_precomp (F : Fin (n + 1) ⥤ C) (e : X ⟶ F.obj 0)
    (a : Fin (m + 1) ⥤ Fin (n + 1)) :
    a ⋙ chainFromInitialArrow F e =
      chainFromInitialArrow (a ⋙ F) (e ≫ F.map (homOfLE (Fin.zero_le (a.obj 0)))) := by
  have obj (i : Fin (m + 1)) : (a ⋙ chainFromInitialArrow F e).obj i =
      (chainFromInitialArrow (a ⋙ F) (e ≫ F.map (homOfLE (Fin.zero_le (a.obj 0))))).obj i := by
    apply StructuredArrow.obj_ext ((a ⋙ chainFromInitialArrow F e).obj i)
      ((chainFromInitialArrow (a ⋙ F) (e ≫ F.map (homOfLE (Fin.zero_le (a.obj 0))))).obj i) rfl
    change (e ≫ F.map (homOfLE (Fin.zero_le (a.obj i)))) ≫ eqToHom rfl =
      (e ≫ F.map (homOfLE (Fin.zero_le (a.obj 0)))) ≫ F.map (a.map (homOfLE (Fin.zero_le i)))
    rw [eqToHom_refl, Category.comp_id, Category.assoc, ← F.map_comp]
    exact congrArg (fun f => e ≫ F.map f) (Subsingleton.elim _ _)
  refine Functor.ext obj ?_
  intro i j f
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right, Functor.comp_map, chainFromInitialArrow_map]
  change F.map (a.map f) = eqToHom (rfl : F.obj (a.obj i) = F.obj (a.obj i)) ≫
    F.map (a.map f) ≫ eqToHom (rfl : F.obj (a.obj j) = F.obj (a.obj j))
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- Every actual target functor preserves the complete original word and its
SAME first arrow, with independent category object and Hom universes. -/
theorem chainFromInitialArrow_post {D : Type u'} [Category.{v'} D]
    (F : Fin (n + 1) ⥤ C) (e : X ⟶ F.obj 0) (G : C ⥤ D) :
    chainFromInitialArrow F e ⋙ Under.post G = chainFromInitialArrow (F ⋙ G) (G.map e) := by
  have obj (i : Fin (n + 1)) : (chainFromInitialArrow F e ⋙ Under.post G).obj i =
      (chainFromInitialArrow (F ⋙ G) (G.map e)).obj i := by
    apply StructuredArrow.obj_ext ((chainFromInitialArrow F e ⋙ Under.post G).obj i)
      ((chainFromInitialArrow (F ⋙ G) (G.map e)).obj i) rfl
    change G.map (e ≫ F.map (homOfLE (Fin.zero_le i))) ≫ eqToHom rfl =
      G.map e ≫ G.map (F.map (homOfLE (Fin.zero_le i)))
    rw [eqToHom_refl, Category.comp_id, G.map_comp]
  refine Functor.ext obj ?_
  intro i j f
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, Under.eqToHom_right]
  change G.map (F.map f) = eqToHom (rfl : G.obj (F.obj i) = G.obj (F.obj i)) ≫
    G.map (F.map f) ≫ eqToHom (rfl : G.obj (F.obj j) = G.obj (F.obj j))
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

end CategoryTheory.Under
