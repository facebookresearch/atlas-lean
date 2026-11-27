/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>

import MathlibExt.Algebra.Category.Grp.FilteredInterleaving
import Mathlib.Algebra.Group.Int.Defs

/-!
Clients retain the original quotient representatives and both interleaving
transformations. The successor client also applies the construction to an
integer-doubling sequence whose stage maps are not isomorphisms.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open GrpCat.FilteredColimits GrpCat.FilteredColimits.Successor
open GrpCat.FilteredInterleaving

namespace GrpCat.FilteredInterleavingTests

section Caller

variable (D E : ℕ ⥤ GrpCat.{u})
  (a : ∀ n, D.obj n ⟶ E.obj n) (b : ∀ n, E.obj n ⟶ D.obj (n + 1))
  (ha : ∀ n, a n ≫ b n = step D n)
  (hb : ∀ n, b n ≫ a (n + 1) = step E n)

include ha hb

/-- A caller's literal natural transformation is the whole forward colimit map. -/
theorem caller_forward (α : D ⟶ E) (hα : ∀ n, α.app n = a n) :
    (colimitIso D E a b ha hb).hom = natQuotientColimit.map α :=
  colimitIso_hom_eq_colimitMap D E a b ha hb α hα

/-- The original quotient representative is recovered after both actual maps. -/
theorem quotient_roundtrip (n : ℕ) (x : E.obj n) :
    (colimitIso D E a b ha hb).hom
      (G.mk (F := D) ⟨n + 1, b n x⟩) = G.mk (F := E) ⟨n, x⟩ := by
  rw [← colimitIso_inv_mk D E a b ha hb n x]
  exact ConcreteCategory.congr_hom (colimitIso D E a b ha hb).inv_hom_id
    (G.mk (F := E) ⟨n, x⟩)

/-- The derived backward transformation retains every actual finite index map. -/
theorem caller_backward_naturality {i j : ℕ} (f : i ⟶ j) :
    E.map f ≫ b j = b i ≫ D.map (successorFunctor.map f) :=
  b_naturality D E a b ha hb f

/-- The whole backward transformation induces exactly the inverse colimit map. -/
theorem caller_inverse :
    (colimitIso D E a b ha hb).inv =
      natQuotientColimit.map (bNatTrans D E a b ha hb) ≫ (successorComparisonIso D).hom :=
  inverse_eq_colimitMap_comp_successor D E a b ha hb

end Caller

/-- Any sequence interleaves with its actual successor by its original transition and identity. -/
def successorInterleavingIso (D : ℕ ⥤ GrpCat.{u}) :
    GrpCat.FilteredColimits.colimit D ≅
      GrpCat.FilteredColimits.colimit (successorFunctor ⋙ D) :=
  colimitIso D (successorFunctor ⋙ D) (fun n => step D n)
    (fun n => 𝟙 (D.obj (n + 1)))
    (fun _ => Category.comp_id _)
    (fun n => by
      change 𝟙 _ ≫ step D (n + 1) = step D (n + 1)
      exact Category.id_comp _)

/-- This instance recovers the stock successor comparison's actual inverse map. -/
theorem successor_forward (D : ℕ ⥤ GrpCat.{u}) :
    (successorInterleavingIso D).hom =
      natQuotientColimit.map (successorTransitionNatTrans.app D) := by
  unfold successorInterleavingIso
  apply colimitIso_hom_eq_colimitMap
  exact successorTransitionNatTrans_app_app D

/-- Both full maps agree with the original cofinal successor comparison. -/
theorem successor_iso (D : ℕ ⥤ GrpCat.{u}) :
    successorInterleavingIso D = (successorComparisonIso D).symm := by
  apply Iso.ext
  exact (successor_forward D).trans (successorTransition_colimit_eq_inv D)

/-- The actual inverse retains every original successor cocone leg. -/
theorem successor_inverse_leg (D : ℕ ⥤ GrpCat.{u}) (n : ℕ) :
    (colimitCocone (successorFunctor ⋙ D)).ι.app n ≫
        (successorInterleavingIso D).inv = (colimitCocone D).ι.app (n + 1) := by
  rw [successor_iso]
  exact successorComparisonIso_hom_ι D n

/-- Doubling on the multiplicative form of the integers. -/
def doubleHom : Multiplicative ℤ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (2 * Multiplicative.toAdd x)
  map_one' := by simp
  map_mul' x y := by simp [mul_add]

/-- The literal sequence with integer groups and doubling at every stage. -/
def doubleDiagram : ℕ ⥤ GrpCat :=
  Functor.ofSequence (X := fun _ => GrpCat.of (Multiplicative ℤ))
    (fun _ => GrpCat.ofHom doubleHom)

/-- No original doubling stage map is surjective. -/
theorem double_step_not_surjective (n : ℕ) :
    ¬ Function.Surjective (step doubleDiagram n) := by
  intro h
  have hstep : step doubleDiagram n = GrpCat.ofHom doubleHom :=
    Functor.ofSequence_map_homOfLE_succ _ n
  rw [hstep] at h
  change Function.Surjective doubleHom at h
  obtain ⟨x, hx⟩ := h (Multiplicative.ofAdd 1)
  have hx' : (2 : ℤ) * Multiplicative.toAdd x = 1 := congrArg Multiplicative.toAdd hx
  omega

/-- The input stage maps really are not isomorphisms. -/
theorem double_step_not_isIso (n : ℕ) : ¬ IsIso (step doubleDiagram n) := by
  intro h
  let _ := h
  apply double_step_not_surjective n
  intro y
  exact ⟨(asIso (step doubleDiagram n)).inv y,
    ConcreteCategory.congr_hom (asIso (step doubleDiagram n)).inv_hom_id y⟩

/-- The original colimit map is nevertheless an isomorphism with both actual maps supplied. -/
def doubleColimitIso :
    GrpCat.FilteredColimits.colimit doubleDiagram ≅
      GrpCat.FilteredColimits.colimit (successorFunctor ⋙ doubleDiagram) :=
  successorInterleavingIso doubleDiagram

end GrpCat.FilteredInterleavingTests
