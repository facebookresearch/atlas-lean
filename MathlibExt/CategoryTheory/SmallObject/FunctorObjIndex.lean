/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.SmallObject.Construction

/-! # Original whole attaching-square label actions

Map the native labels through a functor and postcompose them by an original
Arrow map, retaining the generator index and both prescribed square maps.
The native label type and its small-object construction are due to
Joël Riou (Mathlib, 2024).
-/

@[expose] public section

set_option autoImplicit false
universe s uC vC uD vD
open CategoryTheory
namespace CategoryTheory.SmallObject.FunctorObjIndex

variable {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    {I : Type s} {A B : I → C} {j : ∀ i, A i ⟶ B i}
    {X S : C} {p : X ⟶ S}

/-- Map every original attaching square through a functor. -/
@[simps i t b]
def map (q : FunctorObjIndex j p) (F : C ⥤ D) :
    FunctorObjIndex (fun i => F.map (j i)) (F.map p) where
  i := q.i
  t := F.map q.t
  b := F.map q.b
  w := by simpa only [Functor.map_comp] using F.congr_map q.w

/-- Postcompose both maps of an original attaching square by an Arrow map. -/
@[simps i t b]
def postcomp {Y T : C} {p' : Y ⟶ T} (q : FunctorObjIndex j p)
    (τ : Arrow.mk p ⟶ Arrow.mk p') : FunctorObjIndex j p' where
  i := q.i
  t := q.t ≫ τ.left
  b := q.b ≫ τ.right
  w := by
    rw [Category.assoc, Arrow.w_mk τ, ← Category.assoc, q.w, Category.assoc]

end CategoryTheory.SmallObject.FunctorObjIndex

universe t v u

namespace CategoryTheory.SmallObject.FunctorObjIndex

variable {C : Type u} [Category.{v} C]
  {A : Type t} {S T : A → C} {s : ∀ a, S a ⟶ T a}
  {f g h : Arrow C}

/-- Postcomposition by the actual identity preserves the whole original square. -/
theorem postcomp_id (a : FunctorObjIndex s f.hom) :
    a.postcomp (𝟙 f) = a := by
  cases a
  simp [postcomp]

/-- The original whole square postcomposition composes on both prescribed maps. -/
theorem postcomp_comp (a : FunctorObjIndex s f.hom) (φ : f ⟶ g) (ψ : g ⟶ h) :
    a.postcomp (φ ≫ ψ) = (a.postcomp φ).postcomp ψ := by
  cases f
  cases g
  cases h
  rcases a with ⟨i, a, b, w⟩
  have ha : a ≫ (φ ≫ ψ).left = (a ≫ φ.left) ≫ ψ.left :=
    (congrArg (fun z => a ≫ z) (Arrow.leftFunc.map_comp φ ψ)).trans
      (Category.assoc a φ.left ψ.left).symm
  have hb : b ≫ (φ ≫ ψ).right = (b ≫ φ.right) ≫ ψ.right :=
    (congrArg (fun z => b ≫ z) (Arrow.rightFunc.map_comp φ ψ)).trans
      (Category.assoc b φ.right ψ.right).symm
  simpa only [postcomp, FunctorObjIndex.mk.injEq] using
    And.intro True.intro (And.intro (heq_of_eq ha) (heq_of_eq hb))

/-- Postcomposition by an Arrow map with monic components preserves the
entire original attaching square injectively, including its generator label. -/
theorem postcomp_injective (φ : f ⟶ g) [Mono φ.left] [Mono φ.right] :
    Function.Injective (fun a : FunctorObjIndex s f.hom => a.postcomp φ) := by
  cases f
  cases g
  rintro ⟨i, t, b, w⟩ ⟨i', t', b', w'⟩ hab
  simp only [postcomp, FunctorObjIndex.mk.injEq] at hab
  rcases hab with ⟨rfl, ht, hb⟩
  have ht' : t = t' := (cancel_mono φ.left).mp (eq_of_heq ht)
  have hb' : b = b' := (cancel_mono φ.right).mp (eq_of_heq hb)
  subst t'
  subst b'
  rfl

end CategoryTheory.SmallObject.FunctorObjIndex

namespace CategoryTheory.SmallObject.FunctorObjIndex

variable {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    {I : Type s} {A B : I → C}

/-- The full-faithful equivalence of the whole original attaching squares. -/
noncomputable def equivMap (j : ∀ i, A i ⟶ B i) (F : C ⥤ D)
    [F.Full] [F.Faithful] {X S : C} (p : X ⟶ S) :
    FunctorObjIndex j p ≃ FunctorObjIndex (fun i => F.map (j i)) (F.map p) where
  toFun q := q.map F
  invFun r :=
    ⟨r.i, F.preimage r.t, F.preimage r.b, by
      apply F.map_injective
      simpa only [Functor.map_comp, Functor.map_preimage] using r.w⟩
  left_inv := by
    rintro ⟨i, t, b, w⟩
    simp only [FunctorObjIndex.map, Functor.preimage_map]
  right_inv := by
    rintro ⟨i, t, b, w⟩
    simp only [FunctorObjIndex.map, Functor.map_preimage]

section
variable (j : ∀ i, A i ⟶ B i) (F : C ⥤ D) [F.Full] [F.Faithful]
    {X S : C} (p : X ⟶ S)

/-- The forward equivalence is the original mapped-label function. -/
@[simp]
theorem equivMap_apply (q : FunctorObjIndex j p) : equivMap j F p q = q.map F := rfl

/-- The inverse retains the same original generator index. -/
@[simp]
theorem equivMap_symm_apply_i
    (r : FunctorObjIndex (fun i => F.map (j i)) (F.map p)) :
    ((equivMap j F p).symm r).i = r.i := rfl

/-- The inverse top map is its original full-faithful preimage. -/
@[simp]
theorem equivMap_symm_apply_t
    (r : FunctorObjIndex (fun i => F.map (j i)) (F.map p)) :
    ((equivMap j F p).symm r).t = F.preimage r.t := rfl

/-- The inverse bottom map is its original full-faithful preimage. -/
@[simp]
theorem equivMap_symm_apply_b
    (r : FunctorObjIndex (fun i => F.map (j i)) (F.map p)) :
    ((equivMap j F p).symm r).b = F.preimage r.b := rfl
end

end CategoryTheory.SmallObject.FunctorObjIndex

namespace CategoryTheory.SmallObject.FunctorObjIndex

variable {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D]
    {I : Type s} {A B : I → C} {j : ∀ i, A i ⟶ B i}
    {X S Y T : C} {p : X ⟶ S} {p' : Y ⟶ T}

/-- Mapping every whole original label commutes with original postcomposition. -/
theorem map_postcomp (q : FunctorObjIndex j p)
    (τ : Arrow.mk p ⟶ Arrow.mk p') (F : C ⥤ D) :
    (q.postcomp τ).map F = (q.map F).postcomp (F.mapArrow.map τ) := by
  cases q
  simp [FunctorObjIndex.map, FunctorObjIndex.postcomp, Functor.map_comp]

end CategoryTheory.SmallObject.FunctorObjIndex
