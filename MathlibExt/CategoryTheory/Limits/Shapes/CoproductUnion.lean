/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Coproducts with varying objects on a union of index subsets

The summand at an index `i` is the given object `D i`. Restricting the index
set preserves the same summand, and the two subset inclusions produce the
actual union pushout. This supplies the degreewise comparison for a
coefficient bar on a union of simplicial subcomplexes.
-/

noncomputable section

universe w v u

namespace CategoryTheory.Limits.Sigma

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  {I : Type w} (D : I → C)

public section

/-- Inclusion of restricted coproducts, with the identity on each original
summand. The coefficient objects are allowed to vary with the index. -/
def subtypeMap {s t : Set I} (h : s ⊆ t) :
    (∐ fun i : ↥s => D i.1) ⟶ ∐ fun i : ↥t => D i.1 :=
  Sigma.map' (f := fun j : ↥t => D j.1) (g := fun j : ↥s => D j.1)
    (fun i : ↥s => (⟨i.1, h i.2⟩ : ↥t)) (fun i : ↥s => 𝟙 (D i.1))

/-- The original summand maps to the same index in the larger subset. -/
@[reassoc]
theorem ι_subtypeMap {s t : Set I} (h : s ⊆ t) (i : ↥s) :
    Sigma.ι (fun j : ↥s => D j.1) i ≫ subtypeMap D h =
      Sigma.ι (fun j : ↥t => D j.1) ⟨i.1, h i.2⟩ := by
  change Sigma.ι (fun j : ↥s => D j.1) i ≫
      Sigma.map' (f := fun j : ↥t => D j.1) (g := fun j : ↥s => D j.1)
        (fun j : ↥s => (⟨j.1, h j.2⟩ : ↥t)) (fun j : ↥s => 𝟙 (D j.1)) = _
  rw [Sigma.ι_comp_map', Category.id_comp]

/-- With zero morphisms, the actual weighted subset inclusion is monic.
The existing MonoCoprod theorem applies to the actual injective index map. -/
theorem mono_subtypeMap [HasZeroMorphisms C] {s t : Set I} (h : s ⊆ t) :
    Mono (subtypeMap D h) := by
  change Mono (Sigma.map' (f := fun j : ↥t => D j.1)
    (g := fun i : ↥s => D i.1)
    (fun i : ↥s => (⟨i.1, h i.2⟩ : ↥t)) (fun i : ↥s => 𝟙 (D i.1)))
  exact MonoCoprod.mono_map'_of_injective (fun j : ↥t => D j.1)
    (fun i : ↥s => (⟨i.1, h i.2⟩ : ↥t)) (by
      intro i j hij
      exact Subtype.ext (congrArg (fun z : ↥t => z.val) hij))

end

private def unionDesc (s t : Set I) {Z : C}
    (a : (∐ fun i : ↥s => D i.1) ⟶ Z)
    (b : (∐ fun i : ↥t => D i.1) ⟶ Z) :
    (∐ fun i : ↥(s ∪ t) => D i.1) ⟶ Z := by
  classical
  exact Sigma.desc fun i : ↥(s ∪ t) =>
    if hi : i.1 ∈ s then
      Sigma.ι (fun j : ↥s => D j.1) ⟨i.1, hi⟩ ≫ a
    else
      Sigma.ι (fun j : ↥t => D j.1) ⟨i.1, i.2.resolve_left hi⟩ ≫ b

private theorem subtypeMap_unionDesc_left (s t : Set I) {Z : C}
    (a : (∐ fun i : ↥s => D i.1) ⟶ Z)
    (b : (∐ fun i : ↥t => D i.1) ⟶ Z) :
    subtypeMap D (Set.subset_union_left : s ⊆ s ∪ t) ≫
      unionDesc D s t a b = a := by
  classical
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, ι_subtypeMap]
  simp only [unionDesc, Sigma.ι_comp_desc]
  exact dite_eq_left i.2

private theorem subtypeMap_unionDesc_right (s t : Set I) {Z : C}
    (a : (∐ fun i : ↥s => D i.1) ⟶ Z)
    (b : (∐ fun i : ↥t => D i.1) ⟶ Z)
    (h : subtypeMap D (Set.inter_subset_left : s ∩ t ⊆ s) ≫ a =
      subtypeMap D (Set.inter_subset_right : s ∩ t ⊆ t) ≫ b) :
    subtypeMap D (Set.subset_union_right : t ⊆ s ∪ t) ≫
      unionDesc D s t a b = b := by
  classical
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, ι_subtypeMap]
  simp only [unionDesc, Sigma.ι_comp_desc]
  by_cases hi : i.1 ∈ s
  · rw [dite_eq_left hi]
    have hw := congrArg
      (fun k => Sigma.ι (fun j : ↥(s ∩ t) => D j.1) ⟨i.1, hi, i.2⟩ ≫ k) h
    simpa only [← Category.assoc, ι_subtypeMap] using hw
  · rw [dite_eq_right hi]

public section

/-- The actual coproduct restrictions over an intersection and a union form
a pushout, for arbitrary coefficient objects and independent category and
index universes. No exactness or flatness assumption is required. -/
theorem isPushout_subtypeUnion (s t : Set I) :
    IsPushout
      (subtypeMap D (Set.inter_subset_left : s ∩ t ⊆ s))
      (subtypeMap D (Set.inter_subset_right : s ∩ t ⊆ t))
      (subtypeMap D (Set.subset_union_left : s ⊆ s ∪ t))
      (subtypeMap D (Set.subset_union_right : t ⊆ s ∪ t)) := by
  classical
  apply IsPushout.mk'
  · apply Sigma.hom_ext
    intro i
    simp only [← Category.assoc, ι_subtypeMap]
  · intro Z m m' hs ht
    apply Sigma.hom_ext
    intro i
    rcases i.2 with hi | hi
    · have hw := congrArg
        (fun k => Sigma.ι (fun j : ↥s => D j.1) ⟨i.1, hi⟩ ≫ k) hs
      simpa only [← Category.assoc, ι_subtypeMap] using hw
    · have hw := congrArg
        (fun k => Sigma.ι (fun j : ↥t => D j.1) ⟨i.1, hi⟩ ≫ k) ht
      simpa only [← Category.assoc, ι_subtypeMap] using hw
  · intro Z a b h
    exact ⟨unionDesc D s t a b,
      subtypeMap_unionDesc_left D s t a b,
      subtypeMap_unionDesc_right D s t a b h⟩

end

end CategoryTheory.Limits.Sigma

end
