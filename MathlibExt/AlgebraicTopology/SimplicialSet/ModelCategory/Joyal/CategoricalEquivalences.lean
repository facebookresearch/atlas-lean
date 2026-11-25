/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Whiskering

/-! # Joyal categorical equivalences

`SSet.categoricalEquivalences` is the class of weak categorical equivalences
for the Joyal model structure, in the `hFun` formulation: a map `f : X ⟶ Y`
belongs to the class when precomposition with `f` induces an equivalence of
ordinary homotopy categories `h Fun(Y, C) ⟶ h Fun(X, C)` for every
quasicategory `C`, where `Fun(X, C) = (ihom X).obj C`, precomposition is
`(pre f).app C`, and `h` is `SSet.hoFunctor`.

This module proves the formal closure properties that follow from the
definition alone: categorical equivalences contain identities and
isomorphisms, respect isomorphisms, are stable under composition, have the
two-out-of-three property, and are stable under retracts. The
functoriality of precomposition on homotopy categories of functor
objects used in these proofs is available as the public lemmas
`SSet.hoFunctor_pre_id` and `SSet.hoFunctor_pre_comp`. Stronger results
(such as inner anodyne maps being categorical equivalences) and the Joyal
model structure itself are deliberately not part of this module; the raw
morphism property is usable without opening any model-category scope.

## References

* J. Lurie, *Higher Topos Theory*, §2.2.5 (the `hFun` formulation of weak
  categorical equivalence).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed

/-- A functor is an equivalence if it is a retract of an equivalence in the
strict sense: there are functors `Il`, `Ir`, `Rl`, `Rr` making the obvious
diagram commute on the nose and exhibiting `F` as a retract of `G`. The
quasi-inverse of `F` is `Ir ⋙ G.inv ⋙ Rl`. -/
private lemma Functor.IsEquivalence.of_retract_strict
    {A₁ A₂ B₁ B₂ : Type u} [Category.{u} A₁] [Category.{u} A₂]
    [Category.{u} B₁] [Category.{u} B₂]
    {F : A₁ ⥤ A₂} {G : B₁ ⥤ B₂}
    (Il : A₁ ⥤ B₁) (Ir : A₂ ⥤ B₂) (Rl : B₁ ⥤ A₁) (Rr : B₂ ⥤ A₂)
    (hI : Il ⋙ G = F ⋙ Ir) (hR : Rl ⋙ F = G ⋙ Rr)
    (hl : Il ⋙ Rl = 𝟭 A₁) (hr : Ir ⋙ Rr = 𝟭 A₂)
    [G.IsEquivalence] : F.IsEquivalence := by
  let H : A₂ ⥤ A₁ := Ir ⋙ G.inv ⋙ Rl
  have eqA : F ⋙ H = Il ⋙ (G ⋙ G.inv) ⋙ Rl :=
    congrArg (· ⋙ (G.inv ⋙ Rl)) hI.symm
  have eqB : Il ⋙ (𝟭 B₁) ⋙ Rl = 𝟭 A₁ := hl
  have eFH : F ⋙ H ≅ 𝟭 A₁ :=
    (eqToIso eqA) ≪≫
      (Functor.isoWhiskerLeft Il (Functor.isoWhiskerRight G.asEquivalence.unitIso.symm Rl)) ≪≫
        (eqToIso eqB)
  have eqC : H ⋙ F = Ir ⋙ (G.inv ⋙ G) ⋙ Rr :=
    congrArg (Ir ⋙ G.inv ⋙ ·) hR
  have eqD : Ir ⋙ (𝟭 B₂) ⋙ Rr = 𝟭 A₂ := hr
  have eHF : H ⋙ F ≅ 𝟭 A₂ :=
    (eqToIso eqC) ≪≫
      (Functor.isoWhiskerLeft Ir (Functor.isoWhiskerRight G.asEquivalence.counitIso Rr)) ≪≫
        (eqToIso eqD)
  exact Functor.IsEquivalence.mk' H eFH.symm eHF

namespace SSet

/-- The morphism property of Joyal categorical equivalences between
simplicial sets. A map `f : X ⟶ Y` is tested by precomposition on the
simplicial functor objects into every quasicategory and passage to the
homotopy category: `f` is a categorical equivalence when the induced functor
`h Fun(Y, C) ⟶ h Fun(X, C)` is an equivalence of ordinary categories for
every quasicategory `C`.

This is the `hFun` formulation of weak categorical equivalence used in HTT
§2.2.5. Its equivalence with other formulations (bijectivity on isomorphism
classes, quasicategorical equivalences of functor objects) is a theorem
obligation elsewhere, not built into this definition. -/
def categoricalEquivalences : MorphismProperty SSet.{u} :=
  fun _ _ f => ∀ (C : SSet.{u}), SSet.Quasicategory C →
    (SSet.hoFunctor.map ((pre f).app C)).toFunctor.IsEquivalence

variable {X Y Z : SSet.{u}}

/-- Membership in `categoricalEquivalences` unfolds to the defining
`hFun` condition. -/
theorem categoricalEquivalences.mem_iff (f : X ⟶ Y) :
    categoricalEquivalences f ↔
      ∀ (C : SSet.{u}), Quasicategory C →
        (hoFunctor.map ((pre f).app C)).toFunctor.IsEquivalence :=
  Iff.rfl

/-- Precomposition with an identity map induces the identity functor on
homotopy categories of functor objects: `h Fun(𝟙 X, C)` is the identity
of `h Fun(X, C)`. -/
lemma hoFunctor_pre_id (C : SSet.{u}) :
    (hoFunctor.map ((pre (𝟙 X)).app C)).toFunctor =
      𝟭 (hoFunctor.obj ((ihom X).obj C)) := by
  have h1 : (pre (𝟙 X)).app C = 𝟙 ((ihom X).obj C) := by rw [pre_id]; rfl
  rw [h1, hoFunctor.map_id, Cat.Hom.id_toFunctor]

/-- Precomposition is contravariantly functorial on homotopy categories
of functor objects: `h Fun(f ≫ g, C)` is the composite
`h Fun(g, C) ⋙ h Fun(f, C)`. -/
lemma hoFunctor_pre_comp (C : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (hoFunctor.map ((pre (f ≫ g)).app C)).toFunctor =
      (hoFunctor.map ((pre g).app C)).toFunctor ⋙
        (hoFunctor.map ((pre f).app C)).toFunctor := by
  have h1 : (pre (f ≫ g)).app C = (pre g).app C ≫ (pre f).app C := by
    rw [pre_map]; rfl
  rw [h1, hoFunctor.map_comp, Cat.Hom.comp_toFunctor]

/-- Isomorphisms of simplicial sets are categorical equivalences. -/
theorem categoricalEquivalences.of_isIso (f : X ⟶ Y) [IsIso f] :
    categoricalEquivalences f := by
  intro C _
  have e1 : (𝟭 (hoFunctor.obj ((ihom Y).obj C))) =
      (hoFunctor.map ((pre f).app C)).toFunctor ⋙
        (hoFunctor.map ((pre (inv f)).app C)).toFunctor := by
    rw [← hoFunctor_pre_comp, IsIso.inv_hom_id, hoFunctor_pre_id]
  have e2 : (hoFunctor.map ((pre (inv f)).app C)).toFunctor ⋙
        (hoFunctor.map ((pre f).app C)).toFunctor =
      𝟭 (hoFunctor.obj ((ihom X).obj C)) := by
    rw [← hoFunctor_pre_comp, IsIso.hom_inv_id, hoFunctor_pre_id]
  exact Functor.IsEquivalence.mk' _ (eqToIso e1) (eqToIso e2)

/-- Categorical equivalences contain identity morphisms. -/
instance categoricalEquivalences.containsIdentities :
    categoricalEquivalences.ContainsIdentities where
  id_mem X := by
    intro C _
    rw [hoFunctor_pre_id]
    infer_instance

/-- Categorical equivalences are stable under composition. -/
instance categoricalEquivalences.isStableUnderComposition :
    categoricalEquivalences.IsStableUnderComposition where
  comp_mem f g hf hg := by
    intro C hC
    have := hf C hC
    have := hg C hC
    rw [hoFunctor_pre_comp]
    infer_instance

/-- Categorical equivalences are multiplicative: they contain identities and
are stable under composition. -/
instance categoricalEquivalences.isMultiplicative :
    categoricalEquivalences.IsMultiplicative where

/-- Left cancellation for categorical equivalences: if `g` and `f ≫ g` are
categorical equivalences, so is `f`. -/
instance categoricalEquivalences.hasOfPostcompProperty :
    categoricalEquivalences.HasOfPostcompProperty categoricalEquivalences where
  of_postcomp f g hg hfg := by
    intro C hC
    have := hg C hC
    have hcomp : ((hoFunctor.map ((pre g).app C)).toFunctor ⋙
        (hoFunctor.map ((pre f).app C)).toFunctor).IsEquivalence := by
      rw [← hoFunctor_pre_comp]
      exact hfg C hC
    have := hcomp
    exact Functor.isEquivalence_of_comp_left
      (hoFunctor.map ((pre g).app C)).toFunctor
      (hoFunctor.map ((pre f).app C)).toFunctor

/-- Right cancellation for categorical equivalences: if `f` and `f ≫ g` are
categorical equivalences, so is `g`. -/
instance categoricalEquivalences.hasOfPrecompProperty :
    categoricalEquivalences.HasOfPrecompProperty categoricalEquivalences where
  of_precomp f g hf hfg := by
    intro C hC
    have := hf C hC
    have hcomp : ((hoFunctor.map ((pre g).app C)).toFunctor ⋙
        (hoFunctor.map ((pre f).app C)).toFunctor).IsEquivalence := by
      rw [← hoFunctor_pre_comp]
      exact hfg C hC
    have := hcomp
    exact Functor.isEquivalence_of_comp_right
      (hoFunctor.map ((pre g).app C)).toFunctor
      (hoFunctor.map ((pre f).app C)).toFunctor

/-- Categorical equivalences have the two-out-of-three property. -/
instance categoricalEquivalences.hasTwoOutOfThreeProperty :
    categoricalEquivalences.HasTwoOutOfThreeProperty where

/-- Categorical equivalences respect isomorphisms: they are stable under
pre- and postcomposition with isomorphisms. -/
instance categoricalEquivalences.respectsIso :
    categoricalEquivalences.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) => categoricalEquivalences.of_isIso f)

/-- A retract of a categorical equivalence is a categorical equivalence. -/
theorem categoricalEquivalences.of_retract {A B : SSet.{u}} {f : X ⟶ Y} {g : A ⟶ B}
    (h : RetractArrow f g) (hg : categoricalEquivalences g) :
    categoricalEquivalences f := by
  intro C hC
  have key : ∀ {P Q R : SSet.{u}} (a : P ⟶ Q) (b : Q ⟶ R),
      (pre b).app C ≫ (pre a).app C = (pre (a ≫ b)).app C := by
    intro P Q R a b
    rw [pre_map]
    rfl
  have hP : RetractArrow ((pre f).app C) ((pre g).app C) :=
    { i := Arrow.homMk' ((pre h.r.right).app C) ((pre h.r.left).app C)
        (by rw [key, key, h.r_w])
      r := Arrow.homMk' ((pre h.i.right).app C) ((pre h.i.left).app C)
        (by rw [key, key, h.i_w])
      retract := by
        apply Arrow.hom_ext
        · simp only [Arrow.comp_left, Arrow.homMk'_left, Arrow.id_left]
          rw [key, h.retract_right]
          simp
        · simp only [Arrow.comp_right, Arrow.homMk'_right, Arrow.id_right]
          rw [key, h.retract_left]
          simp }
  have hCat := hP.map hoFunctor
  have hI : hCat.i.left.toFunctor ⋙ (hoFunctor.map ((pre g).app C)).toFunctor =
      (hoFunctor.map ((pre f).app C)).toFunctor ⋙ hCat.i.right.toFunctor :=
    congrArg Cat.Hom.toFunctor hCat.i_w
  have hR : hCat.r.left.toFunctor ⋙ (hoFunctor.map ((pre f).app C)).toFunctor =
      (hoFunctor.map ((pre g).app C)).toFunctor ⋙ hCat.r.right.toFunctor :=
    congrArg Cat.Hom.toFunctor hCat.r_w
  have hl : hCat.i.left.toFunctor ⋙ hCat.r.left.toFunctor =
      𝟭 (hoFunctor.obj ((ihom Y).obj C)) :=
    congrArg Cat.Hom.toFunctor hCat.retract_left
  have hr : hCat.i.right.toFunctor ⋙ hCat.r.right.toFunctor =
      𝟭 (hoFunctor.obj ((ihom X).obj C)) :=
    congrArg Cat.Hom.toFunctor hCat.retract_right
  have := hg C hC
  exact Functor.IsEquivalence.of_retract_strict _ _ _ _ hI hR hl hr

/-- Categorical equivalences are stable under retracts. -/
instance categoricalEquivalences.isStableUnderRetracts :
    categoricalEquivalences.IsStableUnderRetracts where
  of_retract := categoricalEquivalences.of_retract

end SSet
