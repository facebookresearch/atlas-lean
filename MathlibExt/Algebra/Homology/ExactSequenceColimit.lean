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

public import MathlibExt.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Pointwise colimits of exact five-object sequences

For a diagram of sequences A₀ → A₁ → A₂ → A₃ → A₄, take the colimit of each term and the
induced maps of its four arrows. The colimit coprojections commute with each arrow.

In an abelian category, exactness of a short complex of functors is pointwise. Thus when
colimits of the indexing shape are exact, a diagram of exact five-object sequences has an
exact pointwise colimit. The indexing category and coefficient category object and morphism
universes are independent.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.ComposableArrows

universe vJ uJ v u

/-- Exactness of functor-category short complexes is pointwise.

A short complex in J → C, for abelian C, is exact exactly when its evaluation at every j is
exact. -/
theorem functorCategory_shortComplex_exact_iff
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [Abelian C]
    (S : ShortComplex (J ⥤ C)) :
    S.Exact ↔ ∀ j : J,
      (S.map ((evaluation J C).obj j)).Exact := by
  let h : JointlyReflectIsomorphisms
      (fun j : J => (evaluation J C).obj j) :=
    { isIso := fun f => by
        apply NatIso.isIso_of_isIso_app }
  exact h.exact_iff S

/-- The underlying diagram of exact five-object sequences.

Forget the exactness property of each object in the diagram F : J → ExactSequences C 4 to
obtain its composable four-arrow sequence. -/
abbrev exactSequenceFourDiagram
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (F : J ⥤ ExactSequences C 4) : J ⥤ ComposableArrows C 4 :=
  F ⋙ ObjectProperty.ι (exactSequences C 4)

/-- The pointwise colimit of a diagram of five-object sequences.

Take the colimit of each of the five terms and use the colimit maps of the four arrow
transformations. -/
noncomputable def exactSequenceFourColimit
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasColimitsOfShape J C]
    (F : J ⥤ ExactSequences C 4) :
    ComposableArrows C 4 :=
  mk₄
    (colim.map ((exactSequenceFourDiagram F).flip.map
      (homOfLE (show (0 : Fin 5) ≤ 1 from by simp))))
    (colim.map ((exactSequenceFourDiagram F).flip.map
      (homOfLE (show (1 : Fin 5) ≤ 2 from by simp))))
    (colim.map ((exactSequenceFourDiagram F).flip.map
      (homOfLE (show (2 : Fin 5) ≤ 3 from by simp))))
    (colim.map ((exactSequenceFourDiagram F).flip.map
      (homOfLE (show (3 : Fin 5) ≤ 4 from by simp))))

/-- The terms of the pointwise sequence colimit.

The i-th object is the colimit of the diagram of i-th terms. -/
@[simp]
theorem exactSequenceFourColimit_obj
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasColimitsOfShape J C]
    (F : J ⥤ ExactSequences C 4) (i : Fin 5) :
    (exactSequenceFourColimit F).obj i =
      colimit ((exactSequenceFourDiagram F).flip.obj i) := by
  fin_cases i <;> rfl

/-- The first arrow of the sequence colimit.

The arrow from term 0 to term 1 is the colimit map of the first arrow transformation. -/
@[simp]
theorem exactSequenceFourColimit_map_zero_one
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasColimitsOfShape J C]
    (F : J ⥤ ExactSequences C 4) :
    (exactSequenceFourColimit F).map' 0 1 =
      colim.map ((exactSequenceFourDiagram F).flip.map
        (homOfLE (show (0 : Fin 5) ≤ 1 from by simp))) :=
  rfl

/-- The second arrow of the sequence colimit.

The arrow from term 1 to term 2 is the colimit map of the second arrow transformation. -/
@[simp]
theorem exactSequenceFourColimit_map_one_two
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasColimitsOfShape J C]
    (F : J ⥤ ExactSequences C 4) :
    (exactSequenceFourColimit F).map' 1 2 =
      colim.map ((exactSequenceFourDiagram F).flip.map
        (homOfLE (show (1 : Fin 5) ≤ 2 from by simp))) :=
  rfl

/-- The third arrow of the sequence colimit.

The arrow from term 2 to term 3 is the colimit map of the third arrow transformation. -/
@[simp]
theorem exactSequenceFourColimit_map_two_three
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasColimitsOfShape J C]
    (F : J ⥤ ExactSequences C 4) :
    (exactSequenceFourColimit F).map' 2 3 =
      colim.map ((exactSequenceFourDiagram F).flip.map
        (homOfLE (show (2 : Fin 5) ≤ 3 from by simp))) :=
  rfl

/-- The fourth arrow of the sequence colimit.

The arrow from term 3 to term 4 is the colimit map of the fourth arrow transformation. -/
@[simp]
theorem exactSequenceFourColimit_map_three_four
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasColimitsOfShape J C]
    (F : J ⥤ ExactSequences C 4) :
    (exactSequenceFourColimit F).map' 3 4 =
      colim.map ((exactSequenceFourDiagram F).flip.map
        (homOfLE (show (3 : Fin 5) ≤ 4 from by simp))) :=
  rfl

/-- The first arrow commutes with the colimit coprojections.

The term-0 coprojection followed by the colimit first arrow equals the stage first arrow
followed by the term-1 coprojection. -/
@[reassoc]
theorem exactSequenceFourColimit_ι_map_zero_one
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasColimitsOfShape J C]
    (F : J ⥤ ExactSequences C 4) (j : J) :
    colimit.ι ((exactSequenceFourDiagram F).flip.obj 0) j ≫
        (exactSequenceFourColimit F).map' 0 1 =
      (F.obj j).obj.map' 0 1 ≫
        colimit.ι ((exactSequenceFourDiagram F).flip.obj 1) j := by
  rw [exactSequenceFourColimit_map_zero_one]
  apply colimit.ι_map

/-- The second arrow commutes with the colimit coprojections.

The term-1 coprojection followed by the colimit second arrow equals the stage second arrow
followed by the term-2 coprojection. -/
@[reassoc]
theorem exactSequenceFourColimit_ι_map_one_two
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasColimitsOfShape J C]
    (F : J ⥤ ExactSequences C 4) (j : J) :
    colimit.ι ((exactSequenceFourDiagram F).flip.obj 1) j ≫
        (exactSequenceFourColimit F).map' 1 2 =
      (F.obj j).obj.map' 1 2 ≫
        colimit.ι ((exactSequenceFourDiagram F).flip.obj 2) j := by
  rw [exactSequenceFourColimit_map_one_two]
  apply colimit.ι_map

/-- The third arrow commutes with the colimit coprojections.

The term-2 coprojection followed by the colimit third arrow equals the stage third arrow
followed by the term-3 coprojection. -/
@[reassoc]
theorem exactSequenceFourColimit_ι_map_two_three
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasColimitsOfShape J C]
    (F : J ⥤ ExactSequences C 4) (j : J) :
    colimit.ι ((exactSequenceFourDiagram F).flip.obj 2) j ≫
        (exactSequenceFourColimit F).map' 2 3 =
      (F.obj j).obj.map' 2 3 ≫
        colimit.ι ((exactSequenceFourDiagram F).flip.obj 3) j := by
  rw [exactSequenceFourColimit_map_two_three]
  apply colimit.ι_map

/-- The fourth arrow commutes with the colimit coprojections.

The term-3 coprojection followed by the colimit fourth arrow equals the stage fourth arrow
followed by the term-4 coprojection. -/
@[reassoc]
theorem exactSequenceFourColimit_ι_map_three_four
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    [HasColimitsOfShape J C]
    (F : J ⥤ ExactSequences C 4) (j : J) :
    colimit.ι ((exactSequenceFourDiagram F).flip.obj 3) j ≫
        (exactSequenceFourColimit F).map' 3 4 =
      (F.obj j).obj.map' 3 4 ≫
        colimit.ι ((exactSequenceFourDiagram F).flip.obj 4) j := by
  rw [exactSequenceFourColimit_map_three_four]
  apply colimit.ι_map

private def exactSequenceFourShortComplexDiagram
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (F : J ⥤ ExactSequences C 4) (i : ℕ) (hi : i + 2 ≤ 4) :
    ShortComplex (J ⥤ C) :=
  ShortComplex.mk
    ((exactSequenceFourDiagram F).flip.map
      (homOfLE (show (⟨i, by omega⟩ : Fin 5) ≤
        ⟨i + 1, by omega⟩ from by simp)))
    ((exactSequenceFourDiagram F).flip.map
      (homOfLE (show (⟨i + 1, by omega⟩ : Fin 5) ≤
        ⟨i + 2, by omega⟩ from by simp)))
    (by
      ext j
      exact (F.obj j).property.toIsComplex.zero i hi)

private theorem exactSequenceFourShortComplexDiagram_exact
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [Abelian C]
    (F : J ⥤ ExactSequences C 4) (i : ℕ) (hi : i + 2 ≤ 4) :
    (exactSequenceFourShortComplexDiagram F i hi).Exact := by
  rw [functorCategory_shortComplex_exact_iff]
  intro j
  change ((F.obj j).obj.sc (F.obj j).property.toIsComplex i hi).Exact
  exact (F.obj j).property.exact i hi

/-- Exact colimits preserve an exact five-object sequence.

If C is abelian and colimits of shape J are exact, the pointwise colimit of F : J →
ExactSequences C 4 is exact. -/
theorem exactSequenceFourColimit_exact
    {J : Type uJ} [Category.{vJ} J]
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]
    (F : J ⥤ ExactSequences C 4) :
    (exactSequenceFourColimit F).Exact := by
  let S₀ := exactSequenceFourShortComplexDiagram F 0 (by omega)
  let S₁ := exactSequenceFourShortComplexDiagram F 1 (by omega)
  let S₂ := exactSequenceFourShortComplexDiagram F 2 (by omega)
  have hS₀ : S₀.Exact :=
    exactSequenceFourShortComplexDiagram_exact F 0 (by omega)
  have hS₁ : S₁.Exact :=
    exactSequenceFourShortComplexDiagram_exact F 1 (by omega)
  have hS₂ : S₂.Exact :=
    exactSequenceFourShortComplexDiagram_exact F 2 (by omega)
  let T₀ := colim.mapShortComplex S₀ (colimit.isColimit S₀.X₁)
    (colimit.cocone S₀.X₂) (colimit.cocone S₀.X₃)
    (colim.map S₀.f) (colim.map S₀.g)
    (fun j => colimit.ι_map S₀.f j) (fun j => colimit.ι_map S₀.g j)
  let T₁ := colim.mapShortComplex S₁ (colimit.isColimit S₁.X₁)
    (colimit.cocone S₁.X₂) (colimit.cocone S₁.X₃)
    (colim.map S₁.f) (colim.map S₁.g)
    (fun j => colimit.ι_map S₁.f j) (fun j => colimit.ι_map S₁.g j)
  let T₂ := colim.mapShortComplex S₂ (colimit.isColimit S₂.X₁)
    (colimit.cocone S₂.X₂) (colimit.cocone S₂.X₃)
    (colim.map S₂.f) (colim.map S₂.g)
    (fun j => colimit.ι_map S₂.f j) (fun j => colimit.ι_map S₂.g j)
  have h₀ : T₀.Exact := colim.exact_mapShortComplex hS₀
    (colimit.isColimit S₀.X₁) (colimit.isColimit S₀.X₂)
    (colimit.isColimit S₀.X₃)
    (colim.map S₀.f) (colim.map S₀.g)
    (fun j => colimit.ι_map S₀.f j) (fun j => colimit.ι_map S₀.g j)
  have h₁ : T₁.Exact := colim.exact_mapShortComplex hS₁
    (colimit.isColimit S₁.X₁) (colimit.isColimit S₁.X₂)
    (colimit.isColimit S₁.X₃)
    (colim.map S₁.f) (colim.map S₁.g)
    (fun j => colimit.ι_map S₁.f j) (fun j => colimit.ι_map S₁.g j)
  have h₂ : T₂.Exact := colim.exact_mapShortComplex hS₂
    (colimit.isColimit S₂.X₁) (colimit.isColimit S₂.X₂)
    (colimit.isColimit S₂.X₃)
    (colim.map S₂.f) (colim.map S₂.g)
    (fun j => colimit.ι_map S₂.f j) (fun j => colimit.ι_map S₂.g j)
  have hz₀ : (exactSequenceFourColimit F).map' 0 1 ≫
      (exactSequenceFourColimit F).map' 1 2 = 0 := by
    exact T₀.zero
  have hz₁ : (exactSequenceFourColimit F).map' 1 2 ≫
      (exactSequenceFourColimit F).map' 2 3 = 0 := by
    exact T₁.zero
  have hz₂ : (exactSequenceFourColimit F).map' 2 3 ≫
      (exactSequenceFourColimit F).map' 3 4 = 0 := by
    exact T₂.zero
  let hcomplex : (exactSequenceFourColimit F).IsComplex :=
    { zero := fun i hi => by
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi' with rfl | rfl | rfl
        · exact hz₀
        · exact hz₁
        · exact hz₂ }
  refine { toIsComplex := hcomplex, exact := fun i hi => ?_ }
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi' with rfl | rfl | rfl
  · exact h₀
  · exact h₁
  · exact h₂

end CategoryTheory.ComposableArrows

end
