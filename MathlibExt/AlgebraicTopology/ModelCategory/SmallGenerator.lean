/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.SmallObject.Basic

import Mathlib.CategoryTheory.Presentable.IsDiscrete
import Mathlib.CategoryTheory.Presentable.Uniformization

/-!
# Small generators in locally presentable categories

Literal functor images of small morphism properties remain small. The
canonical strict-image/right-orthogonal theorem `strictMap_rlp_eq_inverseImage_rlp`
is in `MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct`, which this file
imports publicly. A small family whose sources are `χ`-presentable in a
`χ`-locally presentable category is eligible for the small-object argument at `χ`.
Finally, every small morphism property in a locally presentable category
permits the small-object argument.

These results install no global instances or generator choices.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v v' u u'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

/-- The literal image of a small morphism property under a functor is small. -/
theorem IsSmall.strictMap
    {I : MorphismProperty C} (hI : I.IsSmall.{w}) (F : C ⥤ D) :
    (I.strictMap F).IsSmall.{w} := by
  let _ : I.IsSmall.{w} := hI
  let φ : I.toSet → (I.strictMap F).toSet := fun i =>
    ⟨Arrow.mk (F.map i.1.hom), ⟨i.2⟩⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨X, Y, g⟩, hg⟩
    cases hg with
    | map hf =>
        exact ⟨⟨Arrow.mk _, hf⟩, rfl⟩
  exact ⟨small_of_surjective hφ⟩

end CategoryTheory.MorphismProperty

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- A small morphism property whose sources are `χ`-presentable, in a `χ`-locally presentable
category, is eligible for the small-object argument at `χ`. -/
theorem isCardinalForSmallObjectArgument_of_presentable_sources
    (I : MorphismProperty C) (χ : Cardinal.{w}) [Fact χ.IsRegular] [OrderBot χ.ord.ToType]
    [IsCardinalLocallyPresentable C χ] [I.IsSmall.{w}]
    (h : ∀ ⦃A B : C⦄ (i : A ⟶ B), I i → IsCardinalPresentable A χ) :
    I.IsCardinalForSmallObjectArgument χ where
  preservesColimit {A _ _ _} i hi _ _ := by
    have := h i hi
    have := preservesColimitsOfShape_of_isCardinalPresentable A χ χ.ord.ToType
    infer_instance

/-- A small morphism property in a locally presentable category permits the
small-object argument. The regular cardinal is chosen uniformly for all
generator sources. -/
theorem hasSmallObjectArgument_of_isSmall
    (I : MorphismProperty C)
    [IsLocallyPresentable.{w} C] [I.IsSmall.{w}] :
    I.HasSmallObjectArgument.{w} := by
  obtain ⟨κ₀, hκ₀, hC₀⟩ :=
    IsLocallyPresentable.exists_cardinal.{w} C
  let _ : Fact κ₀.IsRegular := hκ₀
  let _ : IsCardinalLocallyPresentable C κ₀ := hC₀
  let D₀ : Type := Discrete PUnit
  let K := I.toSet
  let _ : Small.{w} K := by
    dsimp [K]
    infer_instance
  let source : K → C := fun k => k.1.left
  let F : K → D₀ ⥤ C := fun k =>
    (Functor.const D₀).obj (source k)
  let _ (k : K) : Functor.IsAccessible.{w} (F k) := by
    dsimp [F]
    infer_instance
  obtain ⟨κ, hκ, hD₀, hC, _, hPres⟩ :=
    IsCardinalAccessibleCategory.uniformization_of_small F
  let _ : Fact κ.IsRegular := hκ
  let _ : IsCardinalAccessibleCategory D₀ κ := hD₀
  let _ : IsCardinalAccessibleCategory C κ := hC
  let hCLP : IsCardinalLocallyPresentable C κ :=
    { toHasCardinalFilteredGenerator := inferInstance
      toHasColimitsOfSize := inferInstance }
  have hne : Nonempty κ.ord.ToType := by
    simpa using Cardinal.IsRegular.ne_zero Fact.out
  let _ : Nonempty κ.ord.ToType := hne
  let hBot : OrderBot κ.ord.ToType :=
    WellFoundedLT.toOrderBot κ.ord.ToType
  let _ : OrderBot κ.ord.ToType := hBot
  have hSource (k : K) : IsCardinalPresentable (source k) κ := by
    let _ : (F k).PreservesCardinalPresentable κ := hPres k
    have h : IsCardinalPresentable ((F k).obj ⟨PUnit.unit⟩) κ :=
      inferInstance
    simpa [F] using h
  let hI : I.IsCardinalForSmallObjectArgument κ :=
    isCardinalForSmallObjectArgument_of_presentable_sources I κ (fun A _ i hi => by
      simpa [source] using hSource ⟨Arrow.mk i, hi⟩)
  exact ⟨κ, inferInstance, hBot, hI⟩

end CategoryTheory.MorphismProperty
