/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Injective objects in discrete diagram categories

Let C be a category with pullbacks and enough injectives. For any indexing
type I, the category of diagrams Discrete I → C also has enough injectives.
An injective presentation is obtained by choosing an injective presentation
at each index. The index, object and morphism universes are independent.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

/-- A discrete diagram of injective objects is injective when the value category
has pullbacks. The extension through a monomorphism is formed componentwise. -/
theorem injective_discrete_of_obj {I : Type w} [HasPullbacks C]
    (D : Discrete I ⥤ C) (hD : ∀ i, Injective (D.obj i)) : Injective D where
  factors g f _ := by
    have (i : Discrete I) : Injective (D.obj i) := hD i
    refine ⟨Discrete.natTrans (fun i => Injective.factorThru (g.app i) (f.app i)), ?_⟩
    apply NatTrans.ext
    funext i
    exact Injective.comp_factorThru (g.app i) (f.app i)

/-- If C has pullbacks and enough injectives, diagrams on any discrete indexing type I have enough
injectives. The index and both category universes are independent. -/
theorem enoughInjectives_discrete (I : Type w) [HasPullbacks C] [EnoughInjectives C] :
    EnoughInjectives (Discrete I ⥤ C) where
  presentation F := by
    let J : Discrete I ⥤ C :=
      Discrete.functor (fun i => Injective.under (F.obj (Discrete.mk i)))
    have hJ : ∀ i, Injective (J.obj i) := by
      intro i
      dsimp [J]
      infer_instance
    let j : F ⟶ J := Discrete.natTrans (fun i => Injective.ι (F.obj i))
    have (i : Discrete I) : Mono (j.app i) := by
      dsimp [j]
      infer_instance
    exact ⟨⟨J, injective_discrete_of_obj J hJ, j, NatTrans.mono_of_mono_app j⟩⟩

end CategoryTheory
