/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterTerminalComparison
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.CategoryTheory.LiftingProperties.Over

/-!
# Native original inner-anodyne parameter comparisons

For the same original marked source map with an inner-anodyne underlying
map, each monic parameter gives an actual underlying inner-anodyne
pushout-product. The full original square therefore lifts into every
maximally marked inner fibration. The actual slice adjunction converts
these whole lifts to boundary right lifting of the original unmarked
fixed-base mapping restriction. No base Kan or marked-model assumption
is used.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The actual whole underlying slice parameter map is inner anodyne for the original inner-anodyne source
  and monic parameter. -/
theorem overParameterPushoutProduct_underlying_innerAnodyne {Z : Marked.{u}}
    {A D : SSet.{u}} {X Y : Over Z} (a : A ⟶ D) [Mono a] (f : X ⟶ Y)
    (hf : innerAnodyneExtensions f.left.hom) :
    innerAnodyneExtensions (overParameterPushoutProduct a f).left.hom :=
  innerAnodyneExtensions_pushoutObjObjι
    (underlyingParameterSquare (overParameterUnderlyingPushout a f)).flip hf

/-- Each original parameter comparison lifts, with its whole base equation, into the maximally marked
  original inner fibration. -/
theorem overParameterPushoutProduct_maximal_inner_lifting {A D E B : SSet.{u}}
    (a : A ⟶ D) [Mono a] {X Y : Over (max B)} (f : X ⟶ Y)
    (hf : innerAnodyneExtensions f.left.hom) (p : E ⟶ B) [InnerFibration p] :
    HasLiftingProperty (overParameterPushoutProduct a f)
      (Over.mkIdTerminal.from (Over.mk (maximal.map p))) := by
  let i := overParameterPushoutProduct a f
  let q : max E ⟶ max B := maximal.map p
  let T : Over (max B) := Over.mk q
  let r : T ⟶ Over.mk (𝟙 (max B)) := Over.mkIdTerminal.from T
  let _ : HasLiftingProperty i.left.hom p :=
    overParameterPushoutProduct_underlying_innerAnodyne a f hf p InnerFibration.mem
  let _ : HasLiftingProperty i.left q :=
    (maximalAdjunction.hasLiftingProperty_iff i.left p).mp
      (inferInstanceAs (HasLiftingProperty i.left.hom p))
  have hr : r.left = q := Over.mkIdTerminal_from_left T
  let hq : HasLiftingProperty i.left q := inferInstance
  let _ : HasLiftingProperty i.left r.left := hr.symm ▸ hq
  exact HasLiftingProperty.over i r

/-- The actual original maximal-target relative mapping restriction along an underlying inner-anodyne source
  map has all boundary lifts. -/
theorem overMapping_maximalTarget_innerAnodyne_rlp {E B : SSet.{u}}
    {X Y : Over (max B)} (f : X ⟶ Y) (hf : innerAnodyneExtensions f.left.hom)
    (p : E ⟶ B) [InnerFibration p] :
    modelCategoryQuillen.I.{u}.rlp
      ((overMappingFunctor .maximal (max B) (Over.mk (maximal.map p))).map f.op) := by
  apply (overParameterBoundary_terminal_lifting_iff f (Over.mk (maximal.map p))).mp
  intro n
  exact overParameterPushoutProduct_maximal_inner_lifting _ f hf p

end SSet.Marked
