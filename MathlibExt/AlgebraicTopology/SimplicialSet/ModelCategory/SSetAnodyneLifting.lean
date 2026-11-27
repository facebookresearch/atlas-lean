/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-! # Lifting consequences of anodyne extensions

This module packages two generic facts that follow directly from the definition
`SSet.anodyneExtensions = (fibrations SSet).llp` in Mathlib v4.33.

* An anodyne map has the left lifting property against any Kan fibration.
  This is immediate from unfolding `MorphismProperty.llp`.

* Any map into a fibrant simplicial set extends across an anodyne morphism.
  The square with the terminal projection is filled using the previous lifting
  property; commutativity of the square holds by terminal uniqueness.

Both results are category-theoretically reusable within simplicial model-structure
constructions and avoid any horn/product, cylinder, or weak-equivalence input.
-/

@[expose] public section

universe u

open CategoryTheory Limits HomotopicalAlgebra SSet
open scoped SSet.modelCategoryQuillen

namespace SSet

namespace anodyneExtensions

/-- An anodyne extension has the left lifting property against any Kan fibration.

This is the unfolding of `SSet.anodyneExtensions = (fibrations _).llp`:
if `f` is anodyne and `p` is a fibration, every commutative square from `f` to `p`
admits a diagonal filler. -/
lemma hasLeftLiftingProperty {A B : SSet.{u}} {f : A ⟶ B}
    (hf : SSet.anodyneExtensions f) {X Y : SSet.{u}} (p : X ⟶ Y)
    [Fibration p] : HasLiftingProperty f p :=
  hf p (HomotopicalAlgebra.mem_fibrations p)

/-- Extension of a map into a fibrant object across an anodyne morphism.

Given `f : A ⟶ X` with `X` fibrant (`IsFibrant X`) and an anodyne map `g : A ⟶ B`,
there exists `h : B ⟶ X` with `g ≫ h = f`. The proof fills the commutative square
with left side `g`, right side `terminal.from X` (a fibration by fibrancy),
top `f`, bottom `terminal.from B`, using `hasLeftLiftingProperty`. -/
lemma exists_lift_of_isFibrant {A B X : SSet.{u}} (f : A ⟶ X)
    [IsFibrant X] {g : A ⟶ B} (hg : SSet.anodyneExtensions g) :
    ∃ h : B ⟶ X, g ≫ h = f := by
  have hlp : HasLiftingProperty g (terminal.from X) :=
    hasLeftLiftingProperty hg (terminal.from X)
  have sq : CommSq f g (terminal.from X) (terminal.from B) :=
    ⟨Subsingleton.elim _ _⟩
  obtain ⟨⟨h, h_left, _⟩⟩ := (hlp.sq_hasLift sq).exists_lift
  exact ⟨h, h_left⟩

end anodyneExtensions

end SSet
