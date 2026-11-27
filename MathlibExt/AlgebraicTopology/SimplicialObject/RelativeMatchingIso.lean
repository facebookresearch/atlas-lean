/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatching
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Identity and degree-zero relative matching arrows
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The relative matching arrow of an identity is isomorphic to the identity component. -/
noncomputable def relativeMatchingMapIdArrowIso
    (X : SimplicialObject C) (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C]
    [HasPullback (matchingMap X n)
      ((matchingObjectFunctor n).map (𝟙 X))] :
    Arrow.mk (relativeMatchingMap (𝟙 X) n) ≅
      Arrow.mk (𝟙 (X.obj (op ⦋n⦌))) := by
  let _ : IsIso ((matchingObjectFunctor n).map (𝟙 X)) := inferInstance
  let p := pullback.fst (matchingMap X n)
    ((matchingObjectFunctor n).map (𝟙 X))
  let _ : IsIso p := inferInstance
  exact Arrow.isoMk (Iso.refl _) (asIso p) (by simp [p])

/-- In degree zero, the relative matching arrow is isomorphic to the degree-zero component. -/
noncomputable def relativeMatchingMapZeroArrowIso
    [HasTerminal C]
    {X Y : SimplicialObject C} (f : X ⟶ Y)
    [HasLimitsOfShape (matchingIndex 0) C]
    [HasPullback (matchingMap Y 0)
      ((matchingObjectFunctor 0).map f)] :
    Arrow.mk (relativeMatchingMap f 0) ≅
      Arrow.mk (f.app (op ⦋0⦌)) := by
  let hX : IsTerminal (matchingObject X 0) :=
    terminalIsTerminal.ofIso (matchingObjectZeroIso X).symm
  let hY : IsTerminal (matchingObject Y 0) :=
    terminalIsTerminal.ofIso (matchingObjectZeroIso Y).symm
  let _ : IsIso ((matchingObjectFunctor 0).map f) :=
    isIso_of_isTerminal hX hY _
  let p := pullback.fst (matchingMap Y 0)
    ((matchingObjectFunctor 0).map f)
  let _ : IsIso p := inferInstance
  exact Arrow.isoMk (Iso.refl _) (asIso p) (by simp [p])

end CategoryTheory.SimplicialObject
