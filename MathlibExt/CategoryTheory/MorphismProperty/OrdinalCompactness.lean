/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Order.WellFounded

/-!
# Source Hom preservation on ordinal diagrams

The specified morphism class controls the actual transitions of each bottomed
well-ordered diagram. Both endpoints of a generating arrow retain the same
source Hom comparison. No continuity or model category structure is required.
-/

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory Limits Opposite

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C]

/-- Source Hom preserves the actual colimit of each bottomed well-ordered
diagram whose transitions lie in P. Continuity is not assumed. -/
def PreservesOrdinalColimits (P : MorphismProperty C) (A : C) : Prop :=
  ∀ (O : Type w) [LinearOrder O] [OrderBot O] [WellFoundedLT O] (F : O ⥤ C),
    (∀ (i j : O) (f : i ⟶ j), P (F.map f)) →
      PreservesColimit F (coyoneda.obj (Opposite.op A))

/-- The original generating arrows retain both endpoint source-Hom
comparisons on the actual ordinal transition class. -/
structure SourceHomPreservation (I P : MorphismProperty C) : Prop where
  domains (i : I.toSet) : PreservesOrdinalColimits.{u, v, w} P i.1.left
  codomains (i : I.toSet) : PreservesOrdinalColimits.{u, v, w} P i.1.right

end CategoryTheory.MorphismProperty
