/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Functor.SmallIndex
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Small Index
-/

set_option autoImplicit false
noncomputable section

universe w uD vD uM vM

open CategoryTheory

section IndependentUniverses

variable (D : Type uD) [Category.{vD} D] (M : Type uM) [Category.{vM} M]


example (s : Functor.EssentialIndexData.{w} D M) {F G : D ⥤ M}
    {α β : F ⟶ G}
    (h : ∀ d : s.index, α.app (s.equivalence.inverse.obj d) =
      β.app (s.equivalence.inverse.obj d)) : α = β :=
  s.component_ext h

end IndependentUniverses

example : Functor.EssentialIndexData.{0} (Discrete PEmpty) (Type) :=
  Functor.EssentialIndexData.ofEssentiallySmall

example : Functor.EssentialIndexData.{0} (Discrete ℕ) (Type) :=
  Functor.EssentialIndexData.ofEssentiallySmall

/- The original object carrier can live strictly above the working universe. -/
example : Functor.EssentialIndexData.{0} (Discrete (ULift.{1} Bool)) (Type) :=
  Functor.EssentialIndexData.ofEssentiallySmall

section OriginalComponents

variable (D : Type uD) [Category.{vD} D] (M : Type uM) [Category.{vM} M]
variable (s : Functor.EssentialIndexData.{w} D M)

example {F G : D ⥤ M} (α : F ⟶ G) (d : s.index) :
    (((s.equivalence.congrLeft (E := M)).functor).map α).app d =
      α.app (s.equivalence.inverse.obj d) := s.small_component α d

example {F G : s.index ⥤ M} (α : F ⟶ G) (d : D) :
    (((s.equivalence.congrLeft (E := M)).inverse).map α).app d =
      α.app (s.equivalence.functor.obj d) := s.original_component α d

end OriginalComponents
