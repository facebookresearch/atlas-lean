/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Whiskering

/-!
# Composing functor comparison isomorphisms

Composes natural isomorphisms commuting a functor with each of two endofunctors. The resulting isomorphism commutes the functor with their composite, retaining the given comparison components and maps.
-/

set_option autoImplicit false
noncomputable section
universe u v u' v'
open CategoryTheory

namespace CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The full original two-factor comparison retains both natural isomorphisms and all maps. -/
def originalBifibrantComparison (Q R : C ⥤ C) (Q' R' : D ⥤ D) (F : C ⥤ D)
    (cQ : Q ⋙ F ≅ F ⋙ Q') (cR : R ⋙ F ≅ F ⋙ R') :
    (Q ⋙ R) ⋙ F ≅ F ⋙ (Q' ⋙ R') :=
  Functor.isoWhiskerLeft Q cR ≪≫ Functor.isoWhiskerRight cQ R'

end CategoryTheory
