/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian

/-!
# Cofibered categories

This file packages the strong-cocartesian-lift formulation of a cofibered
category.  A functor is cofibered when every arrow out of the image of an
object admits a strongly cocartesian lift.  Strongly cocartesian arrows
compose by Mathlib's existing API, so this is the compact dual formulation
of a fibered category needed by categorical homology constructions.

The namespace also exposes chosen pushforward objects and arrows.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {S : Type u₁} {X : Type u₂}
  [Category.{v₁} S] [Category.{v₂} X]

/-- A functor is cofibered when every base arrow out of the image of an
object has a strongly cocartesian lift. -/
class Functor.IsCofibered (p : X ⥤ S) : Prop where
  exists_isStronglyCocartesian' {a : X} {T : S}
      (f : p.obj a ⟶ T) :
    ∃ (b : X) (phi : a ⟶ b), p.IsStronglyCocartesian f phi

/-- A strongly cocartesian lift with a propositionally identified source
in the base. -/
protected lemma Functor.IsCofibered.exists_isStronglyCocartesian
    (p : X ⥤ S) [p.IsCofibered]
    {a : X} {R T : S} (ha : p.obj a = R) (f : R ⟶ T) :
    ∃ (b : X) (phi : a ⟶ b), p.IsStronglyCocartesian f phi := by
  subst ha
  exact Functor.IsCofibered.exists_isStronglyCocartesian' f

namespace Functor.IsCofibered

variable {p : X ⥤ S} [p.IsCofibered]
  {a : X} {R T : S} (ha : p.obj a = R) (f : R ⟶ T)

/-- A chosen codomain for a strongly cocartesian lift. -/
noncomputable def pushforwardObj : X :=
  Classical.choose
    (Functor.IsCofibered.exists_isStronglyCocartesian p ha f)

/-- A chosen strongly cocartesian lift. -/
noncomputable def pushforwardMap :
    a ⟶ pushforwardObj ha f :=
  Classical.choose
    (Classical.choose_spec
      (Functor.IsCofibered.exists_isStronglyCocartesian p ha f))

instance pushforwardMap_isStronglyCocartesian :
    p.IsStronglyCocartesian f (pushforwardMap ha f) :=
  Classical.choose_spec
    (Classical.choose_spec
      (Functor.IsCofibered.exists_isStronglyCocartesian p ha f))

/-- The chosen pushforward object lies over the target of the base arrow. -/
theorem pushforwardObj_proj : p.obj (pushforwardObj ha f) = T :=
  IsHomLift.codomain_eq p f (pushforwardMap ha f)

end Functor.IsCofibered

end CategoryTheory

end
