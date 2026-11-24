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

import MathlibExt.CategoryTheory.Operad.Colored.Collection

/-!
# Focused O7E colored-collection public-contract packet

Pins the stable downstream-facing contracts for colored symmetric
collections: evaluation, relabeling along profile maps with the
relabel iso and its hom/inv projections, the identity and
composition laws, and color restriction with object/map
computations plus identity/composition functor laws.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u v w

variable {Color Color' : Type u} {V : Type w} [Category.{v} V]

-- Evaluation is functor application.
example (X : ColoredSymmetricCollection Color V)
    (P : ColoredProfile Color) :
    X.eval P = X.obj P :=
  rfl

-- The relabel iso projects to the relabel map.
example (X : ColoredSymmetricCollection Color V)
    {P Q : ColoredProfile Color} (e : P ⟶ Q) :
    (X.relabelIso e).hom = X.relabel e :=
  X.relabelIso_hom e

-- The relabel iso inverse relabels along the inverse map.
example (X : ColoredSymmetricCollection Color V)
    {P Q : ColoredProfile Color} (e : P ⟶ Q) :
    (X.relabelIso e).inv = X.relabel (Groupoid.inv e) :=
  X.relabelIso_inv e

-- Relabeling along identity is the identity.
example (X : ColoredSymmetricCollection Color V)
    (P : ColoredProfile Color) :
    X.relabel (𝟙 P) = 𝟙 (X.eval P) :=
  X.relabel_id P

-- Relabeling respects composition.
example (X : ColoredSymmetricCollection Color V)
    {P Q R : ColoredProfile Color} (e : P ⟶ Q) (f : Q ⟶ R) :
    X.relabel (e ≫ f) = X.relabel e ≫ X.relabel f :=
  X.relabel_comp e f

-- Restriction acts on objects by color pushforward.
example (f : Color → Color')
    (X : ColoredSymmetricCollection Color' V)
    (P : ColoredProfile Color) :
    (ColoredSymmetricCollection.restrictColors f X).obj P =
      X.obj (P.mapColors f) :=
  ColoredSymmetricCollection.restrictColors_obj f X P

-- Restriction acts on maps by color pushforward.
example (f : Color → Color')
    (X : ColoredSymmetricCollection Color' V)
    {P Q : ColoredProfile Color} (e : P ⟶ Q) :
    (ColoredSymmetricCollection.restrictColors f X).map e =
      X.map (e.mapColors f) :=
  ColoredSymmetricCollection.restrictColors_map f X e

-- Restriction at identity is the identity.
example (X : ColoredSymmetricCollection Color V) :
    ColoredSymmetricCollection.restrictColors id X = X :=
  ColoredSymmetricCollection.restrictColors_id X

-- Restriction composes contravariantly.
example {Color'' : Type u} (f : Color → Color')
    (g : Color' → Color'')
    (X : ColoredSymmetricCollection Color'' V) :
    ColoredSymmetricCollection.restrictColors f
        (ColoredSymmetricCollection.restrictColors g X) =
      ColoredSymmetricCollection.restrictColors (g ∘ f) X :=
  ColoredSymmetricCollection.restrictColors_comp f g X

-- Collection evaluation of the identity profile equivalence is the identity.
example (X : ColoredSymmetricCollection Color V) (P : ColoredProfile Color) :
    X.map (ColoredProfile.Hom.refl P) = 𝟙 (X.obj P) :=
  ColoredSymmetricCollection.relabel_refl X P
