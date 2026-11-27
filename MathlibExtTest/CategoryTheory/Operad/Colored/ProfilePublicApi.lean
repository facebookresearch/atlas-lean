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

import MathlibExt.CategoryTheory.Operad.Colored.Profile

/-!
# Focused O7E colored-profile public-contract packet

Pins the stable downstream-facing contracts for finite colored
profiles: profile constructors with their input/output
computations, reindexing and color maps with functoriality, the
hom structure with identity/composition/inverse, the groupoid
instance with categorical projections, reindex homs, and the
color-map and arity functors.
-/

open CategoryTheory
open CategoryTheory.Operad

universe u v

variable {Color : Type u} {Color' : Type v}

-- The nullary profile has the specified output color.
example (c : Color) :
    (ColoredProfile.nullary c).outputColor = c :=
  rfl

-- The unary profile exposes its input and output colors.
example (a b : Color) (i : (ColoredProfile.unary a b).inputs) :
    (ColoredProfile.unary a b).inputColor i = a ∧
      (ColoredProfile.unary a b).outputColor = b :=
  ⟨rfl, rfl⟩

-- Color maps preserve inputs and transform colors.
example (f : Color → Color') (P : ColoredProfile Color) :
    (P.mapColors f).inputs = P.inputs ∧
      (P.mapColors f).outputColor = f P.outputColor :=
  ⟨ColoredProfile.mapColors_inputs f P,
    ColoredProfile.mapColors_outputColor f P⟩

-- Color maps compose.
example {Color'' : Type*} (f : Color → Color')
    (g : Color' → Color'') (P : ColoredProfile Color) :
    (P.mapColors f).mapColors g = P.mapColors (g ∘ f) :=
  ColoredProfile.mapColors_comp f g P

-- Reindexing swaps in the new index type.
example (P : ColoredProfile Color) (J : FintypeCat.{0})
    (e : J ≃ P.inputs) :
    (P.reindex J e).inputs = J ∧
      (P.reindex J e).outputColor = P.outputColor :=
  ⟨ColoredProfile.reindex_inputs P J e,
    ColoredProfile.reindex_outputColor P J e⟩

-- Reindexing composes by transposing equivalences.
example (P : ColoredProfile Color) (J K : FintypeCat.{0})
    (e : J ≃ P.inputs) (f : K ≃ J) :
    (P.reindex J e).reindex K f = P.reindex K (f.trans e) :=
  ColoredProfile.reindex_trans P J K e f

-- Profile hom composition acts by equivalence transitivity.
example {P Q R : ColoredProfile Color} (f : P ⟶ Q)
    (g : Q ⟶ R) :
    (f ≫ g).inputEquiv = f.inputEquiv.trans g.inputEquiv :=
  ColoredProfile.comp_inputEquiv f g

-- Profile hom inversion acts by equivalence symmetry.
example {P Q : ColoredProfile Color} (f : P ⟶ Q) :
    (Groupoid.inv f).inputEquiv = f.inputEquiv.symm :=
  ColoredProfile.inv_inputEquiv f

-- The canonical reindex hom exposes the equivalence.
example (P : ColoredProfile Color) (J : FintypeCat.{0})
    (e : J ≃ P.inputs) :
    (P.reindexHom J e).inputEquiv = e :=
  ColoredProfile.reindexHom_inputEquiv P J e

-- Reindex homs compose by transposing equivalences.
example (P : ColoredProfile Color) (J K : FintypeCat.{0})
    (e : J ≃ P.inputs) (f : K ≃ J) :
    (P.reindex J e).reindexHom K f ≫ P.reindexHom J e =
      P.reindexHom K (f.trans e) :=
  ColoredProfile.reindexHom_trans P J K e f

-- Color maps are functorial on objects.
example (f : Color → Color') (P : ColoredProfile Color) :
    (ColoredProfile.mapColorsFunctor f).obj P = P.mapColors f :=
  ColoredProfile.mapColorsFunctor_obj f P

-- Color-map functors compose.
example {Color'' : Type*} (f : Color → Color')
    (g : Color' → Color'') :
    ColoredProfile.mapColorsFunctor f ⋙
        ColoredProfile.mapColorsFunctor g =
      ColoredProfile.mapColorsFunctor (g ∘ f) :=
  ColoredProfile.mapColorsFunctor_comp f g

-- The arity functor forgets colors on objects.
example (P : ColoredProfile Color) :
    (ColoredProfile.arityFunctor Color).obj P = ⟨P.inputs⟩ :=
  ColoredProfile.arityFunctor_obj Color P

-- The arity functor maps homs through input equivalences.
example {P Q : ColoredProfile Color} (f : P ⟶ Q) :
    (ColoredProfile.arityFunctor Color).map f =
      FinBijGroupoid.homOfEquiv f.inputEquiv :=
  ColoredProfile.arityFunctor_map f

-- The identity profile equivalence is the categorical identity.
example (P : ColoredProfile Color) :
    ColoredProfile.Hom.refl P = 𝟙 P :=
  ColoredProfile.Hom.refl_eq_id P

-- A heterogeneously-identity prefix cancels under composition.
example {A B C P : ColoredProfile Color} {a : A ⟶ B} {b : B ⟶ C}
    (h : HEq a (ColoredProfile.Hom.refl P)) (hA : A = P) (hB : B = P) :
    HEq (ColoredProfile.Hom.trans a b) b :=
  ColoredProfile.Hom.trans_heq_cancel h hA hB
