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

import MathlibExt.CategoryTheory.Operad.Colored.OperadObj.Indexing

/-!
# Focused O7E colored indexing public-contract packet

Pins the stable downstream-facing contracts for colored operadic
substitution indexing: the factor/source/target functors and their
object/morphism computation laws.
-/

open CategoryTheory
open CategoryTheory.Operad

universe w v u

variable {Color : Type u} {V : Type w} [Category.{v} V]

-- Factor functor signature.
noncomputable example (O : ColoredSymmetricCollection Color V) :
    ColoredSubstitutionData Color ⥤ FiniteFamily V :=
  ColoredOperadObj.substitutionFactors O

-- Factor object computation at the outer index.
example (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) :
    ((ColoredOperadObj.substitutionFactors O).obj d).obj
        (ColoredOperadObj.substitutionFactorsOuterIndex O d) =
      O.obj d.outerProfile :=
  ColoredOperadObj.substitutionFactors_obj_outer O d

-- Factor object computation at inner indices.
example (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) (i : d.inner.index) :
    ((ColoredOperadObj.substitutionFactors O).obj d).obj
        (ColoredOperadObj.substitutionFactorsInnerIndex O d i) =
      O.obj (d.inner.obj i) :=
  ColoredOperadObj.substitutionFactors_obj_inner O d i

-- Factor morphism index computation.
example (O : ColoredSymmetricCollection Color V)
    {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    ((ColoredOperadObj.substitutionFactors O).map f).equiv =
      Equiv.optionCongr f.innerHom.equiv :=
  ColoredOperadObj.substitutionFactors_map_equiv O f

-- Factor morphism computation at the outer index.
example (O : ColoredSymmetricCollection Color V)
    {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    ((ColoredOperadObj.substitutionFactors O).map f).hom
        (ColoredOperadObj.substitutionFactorsOuterIndex O d) =
      O.map (ColoredSubstitutionData.outerProfileMap f) :=
  ColoredOperadObj.substitutionFactors_map_outer O f

-- Factor morphism computation at inner indices.
example (O : ColoredSymmetricCollection Color V)
    {d e : ColoredSubstitutionData Color} (f : d ⟶ e)
    (i : d.inner.index) :
    ((ColoredOperadObj.substitutionFactors O).map f).hom
        (ColoredOperadObj.substitutionFactorsInnerIndex O d i) =
      O.map (f.innerHom.hom i) :=
  ColoredOperadObj.substitutionFactors_map_inner O f i

variable [FiniteTensor V]

-- Source functor signature.
noncomputable example (O : ColoredSymmetricCollection Color V) :
    ColoredSubstitutionData Color ⥤ V :=
  ColoredOperadObj.substitutionSource O

-- Target functor signature.
noncomputable example (O : ColoredSymmetricCollection Color V) :
    ColoredSubstitutionData Color ⥤ V :=
  ColoredOperadObj.substitutionTarget O

-- Source object computation.
example (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) :
    (ColoredOperadObj.substitutionSource O).obj d =
      (FiniteTensor.tensor (V := V)).obj
        ((ColoredOperadObj.substitutionFactors O).obj d) :=
  ColoredOperadObj.substitutionSource_obj O d

-- Target object computation.
example (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) :
    (ColoredOperadObj.substitutionTarget O).obj d = O.obj d.totalProfile :=
  ColoredOperadObj.substitutionTarget_obj O d

-- Source morphism computation.
example (O : ColoredSymmetricCollection Color V)
    {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (ColoredOperadObj.substitutionSource O).map f =
      (FiniteTensor.tensor (V := V)).map
        ((ColoredOperadObj.substitutionFactors O).map f) :=
  ColoredOperadObj.substitutionSource_map O f

-- Target morphism computation.
example (O : ColoredSymmetricCollection Color V)
    {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (ColoredOperadObj.substitutionTarget O).map f =
      O.map (ColoredSubstitutionData.totalProfileFunctor.map f) :=
  ColoredOperadObj.substitutionTarget_map O f
