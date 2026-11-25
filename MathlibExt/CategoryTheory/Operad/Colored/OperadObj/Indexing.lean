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

public import MathlibExt.CategoryTheory.Operad.Colored.SubstitutionAssociativity

/-!
# Indexing functors for colored operadic substitution

For a colored symmetric collection `O`, a substitution datum determines a finite family containing
the outer operation and all inner operations. Tensoring that family gives the source of operadic
substitution, while evaluation at the flattened profile gives its target.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe w v u

namespace ColoredOperadObj

variable {Color : Type u} {V : Type w} [Category.{v} V]

/-- The outer operation and all inner operations associated to a substitution datum. -/
def substitutionFactors (O : ColoredSymmetricCollection Color V) :
    ColoredSubstitutionData Color ⥤ FiniteFamily V :=
  ColoredSubstitutionData.factorFamilyFunctor ⋙ FiniteFamily.map O

/-- The index of the outer operation in `substitutionFactors`. -/
def substitutionFactorsOuterIndex (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) : ((substitutionFactors O).obj d).index :=
  ColoredSubstitutionData.factorOuterIndex d

/-- The index of an inner operation in `substitutionFactors`. -/
def substitutionFactorsInnerIndex (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) (i : d.inner.index) :
    ((substitutionFactors O).obj d).index :=
  ColoredSubstitutionData.factorInnerIndex d i

@[simp]
theorem substitutionFactors_obj_outer (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) :
    ((substitutionFactors O).obj d).obj (substitutionFactorsOuterIndex O d) =
      O.obj d.outerProfile :=
  rfl

@[simp]
theorem substitutionFactors_obj_inner (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) (i : d.inner.index) :
    ((substitutionFactors O).obj d).obj (substitutionFactorsInnerIndex O d i) =
      O.obj (d.inner.obj i) :=
  rfl

@[simp]
theorem substitutionFactors_map_equiv (O : ColoredSymmetricCollection Color V)
    {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    ((substitutionFactors O).map f).equiv = Equiv.optionCongr f.innerHom.equiv :=
  rfl

@[simp]
theorem substitutionFactors_map_outer (O : ColoredSymmetricCollection Color V)
    {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    ((substitutionFactors O).map f).hom (substitutionFactorsOuterIndex O d) =
      O.map (ColoredSubstitutionData.outerProfileMap f) :=
  rfl

@[simp]
theorem substitutionFactors_map_inner (O : ColoredSymmetricCollection Color V)
    {d e : ColoredSubstitutionData Color} (f : d ⟶ e) (i : d.inner.index) :
    ((substitutionFactors O).map f).hom (substitutionFactorsInnerIndex O d i) =
      O.map (f.innerHom.hom i) :=
  rfl

/-- Source of colored operadic substitution: the tensor of the outer and inner operations. -/
def substitutionSource [FiniteTensor V] (O : ColoredSymmetricCollection Color V) :
    ColoredSubstitutionData Color ⥤ V :=
  substitutionFactors O ⋙ FiniteTensor.tensor

/-- Target of colored operadic substitution: evaluation at the flattened profile. -/
def substitutionTarget (O : ColoredSymmetricCollection Color V) :
    ColoredSubstitutionData Color ⥤ V :=
  ColoredSubstitutionData.totalProfileFunctor ⋙ O

@[simp]
theorem substitutionSource_obj [FiniteTensor V] (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) :
    (substitutionSource O).obj d =
      (FiniteTensor.tensor (V := V)).obj ((substitutionFactors O).obj d) :=
  rfl

@[simp]
theorem substitutionTarget_obj (O : ColoredSymmetricCollection Color V)
    (d : ColoredSubstitutionData Color) :
    (substitutionTarget O).obj d = O.obj d.totalProfile :=
  rfl

@[simp]
theorem substitutionSource_map [FiniteTensor V] (O : ColoredSymmetricCollection Color V)
    {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (substitutionSource O).map f =
      (FiniteTensor.tensor (V := V)).map ((substitutionFactors O).map f) :=
  rfl

@[simp]
theorem substitutionTarget_map (O : ColoredSymmetricCollection Color V)
    {d e : ColoredSubstitutionData Color} (f : d ⟶ e) :
    (substitutionTarget O).map f = O.map (ColoredSubstitutionData.totalProfileFunctor.map f) :=
  rfl

end ColoredOperadObj

end CategoryTheory.Operad
