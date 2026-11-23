/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.GroupCompletion
public import MathlibExt.CategoryTheory.ClassifyingSpace.PointedCGWH
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Native CGWH realization of additive S⁻¹S

This file places the additive `S⁻¹S` category at the canonical realization
boundary.  Its classifying space is CGWH-valued, pointed at `(0,0)`, and the
canonical core inclusion realizes to a strictly pointed CGWH map.

No TopCat reconstruction, group-completion homology theorem, or comparison
with Quillen `Q` is asserted here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe w v u

namespace CategoryTheory
namespace SInverseS

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

/-- The additive `S⁻¹S` classifying space in CGWH. -/
noncomputable def classifyingSpace : CGWH.{w, max u v} :=
  CategoryTheory.classifyingSpaceCGWH.{w, max v u, u}.obj
    (Cat.of (Pair C))

/-- The additive `S⁻¹S` classifying space pointed at `(0,0)`. -/
noncomputable def pointedClassifyingSpace : PointedCGWH.{w, max u v} :=
  CategoryTheory.classifyingSpaceCGWHPointed.{w}
    (⟨0, 0⟩ : Pair C)

/-- Realization of the canonical `Core(C) ⟶ S⁻¹S` inclusion. -/
noncomputable def liftedCoreInclusion :
    ULiftHom.{max v u} (Core C) ⥤ Pair C :=
  ULiftHom.down ⋙ coreInclusion

/-- Realization of the canonical core inclusion.  `ULiftHom` only raises
the morphism universe so source and target are objects of the same `Cat`. -/
noncomputable def coreClassifyingSpaceMap :
    CategoryTheory.classifyingSpaceCGWH.{w, max v u, u}.obj
        (Cat.of (ULiftHom.{max v u} (Core C))) ⟶
      classifyingSpace.{w} C :=
  CategoryTheory.classifyingSpaceCGWH.{w, max v u, u}.map
    (liftedCoreInclusion (C := C)).toCatHom

/-- The realized core inclusion as a strictly pointed CGWH map. -/
noncomputable def pointedCoreClassifyingSpaceMap :
    CategoryTheory.classifyingSpaceCGWHPointed.{w}
        (ULiftHom.objUp (⟨0⟩ : Core C) :
          ULiftHom.{max v u} (Core C)) ⟶
      pointedClassifyingSpace.{w} C :=
  Under.homMk (coreClassifyingSpaceMap.{w} C) (by
    exact CategoryTheory.classifyingSpaceCGWH_basepointMap_naturality
      (liftedCoreInclusion (C := C))
      (ULiftHom.objUp (⟨0⟩ : Core C) :
        ULiftHom.{max v u} (Core C)))

@[simp]
theorem pointedCoreClassifyingSpaceMap_right :
    (pointedCoreClassifyingSpaceMap.{w} C).right =
      coreClassifyingSpaceMap.{w} C :=
  rfl

/-- The native CGWH classifying space of the categorical identity
component. -/
noncomputable def zeroComponentClassifyingSpace :
    CGWH.{w, max u v} :=
  CategoryTheory.classifyingSpaceCGWH.{w, max v u, u}.obj
    (Cat.of (ZeroComponent (C := C)))

/-- The identity-component classifying space with its selected basepoint. -/
noncomputable def pointedZeroComponentClassifyingSpace :
    PointedCGWH.{w, max u v} :=
  CategoryTheory.classifyingSpaceCGWHPointed.{w}
    (zeroComponentBaseObject (C := C))

/-- The identity component includes into the full additive `S⁻¹S`
classifying space. -/
noncomputable def zeroComponentClassifyingSpaceInclusion :
    zeroComponentClassifyingSpace.{w} C ⟶ classifyingSpace.{w} C :=
  CategoryTheory.classifyingSpaceCGWH.{w, max v u, u}.map
    (zeroComponentProperty (C := C)).ι.toCatHom

/-- The identity-component inclusion as a strictly pointed CGWH map. -/
noncomputable def pointedZeroComponentClassifyingSpaceInclusion :
    pointedZeroComponentClassifyingSpace.{w} C ⟶
      pointedClassifyingSpace.{w} C :=
  Under.homMk (zeroComponentClassifyingSpaceInclusion.{w} C) (by
    exact CategoryTheory.classifyingSpaceCGWH_basepointMap_naturality
      (zeroComponentProperty (C := C)).ι
      (zeroComponentBaseObject (C := C)))

@[simp]
theorem pointedZeroComponentClassifyingSpaceInclusion_right :
    (pointedZeroComponentClassifyingSpaceInclusion.{w} C).right =
      zeroComponentClassifyingSpaceInclusion.{w} C :=
  rfl

end SInverseS
end CategoryTheory
