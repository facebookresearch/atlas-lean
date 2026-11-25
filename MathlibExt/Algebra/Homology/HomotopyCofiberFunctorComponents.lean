/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- SOURCE-ONLY native additive-functor cofiber component bridge; Native has not been run.
module

public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# Original cofiber map components under an additive functor

The existing native additive-functor cofiber isomorphism returns every
actual cofiber morphism with its original source and target inclusion
components. These formulas use the native cofiber, with arbitrary category
and complex-shape worlds, and no caller compatibility certificate.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD w

namespace HomologicalComplex.homotopyCofiber

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasBinaryBiproducts D]
  {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  (H : C ⥤ D) [H.Additive]
  {F G K : HomologicalComplex C c} (φ : F ⟶ G) (q : homotopyCofiber φ ⟶ K)

/-- The native transported cofiber map retains its actual shifted-source component. -/
@[reassoc]
theorem inlX_mapHomologicalComplexObjIso_inv_comp (i j : ι) (hji : c.Rel j i) :
    inlX ((H.mapHomologicalComplex c).map φ) i j hji ≫
      ((mapHomologicalComplexObjIso φ H).inv ≫ (H.mapHomologicalComplex c).map q).f j =
    H.map (inlX φ i j hji ≫ q.f j) := by
  change inlX ((H.mapHomologicalComplex c).map φ) i j hji ≫
      (mapHomologicalComplexObjXIso φ H j).inv ≫ H.map (q.f j) = _
  rw [inlX_mapHomologicalComplexObjXIso_inv_assoc, H.map_comp]

/-- The native transported cofiber map retains its actual target component. -/
@[reassoc]
theorem inrX_mapHomologicalComplexObjIso_inv_comp (i : ι) :
    inrX ((H.mapHomologicalComplex c).map φ) i ≫
      ((mapHomologicalComplexObjIso φ H).inv ≫ (H.mapHomologicalComplex c).map q).f i =
    H.map (inrX φ i ≫ q.f i) := by
  change inrX ((H.mapHomologicalComplex c).map φ) i ≫
      (mapHomologicalComplexObjXIso φ H i).inv ≫ H.map (q.f i) = _
  rw [inrX_mapHomologicalComplexObjXIso_inv_assoc, H.map_comp]

end HomologicalComplex.homotopyCofiber

end
