/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology and opcycles maps under functors

Preservation of the homology data of a particular short complex gives
canonical homology and opcycles comparison maps. Their characteristic
formulas describe the cycle inclusions and quotient projections. Global
abelian, finite-limit and finite-colimit preservation assumptions are
unnecessary.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.ShortComplex

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

/-- The canonical mapped opcycles comparison carries the original quotient map. -/
@[reassoc]
theorem pOpcycles_comp_mapOpcyclesIso_hom (S : ShortComplex C)
    [S.HasRightHomology] (U : C ⥤ D) [U.PreservesZeroMorphisms]
    [U.PreservesRightHomologyOf S] :
    (S.map U).pOpcycles ≫ (S.mapOpcyclesIso U).hom = U.map S.pOpcycles := by
  change (S.map U).pOpcycles ≫ (S.rightHomologyData.map U).opcyclesIso.hom = _
  rw [RightHomologyData.pOpcycles_comp_opcyclesIso_hom,
    RightHomologyData.map_p]
  rfl

/-- The canonical homology comparison commutes with inclusion into opcycles. -/
@[reassoc]
theorem mapHomologyIso_hom_comp_homologyι (S : ShortComplex C)
    [S.HasHomology] (U : C ⥤ D) [U.PreservesZeroMorphisms]
    [(S.map U).HasHomology] [U.PreservesLeftHomologyOf S]
    [U.PreservesRightHomologyOf S] :
    (S.mapHomologyIso U).hom ≫ U.map S.homologyι =
      (S.map U).homologyι ≫ (S.mapOpcyclesIso U).hom := by
  let h := S.homologyData.right
  have hH := congrArg Iso.hom (h.mapHomologyIso'_eq U)
  have hO := congrArg Iso.hom (h.mapOpcyclesIso_eq U)
  have hι := (h.map U).homologyIso_hom_comp_ι
  dsimp only [RightHomologyData.map, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom] at hH hO hι
  rw [← S.mapHomologyIso'_eq_mapHomologyIso U, hH, hO]
  rw [Category.assoc, ← U.map_comp,
    h.homologyIso_inv_comp_homologyι, U.map_comp]
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ U.map h.opcyclesIso.inv) hι

/-- The inverse homology comparison retains the same opcycles inclusion. -/
@[reassoc]
theorem mapHomologyIso_inv_comp_homologyι (S : ShortComplex C)
    [S.HasHomology] (U : C ⥤ D) [U.PreservesZeroMorphisms]
    [(S.map U).HasHomology] [U.PreservesLeftHomologyOf S]
    [U.PreservesRightHomologyOf S] :
    (S.mapHomologyIso U).inv ≫ (S.map U).homologyι =
      U.map S.homologyι ≫ (S.mapOpcyclesIso U).inv := by
  apply (cancel_mono (S.mapOpcyclesIso U).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← mapHomologyIso_hom_comp_homologyι S U]
  exact (S.mapHomologyIso U).inv_hom_id_assoc (U.map S.homologyι)

end CategoryTheory.ShortComplex

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
  {F G : C ⥤ D} [F.PreservesZeroMorphisms]
  [F.PreservesHomology]

/-- Preservation of homology transfers along an actual natural isomorphism. -/
theorem preservesHomology_of_iso (e : F ≅ G) :
    letI : G.PreservesZeroMorphisms := preservesZeroMorphisms_of_iso e
    G.PreservesHomology := by
  let : G.PreservesZeroMorphisms := preservesZeroMorphisms_of_iso e
  exact
    { preservesKernels {X Y} f := by
        let := Functor.PreservesHomology.preservesKernel F f
        exact preservesLimit_of_natIso (parallelPair f 0) e
      preservesCokernels {X Y} f := by
        let := Functor.PreservesHomology.preservesCokernel F f
        exact preservesColimit_of_natIso (parallelPair f 0) e }

end CategoryTheory.Functor
