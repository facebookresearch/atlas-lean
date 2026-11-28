/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology and opcycles comparisons under functors

Let U : C → D preserve zero morphisms. For a short complex S, preservation of its right homology
data gives the canonical opcycles comparison opcycles(U(S)) ≅ U(opcycles(S)). Preservation of
both left and right homology data gives H(U(S)) ≅ U(H(S)).

These comparisons preserve the quotient from the middle object and the homology inclusion into
opcycles. Homology preservation also transfers through a natural isomorphism of functors.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.ShortComplex

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

/-- Let C,D be categories with zero morphisms, S a short complex in C, and U : C → D a functor
preserving zero morphisms. Assume S has right homology and U preserves that right homology data.
The quotient U(S₂) → opcycles(U(S)), followed by opcycles(U(S)) ≅ U(opcycles(S)), equals U of
the original quotient S₂ → opcycles(S). -/
@[reassoc]
theorem pOpcycles_comp_mapOpcyclesIso_hom (S : ShortComplex C)
    [S.HasRightHomology] (U : C ⥤ D) [U.PreservesZeroMorphisms]
    [U.PreservesRightHomologyOf S] :
    (S.map U).pOpcycles ≫ (S.mapOpcyclesIso U).hom = U.map S.pOpcycles := by
  change (S.map U).pOpcycles ≫ (S.rightHomologyData.map U).opcyclesIso.hom = _
  rw [RightHomologyData.pOpcycles_comp_opcyclesIso_hom,
    RightHomologyData.map_p]
  rfl

/-- Let C,D be categories with zero morphisms, S a short complex in C, and U : C → D a functor
preserving zero morphisms. Assume S and U(S) have homology, and U preserves both homology data
of S. The comparison H(U(S)) ≅ U(H(S)) followed by U of H(S) → opcycles(S) equals H(U(S)) →
opcycles(U(S)) followed by the opcycles comparison. -/
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

/-- Let C,D be categories with zero morphisms, S a short complex in C, and U : C → D a functor
preserving zero morphisms. Assume S and U(S) have homology and U preserves both left and right
homology data of S. The inverse comparison U(H(S)) → H(U(S)) followed by the opcycles inclusion
equals U of the original inclusion followed by the inverse opcycles comparison. -/
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

/-- Let C,D have zero morphisms and let e : F ≅ G be a natural isomorphism of functors C → D. If F
preserves zero morphisms and the homology of every short complex, then G preserves zero
morphisms and homology as well. -/
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
