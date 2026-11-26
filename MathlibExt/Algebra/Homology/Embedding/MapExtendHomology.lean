/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module
public import MathlibExt.Algebra.Homology.Embedding.MapExtend
public import MathlibExt.Algebra.Homology.Embedding.ExtendHomologyFunctor
public import MathlibExt.Algebra.Homology.Functor

/-!
# Components of the extension–homology comparison

For a shape embedding e and a selected degree j'=e(j), the natural
comparison between homology after extension by zero and original homology
has the same component as the canonical objectwise homology isomorphism.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v v' u u'

variable {ι : Type u} {ι' : Type u'} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable {C : Type v} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
  [CategoryWithHomology C]
variable {D : Type v'} [Category D] [HasZeroMorphisms D] [HasZeroObject D]
  [CategoryWithHomology D]

omit [HasZeroObject C] [CategoryWithHomology C]
  [HasZeroObject D] [CategoryWithHomology D] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem mapHomologyIso_homologyπ
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (S : ShortComplex C) [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [S.homologyData.left.mapHomologyIso_eq F]
  rw [S.homologyData.left.mapCyclesIso_eq F]
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [Category.assoc,
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  rw [cancel_epi]
  rw [ShortComplex.LeftHomologyData.map_π]
  rw [← F.map_comp, ← F.map_comp,
    ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]

omit [HasZeroObject C] [HasZeroObject D] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem mapHomologyFunctorIso_homologyπ
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    (K : HomologicalComplex C c) (i : ι) :
    ((F.mapHomologicalComplex c).obj K).homologyπ i ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := c) i F).hom.app K =
      ((K.sc i).mapCyclesIso F).hom ≫ F.map (K.homologyπ i) := by
  exact mapHomologyIso_homologyπ F (K.sc i)

omit [HasZeroObject C] [HasZeroObject D] in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem mapHomologicalComplex_mapCyclesIso_hom_iCycles
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    (K : HomologicalComplex C c) (i : ι) :
    ((K.sc i).mapCyclesIso F).hom ≫ F.map (K.iCycles i) =
      ((F.mapHomologicalComplex c).obj K).iCycles i := by
  exact ShortComplex.mapCyclesIso_hom_iCycles (S := K.sc i) F

/--
Let C have zero morphisms, a zero object and homology for short complexes. Let e:c→c' be a
shape embedding, K a c-complex, and j,j' degrees with e(j)=j'. The forward component at K of
the natural extension–homology comparison is exactly (K.extendHomologyIso e hj).hom, from
H_{j'}(K.extend e) to H_j(K).
-/
@[deprecated HomologicalComplex.extendHomologyFunctorIso_hom_app
  +typeChanged (since := "2026-10-21")]
theorem extendHomologyFunctorIso_hom_app
    (e : c.Embedding c') (K : HomologicalComplex C c)
    (j : ι) (j' : ι') (hj : e.f j = j') :
    (HomologicalComplex.extendHomologyFunctorIso
      (C := C) e j j' hj).hom.app K =
      (K.extendHomologyIso e hj).hom := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem extendFunctor_homologyπ_extendHomologyIso_hom
    (e : c.Embedding c') (K : HomologicalComplex C c)
    (j : ι) (j' : ι') (hj : e.f j = j') :
    ((e.extendFunctor C).obj K).homologyπ j' ≫
        (K.extendHomologyIso e hj).hom =
      (K.extendCyclesIso e hj).hom ≫ K.homologyπ j := by
  exact K.homologyπ_extendHomologyIso_hom e hj

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem mapHomologicalComplexExtendIso_cycles
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    (e : c.Embedding c') (K : HomologicalComplex C c)
    (j : ι) (j' : ι') (hj : e.f j = j') :
    HomologicalComplex.cyclesMap
          ((mapHomologicalComplexExtendIso F e).hom.app K) j' ≫
        ((((e.extendFunctor C).obj K).sc j').mapCyclesIso F).hom ≫
      F.map (K.extendCyclesIso e hj).hom =
    (((F.mapHomologicalComplex c).obj K).extendCyclesIso e hj).hom ≫
      ((K.sc j).mapCyclesIso F).hom := by
  let t := ((K.sc j).mapCyclesIso F).inv ≫ ((K.sc j).map F).iCycles
  have ht : F.map (K.iCycles j) = t := by
    dsimp only [t]
    rw [← cancel_epi ((K.sc j).mapCyclesIso F).hom]
    simp only [Iso.hom_inv_id_assoc]
    exact ShortComplex.mapCyclesIso_hom_iCycles (S := K.sc j) F
  have : Mono (F.map (K.iCycles j)) := by
    rw [ht]
    infer_instance
  rw [← cancel_mono (F.map (K.iCycles j))]
  simp only [Category.assoc]
  rw [← F.map_comp]
  rw [HomologicalComplex.extendCyclesIso_hom_iCycles]
  rw [F.map_comp]
  slice_lhs 2 3 =>
    erw [mapHomologicalComplex_mapCyclesIso_hom_iCycles]
  slice_rhs 2 3 =>
    rw [mapHomologicalComplex_mapCyclesIso_hom_iCycles]
  slice_lhs 1 2 =>
    erw [HomologicalComplex.cyclesMap_i]
  rw [HomologicalComplex.extendCyclesIso_hom_iCycles]
  simp only [Category.assoc]
  rw [mapHomologicalComplexExtendIso_hom_app_f]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem mapHomologicalComplexExtendIso_homology
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    (e : c.Embedding c') (K : HomologicalComplex C c)
    (j : ι) (j' : ι') (hj : e.f j = j') :
    HomologicalComplex.homologyMap
          ((mapHomologicalComplexExtendIso F e).hom.app K) j' ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := c') j' F).hom.app
          ((e.extendFunctor C).obj K) ≫
      F.map ((HomologicalComplex.extendHomologyFunctorIso
        (C := C) e j j' hj).hom.app K) =
    (HomologicalComplex.extendHomologyFunctorIso
        (C := D) e j j' hj).hom.app
          ((F.mapHomologicalComplex c).obj K) ≫
      (HomologicalComplex.mapHomologyFunctorIso (c := c) j F).hom.app K := by
  apply (cancel_epi
    (((F.mapHomologicalComplex c ⋙ e.extendFunctor D).obj K).homologyπ j')).mp
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  dsimp only [Functor.comp_obj]
  rw [mapHomologyFunctorIso_homologyπ_assoc]
  rw [HomologicalComplex.extendHomologyFunctorIso_hom_app
    (C := C) e j j' hj K]
  rw [HomologicalComplex.extendHomologyFunctorIso_hom_app
    (C := D) e j j' hj ((F.mapHomologicalComplex c).obj K)]
  rw [← F.map_comp]
  rw [extendFunctor_homologyπ_extendHomologyIso_hom]
  rw [extendFunctor_homologyπ_extendHomologyIso_hom_assoc]
  rw [mapHomologyFunctorIso_homologyπ]
  rw [F.map_comp]
  rw [mapHomologicalComplexExtendIso_cycles_assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
theorem mapHomologicalComplexExtendIso_homology_inv
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    (e : c.Embedding c') (K : HomologicalComplex C c)
    (j : ι) (j' : ι') (hj : e.f j = j') :
    (HomologicalComplex.mapHomologyFunctorIso (c := c) j F).inv.app K ≫
        (HomologicalComplex.extendHomologyFunctorIso
          (C := D) e j j' hj).inv.app
            ((F.mapHomologicalComplex c).obj K) =
      F.map ((HomologicalComplex.extendHomologyFunctorIso
        (C := C) e j j' hj).inv.app K) ≫
        (HomologicalComplex.mapHomologyFunctorIso (c := c') j' F).inv.app
          ((e.extendFunctor C).obj K) ≫
        HomologicalComplex.homologyMap
          ((mapHomologicalComplexExtendIso F e).inv.app K) j' := by
  let α := (HomologicalComplex.homologyFunctor D c' j').mapIso
    ((mapHomologicalComplexExtendIso F e).app K)
  let β := (HomologicalComplex.mapHomologyFunctorIso (c := c') j' F).app
    ((e.extendFunctor C).obj K)
  let γ := F.mapIso
    ((HomologicalComplex.extendHomologyFunctorIso (C := C) e j j' hj).app K)
  let δ := (HomologicalComplex.extendHomologyFunctorIso
    (C := D) e j j' hj).app ((F.mapHomologicalComplex c).obj K)
  let ε := (HomologicalComplex.mapHomologyFunctorIso (c := c) j F).app K
  have h := mapHomologicalComplexExtendIso_homology F e K j j' hj
  have hIso : α ≪≫ β ≪≫ γ = δ ≪≫ ε := Iso.ext h
  have hInv := congrArg Iso.inv hIso
  dsimp [α, β, γ, δ, ε] at hInv
  simpa only [Category.assoc, HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.extendHomologyFunctorIso_inv_app] using hInv.symm

end CategoryTheory.Functor
