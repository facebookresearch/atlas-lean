/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport

/-!
# Functorial homology comparisons for extension by zero

The native extension API supplies canonical objectwise comparisons for terms,
cycles, opcycles, and homology. This file packages the latter three as natural
isomorphisms and exposes both orientations of their naturality squares.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

universe w w' v u

section Naturality

variable {ι : Type w} {ι' : Type w'} {c : ComplexShape ι}
  {c' : ComplexShape ι'}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C]

/-- Inverse naturality of the component comparison for extension along an
embedding of complex shapes. -/
@[reassoc (attr := simp)]
theorem extendXIso_inv_naturality (e : c.Embedding c')
    {K L : HomologicalComplex C c} (φ : K ⟶ L)
    {i : ι} {i' : ι'} (h : e.f i = i') :
    (extendXIso K e h).inv ≫ (extendMap φ e).f i' =
      φ.f i ≫ (extendXIso L e h).inv := by
  rw [extendMap_f φ e h]
  simp

/-- Naturality of the opcycles comparison for extension along an embedding. -/
@[reassoc]
theorem extendOpcyclesIso_hom_naturality
    {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (e : c.Embedding c') {j : ι} {j' : ι'} (hj' : e.f j = j')
    [K.HasHomology j] [L.HasHomology j]
    [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j'] :
    opcyclesMap (extendMap φ e) j' ≫ (L.extendOpcyclesIso e hj').hom =
      (K.extendOpcyclesIso e hj').hom ≫ opcyclesMap φ j := by
  simp [← cancel_epi ((K.extend e).pOpcycles j'), extendMap_f φ e hj']

/-- Inverse naturality of the cycles comparison for extension along an
embedding. -/
@[reassoc]
theorem extendCyclesIso_inv_naturality
    {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (e : c.Embedding c') {j : ι} {j' : ι'} (hj' : e.f j = j')
    [K.HasHomology j] [L.HasHomology j]
    [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j'] :
    cyclesMap φ j ≫ (L.extendCyclesIso e hj').inv =
      (K.extendCyclesIso e hj').inv ≫ cyclesMap (extendMap φ e) j' := by
  apply (cancel_mono (L.extendCyclesIso e hj').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [extendCyclesIso_hom_naturality]
  simp

/-- Inverse naturality of the opcycles comparison for extension along an
embedding. -/
@[reassoc]
theorem extendOpcyclesIso_inv_naturality
    {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (e : c.Embedding c') {j : ι} {j' : ι'} (hj' : e.f j = j')
    [K.HasHomology j] [L.HasHomology j]
    [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j'] :
    opcyclesMap φ j ≫ (L.extendOpcyclesIso e hj').inv =
      (K.extendOpcyclesIso e hj').inv ≫ opcyclesMap (extendMap φ e) j' := by
  apply (cancel_mono (L.extendOpcyclesIso e hj').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [extendOpcyclesIso_hom_naturality]
  simp

/-- Inverse naturality of the homology comparison for extension along an
embedding. -/
@[reassoc]
theorem extendHomologyIso_inv_naturality
    {K L : HomologicalComplex C c} (φ : K ⟶ L)
    (e : c.Embedding c') {j : ι} {j' : ι'} (hj' : e.f j = j')
    [K.HasHomology j] [L.HasHomology j]
    [(K.extend e).HasHomology j'] [(L.extend e).HasHomology j'] :
    homologyMap φ j ≫ (L.extendHomologyIso e hj').inv =
      (K.extendHomologyIso e hj').inv ≫ homologyMap (extendMap φ e) j' := by
  apply (cancel_mono (L.extendHomologyIso e hj').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [extendHomologyIso_hom_naturality]
  simp

/-- The extension homology comparison is coherent under propositionally equal
shape embeddings and target degrees. -/
theorem homologyIsoOfEq_hom_extendHomologyIso_hom_of_embedding_eq
    (K : HomologicalComplex C c) (e e' : c.Embedding c') (he : e = e')
    (q : ι) (n m : ι') (hn : e'.f q = n) (hm : e.f q = m)
    (hDegree : n = m) [K.HasHomology q]
    [(K.extend e).HasHomology n] [(K.extend e).HasHomology m]
    [(K.extend e').HasHomology n] :
    (homologyIsoOfEq (K.extend e) hDegree).hom ≫
        (K.extendHomologyIso e hm).hom =
      homologyMap (eqToIso (congrArg (fun d ↦ K.extend d) he)).hom n ≫
        (K.extendHomologyIso e' hn).hom := by
  cases he
  cases hDegree
  have hhm : hm = hn := Subsingleton.elim _ _
  cases hhm
  simp [homologyIsoOfEq]

end Naturality

section FunctorIso

variable {ι : Type w} {ι' : Type w'} {c : ComplexShape ι}
  {c' : ComplexShape ι'}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  [CategoryWithHomology C]

/-- Functor-level cycles comparison for an embedding. -/
noncomputable def extendCyclesFunctorIso (e : c.Embedding c')
    (j : ι) (j' : ι') (hj' : e.f j = j') :
    e.extendFunctor C ⋙ cyclesFunctor C c' j' ≅ cyclesFunctor C c j :=
  NatIso.ofComponents (fun K ↦ K.extendCyclesIso e hj')
    (fun {_ _} f ↦ extendCyclesIso_hom_naturality f e hj')

/-- Functor-level opcycles comparison for an embedding. -/
noncomputable def extendOpcyclesFunctorIso (e : c.Embedding c')
    (j : ι) (j' : ι') (hj' : e.f j = j') :
    e.extendFunctor C ⋙ opcyclesFunctor C c' j' ≅ opcyclesFunctor C c j :=
  NatIso.ofComponents (fun K ↦ K.extendOpcyclesIso e hj')
    (fun {_ _} f ↦ extendOpcyclesIso_hom_naturality f e hj')

/-- Functor-level homology comparison for an embedding. -/
noncomputable def extendHomologyFunctorIso (e : c.Embedding c')
    (j : ι) (j' : ι') (hj' : e.f j = j') :
    e.extendFunctor C ⋙ homologyFunctor C c' j' ≅ homologyFunctor C c j :=
  NatIso.ofComponents (fun K => K.extendHomologyIso e hj')
    (fun {_ _} f => extendHomologyIso_hom_naturality f e hj')

@[simp]
lemma extendCyclesFunctorIso_hom_app (e : c.Embedding c')
    (j : ι) (j' : ι') (hj' : e.f j = j') (K : HomologicalComplex C c) :
    (extendCyclesFunctorIso (C := C) e j j' hj').hom.app K =
      (K.extendCyclesIso e hj').hom :=
  rfl

@[simp]
lemma extendCyclesFunctorIso_inv_app (e : c.Embedding c')
    (j : ι) (j' : ι') (hj' : e.f j = j') (K : HomologicalComplex C c) :
    (extendCyclesFunctorIso (C := C) e j j' hj').inv.app K =
      (K.extendCyclesIso e hj').inv :=
  rfl

@[simp]
lemma extendOpcyclesFunctorIso_hom_app (e : c.Embedding c')
    (j : ι) (j' : ι') (hj' : e.f j = j') (K : HomologicalComplex C c) :
    (extendOpcyclesFunctorIso (C := C) e j j' hj').hom.app K =
      (K.extendOpcyclesIso e hj').hom :=
  rfl

@[simp]
lemma extendOpcyclesFunctorIso_inv_app (e : c.Embedding c')
    (j : ι) (j' : ι') (hj' : e.f j = j') (K : HomologicalComplex C c) :
    (extendOpcyclesFunctorIso (C := C) e j j' hj').inv.app K =
      (K.extendOpcyclesIso e hj').inv :=
  rfl

@[simp]
lemma extendHomologyFunctorIso_hom_app (e : c.Embedding c')
    (j : ι) (j' : ι') (hj' : e.f j = j') (K : HomologicalComplex C c) :
    (extendHomologyFunctorIso (C := C) e j j' hj').hom.app K =
      (K.extendHomologyIso e hj').hom :=
  rfl

@[simp]
lemma extendHomologyFunctorIso_inv_app (e : c.Embedding c')
    (j : ι) (j' : ι') (hj' : e.f j = j') (K : HomologicalComplex C c) :
    (extendHomologyFunctorIso (C := C) e j j' hj').inv.app K =
      (K.extendHomologyIso e hj').inv :=
  rfl

end FunctorIso

section OffImage

variable {ι : Type w} {ι' : Type w'} {c : ComplexShape ι}
  {c' : ComplexShape ι'}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- Vanishing of homology off the image of the embedding. -/
lemma isZero_homology_extend_of_notMem_range
    (K : HomologicalComplex C c) (e : c.Embedding c') (j' : ι')
    (hj' : ∀ j, e.f j ≠ j') [(K.extend e).HasHomology j'] :
    IsZero ((K.extend e).homology j') :=
  (extend_exactAt K e j' hj').isZero_homology

end OffImage

end HomologicalComplex
