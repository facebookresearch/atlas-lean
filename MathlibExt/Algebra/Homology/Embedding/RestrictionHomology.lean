/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: @toskua
-/

module

public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Functorial homology comparisons for restriction of complex shapes

Restriction along an embedding preserves homology at a degree when the
embedding also identifies that degree's predecessor and successor. This file
packages the native cycles, opcycles, and homology comparisons, proves both
orientations of their naturality, and bundles the comparisons as natural
isomorphisms.

Neighbor compatibility is explicit. In particular, relation reflection alone
does not identify the neighbors of a truncation-boundary degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

universe w w' v u

variable {ι : Type w} {ι' : Type w'} {c : ComplexShape ι}
  {c' : ComplexShape ι'}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

section ExplicitNaturality

/-- Naturality of `restrictionCyclesIso` for morphisms of homological
complexes. -/
@[reassoc]
lemma restrictionCyclesIso_naturality
    {K L : HomologicalComplex C c'} (φ : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff]
    (j k : ι) (hk : c.next j = k)
    {j' k' : ι'} (hj' : e.f j = j') (hk' : e.f k = k')
    (hk'' : c'.next j' = k')
    [K.HasHomology j'] [L.HasHomology j']
    [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    cyclesMap (restrictionMap φ e) j ≫
        (L.restrictionCyclesIso e j k hk hj' hk' hk'').hom =
      (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom ≫
        cyclesMap φ j' := by
  apply (cancel_mono (L.iCycles j')).mp
  simp only [Category.assoc,
    restrictionCyclesIso_hom_iCycles_assoc, cyclesMap_i_assoc,
    restrictionCyclesIso_hom_iCycles, cyclesMap_i]
  rw [restrictionMap_f' φ e hj']
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Naturality of `restrictionOpcyclesIso` for morphisms of homological
complexes. -/
@[reassoc]
lemma restrictionOpcyclesIso_naturality
    {K L : HomologicalComplex C c'} (φ : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff]
    (i j : ι) (hi : c.prev j = i)
    {i' j' : ι'} (hi' : e.f i = i') (hj' : e.f j = j')
    (hi'' : c'.prev j' = i')
    [K.HasHomology j'] [L.HasHomology j']
    [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    opcyclesMap (restrictionMap φ e) j ≫
        (L.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom =
      (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom ≫
        opcyclesMap φ j' := by
  apply (cancel_epi ((K.restriction e).pOpcycles j)).mp
  calc (K.restriction e).pOpcycles j ≫ opcyclesMap (restrictionMap φ e) j ≫
          (L.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom
      = (restrictionMap φ e).f j ≫ (L.restriction e).pOpcycles j ≫
          (L.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom := by
        rw [p_opcyclesMap_assoc]
    _ = (restrictionMap φ e).f j ≫
        ((L.restriction e).pOpcycles j ≫
          (L.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom) := rfl
    _ = (restrictionMap φ e).f j ≫
        ((L.restrictionXIso e hj').hom ≫ L.pOpcycles j') := by
        rw [pOpcycles_restrictionOpcyclesIso_hom]
    _ = (restrictionMap φ e).f j ≫ (L.restrictionXIso e hj').hom ≫
        L.pOpcycles j' := rfl
    _ = ((K.restrictionXIso e hj').hom ≫ φ.f j' ≫
        (L.restrictionXIso e hj').inv) ≫
        (L.restrictionXIso e hj').hom ≫ L.pOpcycles j' := by
        rw [restrictionMap_f' φ e hj']
    _ = (K.restrictionXIso e hj').hom ≫ φ.f j' ≫ L.pOpcycles j' := by
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = (K.restrictionXIso e hj').hom ≫
        (K.pOpcycles j' ≫ opcyclesMap φ j') := by
        rw [← p_opcyclesMap]
    _ = (K.restrictionXIso e hj').hom ≫ K.pOpcycles j' ≫
        opcyclesMap φ j' := rfl
    _ = ((K.restrictionXIso e hj').hom ≫ K.pOpcycles j') ≫
        opcyclesMap φ j' := by
        rw [← Category.assoc]
    _ = ((K.restriction e).pOpcycles j ≫
        (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom) ≫
        opcyclesMap φ j' := by
        rw [← pOpcycles_restrictionOpcyclesIso_hom]
    _ = (K.restriction e).pOpcycles j ≫
        (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom ≫
          opcyclesMap φ j' := by
        rw [Category.assoc]

/-- Naturality of `restrictionHomologyIso` for morphisms of homological
complexes. -/
@[reassoc]
lemma restrictionHomologyIso_naturality
    {K L : HomologicalComplex C c'} (φ : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff]
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j')
    (hk' : e.f k = k')
    (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
    [K.HasHomology j'] [L.HasHomology j']
    [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    homologyMap (restrictionMap φ e) j ≫
        (L.restrictionHomologyIso e i j k hi hk
          hi' hj' hk' hi'' hk'').hom =
      (K.restrictionHomologyIso e i j k hi hk
          hi' hj' hk' hi'' hk'').hom ≫ homologyMap φ j' := by
  apply (cancel_epi ((K.restriction e).homologyπ j)).mp
  simp only [homologyπ_naturality_assoc,
    homologyπ_restrictionHomologyIso_hom_assoc,
    homologyπ_naturality, homologyπ_restrictionHomologyIso_hom]
  rw [← Category.assoc,
    restrictionCyclesIso_naturality φ e j k hk hj' hk' hk'']
  simp only [Category.assoc]

/-- Inverse naturality of the cycles comparison for restriction. -/
@[reassoc]
lemma restrictionCyclesIso_inv_naturality
    {K L : HomologicalComplex C c'} (φ : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff]
    (j k : ι) (hk : c.next j = k)
    {j' k' : ι'} (hj' : e.f j = j') (hk' : e.f k = k')
    (hk'' : c'.next j' = k')
    [K.HasHomology j'] [L.HasHomology j']
    [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    cyclesMap φ j' ≫
        (L.restrictionCyclesIso e j k hk hj' hk' hk'').inv =
      (K.restrictionCyclesIso e j k hk hj' hk' hk'').inv ≫
        cyclesMap (restrictionMap φ e) j := by
  apply (cancel_epi
    (K.restrictionCyclesIso e j k hk hj' hk' hk'').hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← restrictionCyclesIso_naturality]
  simp

/-- Inverse naturality of the opcycles comparison for restriction. -/
@[reassoc]
lemma restrictionOpcyclesIso_inv_naturality
    {K L : HomologicalComplex C c'} (φ : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff]
    (i j : ι) (hi : c.prev j = i)
    {i' j' : ι'} (hi' : e.f i = i') (hj' : e.f j = j')
    (hi'' : c'.prev j' = i')
    [K.HasHomology j'] [L.HasHomology j']
    [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    opcyclesMap φ j' ≫
        (L.restrictionOpcyclesIso e i j hi hi' hj' hi'').inv =
      (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').inv ≫
        opcyclesMap (restrictionMap φ e) j := by
  apply (cancel_epi
    (K.restrictionOpcyclesIso e i j hi hi' hj' hi'').hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← restrictionOpcyclesIso_naturality]
  simp

/-- The inverse restriction-homology isomorphism is natural in the
homological complex. -/
@[reassoc]
lemma restrictionHomologyIso_inv_naturality
    {K L : HomologicalComplex C c'} (φ : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff]
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    {i' j' k' : ι'} (hi' : e.f i = i') (hj' : e.f j = j')
    (hk' : e.f k = k')
    (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
    [K.HasHomology j'] [L.HasHomology j']
    [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    homologyMap φ j' ≫
        (L.restrictionHomologyIso e i j k hi hk
          hi' hj' hk' hi'' hk'').inv =
      (K.restrictionHomologyIso e i j k hi hk
          hi' hj' hk' hi'' hk'').inv ≫
        homologyMap (restrictionMap φ e) j := by
  apply (cancel_epi
    (K.restrictionHomologyIso e i j k hi hk
      hi' hj' hk' hi'' hk'').hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← restrictionHomologyIso_naturality]
  simp

end ExplicitNaturality

section NeighborCompatible

variable (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]

/-- The cycles comparison at a degree where restriction preserves the
successor. -/
noncomputable def restrictionCyclesIsoAt (j : ι)
    (hnext : c'.next (e.f j) = e.f (c.next j))
    [K.HasHomology (e.f j)] [(K.restriction e).HasHomology j] :
    (K.restriction e).cycles j ≅ K.cycles (e.f j) :=
  K.restrictionCyclesIso e j (c.next j) rfl rfl rfl hnext

/-- The opcycles comparison at a degree where restriction preserves the
predecessor. -/
noncomputable def restrictionOpcyclesIsoAt (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    [K.HasHomology (e.f j)] [(K.restriction e).HasHomology j] :
    (K.restriction e).opcycles j ≅ K.opcycles (e.f j) :=
  K.restrictionOpcyclesIso e (c.prev j) j rfl rfl rfl hprev

/-- The homology comparison at a degree where restriction preserves both
neighbors. -/
noncomputable def restrictionHomologyIsoAt (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    (hnext : c'.next (e.f j) = e.f (c.next j))
    [K.HasHomology (e.f j)] [(K.restriction e).HasHomology j] :
    (K.restriction e).homology j ≅ K.homology (e.f j) :=
  K.restrictionHomologyIso e (c.prev j) j (c.next j)
    rfl rfl rfl rfl rfl hprev hnext

@[reassoc (attr := simp)]
lemma restrictionCyclesIsoAt_hom_iCycles (j : ι)
    (hnext : c'.next (e.f j) = e.f (c.next j))
    [K.HasHomology (e.f j)] [(K.restriction e).HasHomology j] :
    (K.restrictionCyclesIsoAt e j hnext).hom ≫ K.iCycles (e.f j) =
      (K.restriction e).iCycles j ≫ (K.restrictionXIso e rfl).hom :=
  K.restrictionCyclesIso_hom_iCycles e j (c.next j)
    rfl rfl rfl hnext

@[reassoc (attr := simp)]
lemma pOpcycles_restrictionOpcyclesIsoAt_hom (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    [K.HasHomology (e.f j)] [(K.restriction e).HasHomology j] :
    (K.restriction e).pOpcycles j ≫
        (K.restrictionOpcyclesIsoAt e j hprev).hom =
      (K.restrictionXIso e rfl).hom ≫ K.pOpcycles (e.f j) :=
  K.pOpcycles_restrictionOpcyclesIso_hom e
    (c.prev j) j rfl rfl rfl hprev

@[reassoc (attr := simp)]
lemma homologyπ_restrictionHomologyIsoAt_hom (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    (hnext : c'.next (e.f j) = e.f (c.next j))
    [K.HasHomology (e.f j)] [(K.restriction e).HasHomology j] :
    (K.restriction e).homologyπ j ≫
        (K.restrictionHomologyIsoAt e j hprev hnext).hom =
      (K.restrictionCyclesIsoAt e j hnext).hom ≫
        K.homologyπ (e.f j) :=
  K.homologyπ_restrictionHomologyIso_hom e
    (c.prev j) j (c.next j) rfl rfl rfl rfl rfl hprev hnext

@[reassoc (attr := simp)]
lemma restrictionHomologyIsoAt_hom_homologyι (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    (hnext : c'.next (e.f j) = e.f (c.next j))
    [K.HasHomology (e.f j)] [(K.restriction e).HasHomology j] :
    (K.restrictionHomologyIsoAt e j hprev hnext).hom ≫
        K.homologyι (e.f j) =
      (K.restriction e).homologyι j ≫
        (K.restrictionOpcyclesIsoAt e j hprev).hom :=
  K.restrictionHomologyIso_hom_homologyι e
    (c.prev j) j (c.next j) rfl rfl rfl rfl rfl hprev hnext

variable {K}

@[reassoc]
lemma restrictionCyclesIsoAt_hom_naturality
    {L : HomologicalComplex C c'} (φ : K ⟶ L) (j : ι)
    (hnext : c'.next (e.f j) = e.f (c.next j))
    [K.HasHomology (e.f j)] [L.HasHomology (e.f j)]
    [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    cyclesMap (restrictionMap φ e) j ≫
        (L.restrictionCyclesIsoAt e j hnext).hom =
      (K.restrictionCyclesIsoAt e j hnext).hom ≫
        cyclesMap φ (e.f j) :=
  restrictionCyclesIso_naturality φ e j (c.next j)
    rfl rfl rfl hnext

@[reassoc]
lemma restrictionOpcyclesIsoAt_hom_naturality
    {L : HomologicalComplex C c'} (φ : K ⟶ L) (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    [K.HasHomology (e.f j)] [L.HasHomology (e.f j)]
    [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    opcyclesMap (restrictionMap φ e) j ≫
        (L.restrictionOpcyclesIsoAt e j hprev).hom =
      (K.restrictionOpcyclesIsoAt e j hprev).hom ≫
        opcyclesMap φ (e.f j) :=
  restrictionOpcyclesIso_naturality φ e (c.prev j) j
    rfl rfl rfl hprev

@[reassoc]
lemma restrictionHomologyIsoAt_hom_naturality
    {L : HomologicalComplex C c'} (φ : K ⟶ L) (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    (hnext : c'.next (e.f j) = e.f (c.next j))
    [K.HasHomology (e.f j)] [L.HasHomology (e.f j)]
    [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    homologyMap (restrictionMap φ e) j ≫
        (L.restrictionHomologyIsoAt e j hprev hnext).hom =
      (K.restrictionHomologyIsoAt e j hprev hnext).hom ≫
        homologyMap φ (e.f j) :=
  restrictionHomologyIso_naturality φ e
    (c.prev j) j (c.next j) rfl rfl rfl rfl rfl hprev hnext

@[reassoc]
lemma restrictionHomologyIsoAt_inv_naturality
    {L : HomologicalComplex C c'} (φ : K ⟶ L) (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    (hnext : c'.next (e.f j) = e.f (c.next j))
    [K.HasHomology (e.f j)] [L.HasHomology (e.f j)]
    [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    homologyMap φ (e.f j) ≫
        (L.restrictionHomologyIsoAt e j hprev hnext).inv =
      (K.restrictionHomologyIsoAt e j hprev hnext).inv ≫
        homologyMap (restrictionMap φ e) j :=
  restrictionHomologyIso_inv_naturality φ e
    (c.prev j) j (c.next j) rfl rfl rfl rfl rfl hprev hnext

end NeighborCompatible

section FunctorIso

-- Mathlib's `restrictionFunctor` currently retains this instance parameter
-- even though its object and map constructions use only zero morphisms.
variable [HasZeroObject C] [CategoryWithHomology C]

/-- Functor-level cycles comparison for restriction at a degree with compatible
successor. -/
noncomputable def restrictionCyclesFunctorIsoAt
    (e : c.Embedding c') [e.IsRelIff] (j : ι)
    (hnext : c'.next (e.f j) = e.f (c.next j)) :
    e.restrictionFunctor C ⋙ cyclesFunctor C c j ≅
      cyclesFunctor C c' (e.f j) :=
  NatIso.ofComponents (fun K ↦ K.restrictionCyclesIsoAt e j hnext)
    (fun {_ _} φ ↦ restrictionCyclesIsoAt_hom_naturality e φ j hnext)

/-- Functor-level opcycles comparison for restriction at a degree with
compatible predecessor. -/
noncomputable def restrictionOpcyclesFunctorIsoAt
    (e : c.Embedding c') [e.IsRelIff] (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j)) :
    e.restrictionFunctor C ⋙ opcyclesFunctor C c j ≅
      opcyclesFunctor C c' (e.f j) :=
  NatIso.ofComponents (fun K ↦ K.restrictionOpcyclesIsoAt e j hprev)
    (fun {_ _} φ ↦ restrictionOpcyclesIsoAt_hom_naturality e φ j hprev)

/-- Functor-level homology comparison for restriction at a degree with
compatible predecessor and successor. -/
noncomputable def restrictionHomologyFunctorIsoAt
    (e : c.Embedding c') [e.IsRelIff] (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    (hnext : c'.next (e.f j) = e.f (c.next j)) :
    e.restrictionFunctor C ⋙ homologyFunctor C c j ≅
      homologyFunctor C c' (e.f j) :=
  NatIso.ofComponents (fun K ↦ K.restrictionHomologyIsoAt e j hprev hnext)
    (fun {_ _} φ ↦ restrictionHomologyIsoAt_hom_naturality
      e φ j hprev hnext)

omit [HasZeroObject C] in
@[simp]
lemma restrictionCyclesFunctorIsoAt_hom_app
    (e : c.Embedding c') [e.IsRelIff] (j : ι)
    (hnext : c'.next (e.f j) = e.f (c.next j))
    (K : HomologicalComplex C c') :
    (restrictionCyclesFunctorIsoAt (C := C) e j hnext).hom.app K =
      (K.restrictionCyclesIsoAt e j hnext).hom :=
  by
    unfold restrictionCyclesFunctorIsoAt
    rfl

omit [HasZeroObject C] in
@[simp]
lemma restrictionOpcyclesFunctorIsoAt_hom_app
    (e : c.Embedding c') [e.IsRelIff] (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    (K : HomologicalComplex C c') :
    (restrictionOpcyclesFunctorIsoAt (C := C) e j hprev).hom.app K =
      (K.restrictionOpcyclesIsoAt e j hprev).hom :=
  by
    unfold restrictionOpcyclesFunctorIsoAt
    rfl

omit [HasZeroObject C] in
@[simp]
lemma restrictionHomologyFunctorIsoAt_hom_app
    (e : c.Embedding c') [e.IsRelIff] (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    (hnext : c'.next (e.f j) = e.f (c.next j))
    (K : HomologicalComplex C c') :
    (restrictionHomologyFunctorIsoAt (C := C) e j hprev hnext).hom.app K =
      (K.restrictionHomologyIsoAt e j hprev hnext).hom :=
  by
    unfold restrictionHomologyFunctorIsoAt
    rfl

omit [HasZeroObject C] in
@[simp]
lemma restrictionHomologyFunctorIsoAt_inv_app
    (e : c.Embedding c') [e.IsRelIff] (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    (hnext : c'.next (e.f j) = e.f (c.next j))
    (K : HomologicalComplex C c') :
    (restrictionHomologyFunctorIsoAt (C := C) e j hprev hnext).inv.app K =
      (K.restrictionHomologyIsoAt e j hprev hnext).inv :=
  by
    unfold restrictionHomologyFunctorIsoAt
    rfl

end FunctorIso

section QuasiIso

/-- Restriction preserves and reflects a quasi-isomorphism at a degree whose
predecessor and successor are preserved by the shape embedding. -/
lemma quasiIsoAt_restrictionMap_iff
    {K L : HomologicalComplex C c'} (φ : K ⟶ L)
    (e : c.Embedding c') [e.IsRelIff] (j : ι)
    (hprev : c'.prev (e.f j) = e.f (c.prev j))
    (hnext : c'.next (e.f j) = e.f (c.next j))
    [K.HasHomology (e.f j)] [L.HasHomology (e.f j)]
    [(K.restriction e).HasHomology j]
    [(L.restriction e).HasHomology j] :
    QuasiIsoAt (restrictionMap φ e) j ↔ QuasiIsoAt φ (e.f j) := by
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  exact (MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (K.restrictionHomologyIsoAt e j hprev hnext)
      (L.restrictionHomologyIsoAt e j hprev hnext)
      (restrictionHomologyIsoAt_hom_naturality
        e φ j hprev hnext).symm)

end QuasiIso

end HomologicalComplex
