/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.Boundary
public import MathlibExt.Algebra.Homology.Embedding.RestrictionHomology

/-!
# Homology of the chain-to-cochain reindexing

This file provides infrastructure for comparing homology before and after the
standard integer chain-to-cochain reindexing.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

-- Degree negation is surjective, so the image is closed under both
-- predecessor and successor edges.
local instance : ComplexShape.embeddingUpIntDownInt.IsTruncLE where
  mem_prev {i' _} _ := ⟨-i', by simp [ComplexShape.embeddingUpIntDownInt]⟩

local instance : ComplexShape.embeddingUpIntDownInt.IsTruncGE where
  mem_next {_ k'} _ := ⟨-k', by simp [ComplexShape.embeddingUpIntDownInt]⟩

/-- Homology commutes with the standard integer chain-to-cochain reindexing. -/
noncomputable def chainToCochainHomologyIso
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (K : ChainComplex C ℤ) (i : ℤ)
    [K.HasHomology (ComplexShape.embeddingUpIntDownInt.f i)]
    [(K.restriction ComplexShape.embeddingUpIntDownInt).HasHomology i] :
    (K.restriction ComplexShape.embeddingUpIntDownInt).homology i ≅
      K.homology (ComplexShape.embeddingUpIntDownInt.f i) :=
  K.restrictionHomologyIsoAt ComplexShape.embeddingUpIntDownInt i
    (ComplexShape.embeddingUpIntDownInt.prev_f rfl)
    (ComplexShape.embeddingUpIntDownInt.next_f rfl)

/-- Opcycles commute with the standard integer chain-to-cochain reindexing. -/
noncomputable def chainToCochainOpcyclesIso
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (K : ChainComplex C ℤ) (i : ℤ)
    [K.HasHomology (ComplexShape.embeddingUpIntDownInt.f i)]
    [(K.restriction ComplexShape.embeddingUpIntDownInt).HasHomology i] :
    (K.restriction ComplexShape.embeddingUpIntDownInt).opcycles i ≅
      K.opcycles (ComplexShape.embeddingUpIntDownInt.f i) :=
  K.restrictionOpcyclesIsoAt ComplexShape.embeddingUpIntDownInt i
    (ComplexShape.embeddingUpIntDownInt.prev_f rfl)

/-- Cycles commute with the standard integer chain-to-cochain reindexing. -/
noncomputable def chainToCochainCyclesIso
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (K : ChainComplex C ℤ) (i : ℤ)
    [K.HasHomology (ComplexShape.embeddingUpIntDownInt.f i)]
    [(K.restriction ComplexShape.embeddingUpIntDownInt).HasHomology i] :
    (K.restriction ComplexShape.embeddingUpIntDownInt).cycles i ≅
      K.cycles (ComplexShape.embeddingUpIntDownInt.f i) :=
  K.restrictionCyclesIsoAt ComplexShape.embeddingUpIntDownInt i
    (ComplexShape.embeddingUpIntDownInt.next_f rfl)

/-- Functor-level homology comparison for integer chain-to-cochain
reindexing. -/
noncomputable def chainToCochainHomologyFunctorIso
    (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [CategoryWithHomology C] (i : ℤ) :
    ComplexShape.embeddingUpIntDownInt.restrictionFunctor C ⋙
        homologyFunctor C (ComplexShape.up ℤ) i ≅
      homologyFunctor C (ComplexShape.down ℤ)
        (ComplexShape.embeddingUpIntDownInt.f i) :=
  restrictionHomologyFunctorIsoAt ComplexShape.embeddingUpIntDownInt i
    (ComplexShape.embeddingUpIntDownInt.prev_f rfl)
    (ComplexShape.embeddingUpIntDownInt.next_f rfl)

@[reassoc]
theorem chainToCochainOpcyclesIso_naturality
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {K L : ChainComplex C ℤ} (f : K ⟶ L) (i : ℤ)
    [K.HasHomology (ComplexShape.embeddingUpIntDownInt.f i)]
    [L.HasHomology (ComplexShape.embeddingUpIntDownInt.f i)]
    [(K.restriction ComplexShape.embeddingUpIntDownInt).HasHomology i]
    [(L.restriction ComplexShape.embeddingUpIntDownInt).HasHomology i] :
    opcyclesMap
          (restrictionMap f ComplexShape.embeddingUpIntDownInt) i ≫
        (chainToCochainOpcyclesIso L i).hom =
      (chainToCochainOpcyclesIso K i).hom ≫
    opcyclesMap f (ComplexShape.embeddingUpIntDownInt.f i) :=
  restrictionOpcyclesIsoAt_hom_naturality
    ComplexShape.embeddingUpIntDownInt f i
      (ComplexShape.embeddingUpIntDownInt.prev_f rfl)

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of the homology isomorphism for integer chain-to-cochain reindexing. -/
@[reassoc]
lemma chainToCochainHomologyIso_naturality
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {K L : ChainComplex C ℤ} (f : K ⟶ L) (i : ℤ)
    [K.HasHomology (ComplexShape.embeddingUpIntDownInt.f i)]
    [L.HasHomology (ComplexShape.embeddingUpIntDownInt.f i)]
    [(K.restriction ComplexShape.embeddingUpIntDownInt).HasHomology i]
    [(L.restriction ComplexShape.embeddingUpIntDownInt).HasHomology i] :
    homologyMap
        (restrictionMap f ComplexShape.embeddingUpIntDownInt) i ≫
        (chainToCochainHomologyIso L i).hom =
      (chainToCochainHomologyIso K i).hom ≫
        homologyMap f (ComplexShape.embeddingUpIntDownInt.f i) :=
  restrictionHomologyIsoAt_hom_naturality
    ComplexShape.embeddingUpIntDownInt f i
      (ComplexShape.embeddingUpIntDownInt.prev_f rfl)
      (ComplexShape.embeddingUpIntDownInt.next_f rfl)

private lemma quasiIsoAt_restrictionMap_embeddingUpIntDownInt_iff
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [CategoryWithHomology C]
    {K L : ChainComplex C ℤ} (f : K ⟶ L) (i : ℤ) :
    QuasiIsoAt (restrictionMap f ComplexShape.embeddingUpIntDownInt) i ↔
      QuasiIsoAt f (ComplexShape.embeddingUpIntDownInt.f i) :=
  quasiIsoAt_restrictionMap_iff f ComplexShape.embeddingUpIntDownInt i
    (ComplexShape.embeddingUpIntDownInt.prev_f rfl)
    (ComplexShape.embeddingUpIntDownInt.next_f rfl)

/-- The cochain complex equivalence preserves quasi-isomorphisms. -/
@[simp]
lemma quasiIso_cochainComplexEquivalence_map_iff
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [CategoryWithHomology C]
    {K L : ChainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso ((ChainComplex.cochainComplexEquivalence C).functor.map f) ↔
      QuasiIso f := by
  change QuasiIso (restrictionMap f ComplexShape.embeddingUpIntDownInt) ↔
    QuasiIso f
  rw [quasiIso_iff, quasiIso_iff]
  constructor
  · intro h i
    have h1 := h (-i)
    rw [quasiIsoAt_restrictionMap_embeddingUpIntDownInt_iff] at h1
    simpa using h1
  · intro h i
    rw [quasiIsoAt_restrictionMap_embeddingUpIntDownInt_iff]
    exact h _

end HomologicalComplex
