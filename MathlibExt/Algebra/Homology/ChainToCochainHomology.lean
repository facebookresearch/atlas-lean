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
# Homology under integer chain-to-cochain reindexing

For a category with zero morphisms, reindexing an integer chain
complex by `i ↦ -i` gives an integer cochain complex. The cycles,
opcycles and homology in cochain degree `i` are canonically identified
with those in chain degree `-i` whenever the displayed homologies
exist. The homology comparison is natural. With chosen homology
throughout the category it gives a functor isomorphism and the
chain-to-cochain equivalence preserves and reflects quasi-isomorphisms.
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

/-- Let `C` be a category with zero morphisms and `K` an integer
chain complex. Reindex by the shape embedding `i ↦ -i` to obtain
an integer cochain complex `K^∨`. Suppose the homologies of `K`
in degree `-i` and `K^∨` in degree `i` exist. Reindexing gives the canonical comparison
`H^i(K^∨) ≅ H_(-i)(K)`. -/
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

/-- Let `C` be a category with zero morphisms and `K` an integer
chain complex. Reindex by the shape embedding `i ↦ -i` to obtain
an integer cochain complex `K^∨`. Suppose the homologies of `K`
in degree `-i` and `K^∨` in degree `i` exist. Reindexing gives the canonical opcycles comparison
`opcycles^i(K^∨) ≅ opcycles_(-i)(K)`. -/
noncomputable def chainToCochainOpcyclesIso
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (K : ChainComplex C ℤ) (i : ℤ)
    [K.HasHomology (ComplexShape.embeddingUpIntDownInt.f i)]
    [(K.restriction ComplexShape.embeddingUpIntDownInt).HasHomology i] :
    (K.restriction ComplexShape.embeddingUpIntDownInt).opcycles i ≅
      K.opcycles (ComplexShape.embeddingUpIntDownInt.f i) :=
  K.restrictionOpcyclesIsoAt ComplexShape.embeddingUpIntDownInt i
    (ComplexShape.embeddingUpIntDownInt.prev_f rfl)

/-- Let `C` be a category with zero morphisms and `K` an integer
chain complex. Reindex by the shape embedding `i ↦ -i` to obtain
an integer cochain complex `K^∨`. Suppose the homologies of `K`
in degree `-i` and `K^∨` in degree `i` exist. Reindexing gives the canonical cycles comparison
`cycles^i(K^∨) ≅ cycles_(-i)(K)`. -/
noncomputable def chainToCochainCyclesIso
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (K : ChainComplex C ℤ) (i : ℤ)
    [K.HasHomology (ComplexShape.embeddingUpIntDownInt.f i)]
    [(K.restriction ComplexShape.embeddingUpIntDownInt).HasHomology i] :
    (K.restriction ComplexShape.embeddingUpIntDownInt).cycles i ≅
      K.cycles (ComplexShape.embeddingUpIntDownInt.f i) :=
  K.restrictionCyclesIsoAt ComplexShape.embeddingUpIntDownInt i
    (ComplexShape.embeddingUpIntDownInt.next_f rfl)

/-- Let `C` be a category with zero morphisms and chosen homology
objects in all degrees. Reindexing integer chains by `i ↦ -i`
followed by cochain homology in degree `i` is naturally isomorphic
to chain homology in degree `-i`. -/
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
/-- Let `C` be a category with zero morphisms, `f : K → L` a map
of integer chain complexes, and suppose the homologies of `K,L`
in degree `-i` and their reindexings in degree `i` exist. The
chain-to-cochain homology comparisons commute with both homology maps. -/
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

/-- Let `C` be a category with zero morphisms and chosen homology.
A map of integer chain complexes is a quasi-isomorphism if and only
if its image under the chain-to-cochain equivalence is one. -/
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
