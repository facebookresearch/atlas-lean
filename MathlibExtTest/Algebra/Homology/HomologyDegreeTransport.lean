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

public import MathlibExt.Algebra.Homology.HomologyDegreeTransport

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

universe v u w

open CategoryTheory Limits

namespace MathlibExtTest.Algebra.Homology.HomologyDegreeTransport

/-- Public client transporting cycles along a degree equality. -/
public noncomputable def cyclesIsoClient
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {p q : ι}
    (h : p = q) [K.HasHomology p] [K.HasHomology q] :
    K.cycles p ≅ K.cycles q :=
  HomologicalComplex.cyclesIsoOfEq K h

/-- Public client transporting homology along a degree equality. -/
public noncomputable def homologyIsoClient
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {p q : ι}
    (h : p = q) [K.HasHomology p] [K.HasHomology q] :
    K.homology p ≅ K.homology q :=
  HomologicalComplex.homologyIsoOfEq K h

/-- Public client restating compatibility of `homologyπ` with degree transport. -/
public theorem homologyπ_comp_client
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {p q : ι}
    (h : p = q) [K.HasHomology p] [K.HasHomology q] :
    K.homologyπ p ≫ (HomologicalComplex.homologyIsoOfEq K h).hom =
      (HomologicalComplex.cyclesIsoOfEq K h).hom ≫ K.homologyπ q :=
  HomologicalComplex.homologyπ_comp_homologyIsoOfEq_hom K h

/-- Public client for naturality of the homology isomorphism associated to a
specified predecessor and successor. -/
public theorem homologyIsoScNaturalityClient
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology] :
    K.homologyMap f j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' C c i j k).map f) :=
  HomologicalComplex.homologyIsoSc'_hom_naturality f i j k hi hk

/-- Public client for inverse naturality of the homology isomorphism
associated to a specified predecessor and successor. -/
public theorem homologyIsoScInvNaturalityClient
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology] :
    ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' C c i j k).map f) ≫
        (L.homologyIsoSc' i j k hi hk).inv =
      (K.homologyIsoSc' i j k hi hk).inv ≫ K.homologyMap f j :=
  HomologicalComplex.homologyIsoSc'_inv_naturality f i j k hi hk

end MathlibExtTest.Algebra.Homology.HomologyDegreeTransport
