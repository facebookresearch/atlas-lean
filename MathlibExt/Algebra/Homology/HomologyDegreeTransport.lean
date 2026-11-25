/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologyMapSquare

/-!
# Homology comparisons between equal degrees

An equality of grading indices identifies the corresponding cycles,
opcycles and homology objects. These comparisons commute with their
structural maps and with maps induced by morphisms of complexes.
-/

@[expose] public section

noncomputable section

universe v u w

open CategoryTheory Limits

namespace HomologicalComplex

/-- Transport of cycles along a degree equality. -/
noncomputable def cyclesIsoOfEq
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {p q : ι}
    (h : p = q) [K.HasHomology p] [K.HasHomology q] :
    K.cycles p ≅ K.cycles q := by
  subst h
  exact Iso.refl _

/-- Transport of homology along a degree equality. -/
noncomputable def homologyIsoOfEq
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {p q : ι}
    (h : p = q) [K.HasHomology p] [K.HasHomology q] :
    K.homology p ≅ K.homology q := by
  subst h
  exact Iso.refl _

/-- Transport of opcycles along a degree equality. -/
noncomputable def opcyclesIsoOfEq
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {p q : ι}
    (h : p = q) [K.HasHomology p] [K.HasHomology q] :
    K.opcycles p ≅ K.opcycles q := by
  subst h
  exact Iso.refl _

@[reassoc]
lemma cyclesIsoOfEq_hom_iCycles
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {p q : ι}
    (h : p = q) [K.HasHomology p] [K.HasHomology q] :
    (cyclesIsoOfEq K h).hom ≫ K.iCycles q =
      K.iCycles p ≫ (K.XIsoOfEq h).hom := by
  subst h
  simp [cyclesIsoOfEq, XIsoOfEq]

@[reassoc]
lemma pOpcycles_comp_opcyclesIsoOfEq_hom
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {p q : ι}
    (h : p = q) [K.HasHomology p] [K.HasHomology q] :
    K.pOpcycles p ≫ (opcyclesIsoOfEq K h).hom =
      (K.XIsoOfEq h).hom ≫ K.pOpcycles q := by
  subst h
  simp [opcyclesIsoOfEq, XIsoOfEq]

@[reassoc]
lemma homologyπ_comp_homologyIsoOfEq_hom
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {p q : ι}
    (h : p = q) [K.HasHomology p] [K.HasHomology q] :
    K.homologyπ p ≫ (homologyIsoOfEq K h).hom =
      (cyclesIsoOfEq K h).hom ≫ K.homologyπ q := by
  subst h
  simp [cyclesIsoOfEq, homologyIsoOfEq]

@[reassoc]
lemma homologyIsoOfEq_hom_comp_homologyι
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} (K : HomologicalComplex C c) {p q : ι}
    (h : p = q) [K.HasHomology p] [K.HasHomology q] :
    (homologyIsoOfEq K h).hom ≫ K.homologyι q =
      K.homologyι p ≫ (opcyclesIsoOfEq K h).hom := by
  subst h
  simp [homologyIsoOfEq, opcyclesIsoOfEq]

@[reassoc]
lemma cyclesIsoOfEq_hom_naturality
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)
    {p q : ι} (h : p = q) [K.HasHomology p] [K.HasHomology q]
    [L.HasHomology p] [L.HasHomology q] :
    K.cyclesMap f p ≫ (cyclesIsoOfEq L h).hom =
      (cyclesIsoOfEq K h).hom ≫ K.cyclesMap f q := by
  subst h
  simp [cyclesIsoOfEq]

@[reassoc]
lemma cyclesIsoOfEq_inv_naturality
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)
    {p q : ι} (h : p = q) [K.HasHomology p] [K.HasHomology q]
    [L.HasHomology p] [L.HasHomology q] :
    K.cyclesMap f q ≫ (cyclesIsoOfEq L h).inv =
      (cyclesIsoOfEq K h).inv ≫ K.cyclesMap f p := by
  subst h
  simp [cyclesIsoOfEq]

@[reassoc]
lemma opcyclesIsoOfEq_hom_naturality
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)
    {p q : ι} (h : p = q) [K.HasHomology p] [K.HasHomology q]
    [L.HasHomology p] [L.HasHomology q] :
    K.opcyclesMap f p ≫ (opcyclesIsoOfEq L h).hom =
      (opcyclesIsoOfEq K h).hom ≫ K.opcyclesMap f q := by
  subst h
  simp [opcyclesIsoOfEq]

@[reassoc]
lemma opcyclesIsoOfEq_inv_naturality
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)
    {p q : ι} (h : p = q) [K.HasHomology p] [K.HasHomology q]
    [L.HasHomology p] [L.HasHomology q] :
    K.opcyclesMap f q ≫ (opcyclesIsoOfEq L h).inv =
      (opcyclesIsoOfEq K h).inv ≫ K.opcyclesMap f p := by
  subst h
  simp [opcyclesIsoOfEq]

@[reassoc]
lemma homologyIsoOfEq_hom_naturality
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)
    {p q : ι} (h : p = q) [K.HasHomology p] [K.HasHomology q]
    [L.HasHomology p] [L.HasHomology q] :
    K.homologyMap f p ≫ (homologyIsoOfEq L h).hom =
      (homologyIsoOfEq K h).hom ≫ K.homologyMap f q := by
  subst h
  simp [homologyIsoOfEq]

@[reassoc]
lemma homologyIsoOfEq_inv_naturality
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)
    {p q : ι} (h : p = q) [K.HasHomology p] [K.HasHomology q]
    [L.HasHomology p] [L.HasHomology q] :
    K.homologyMap f q ≫ (homologyIsoOfEq L h).inv =
      (homologyIsoOfEq K h).inv ≫ K.homologyMap f p := by
  subst h
  simp [homologyIsoOfEq]

section EqualityTransportCoherence

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι} (K : HomologicalComplex C c)

/-- Reflexive degree transport is the identity on the homology object. -/
@[simp]
lemma homologyIsoOfEq_refl (p : ι) [K.HasHomology p] :
    homologyIsoOfEq K (rfl : p = p) = Iso.refl (K.homology p) := rfl

/-- Successive equal-degree homology maps are the map for the composed equality. -/
@[reassoc]
lemma homologyIsoOfEq_hom_trans {p q r : ι} (h₁ : p = q) (h₂ : q = r)
    [K.HasHomology p] [K.HasHomology q] [K.HasHomology r] :
    (homologyIsoOfEq K h₁).hom ≫ (homologyIsoOfEq K h₂).hom =
      (homologyIsoOfEq K (h₁.trans h₂)).hom := by
  subst h₁
  subst h₂
  simp [homologyIsoOfEq]

/-- Composition of the homology transport isomorphisms composes degree equalities. -/
lemma homologyIsoOfEq_trans {p q r : ι} (h₁ : p = q) (h₂ : q = r)
    [K.HasHomology p] [K.HasHomology q] [K.HasHomology r] :
    (homologyIsoOfEq K h₁).trans (homologyIsoOfEq K h₂) =
      homologyIsoOfEq K (h₁.trans h₂) := by
  apply Iso.ext
  exact homologyIsoOfEq_hom_trans K h₁ h₂

/-- Inverse degree transport is transport along the reversed degree equality. -/
@[simp]
lemma homologyIsoOfEq_symm {p q : ι} (h : p = q)
    [K.HasHomology p] [K.HasHomology q] :
    (homologyIsoOfEq K h).symm = homologyIsoOfEq K h.symm := by
  subst h
  rfl

end EqualityTransportCoherence

section FunctorIso

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [CategoryWithHomology C] {ι : Type w} {c : ComplexShape ι}

/-- In a category with chosen homology objects in every degree, the forward
degree-transport comparison is the canonical equality transport. -/
@[simp]
lemma homologyIsoOfEq_hom {p q : ι} (K : HomologicalComplex C c)
    (h : p = q) :
    (homologyIsoOfEq K h).hom =
      eqToHom (congrArg (fun i ↦ K.homology i) h) := by
  subst h
  rfl

/-- Degree transport for the cycles functor. -/
noncomputable def cyclesFunctorIsoOfEq {p q : ι} (h : p = q) :
    cyclesFunctor C c p ≅ cyclesFunctor C c q :=
  NatIso.ofComponents (fun K ↦ cyclesIsoOfEq K h)
    (fun f ↦ cyclesIsoOfEq_hom_naturality f h)

/-- Degree transport for the opcycles functor. -/
noncomputable def opcyclesFunctorIsoOfEq {p q : ι} (h : p = q) :
    opcyclesFunctor C c p ≅ opcyclesFunctor C c q :=
  NatIso.ofComponents (fun K ↦ opcyclesIsoOfEq K h)
    (fun f ↦ opcyclesIsoOfEq_hom_naturality f h)

/-- Degree transport for the homology functor. -/
noncomputable def homologyFunctorIsoOfEq {p q : ι} (h : p = q) :
    homologyFunctor C c p ≅ homologyFunctor C c q :=
  NatIso.ofComponents (fun K ↦ homologyIsoOfEq K h)
    (fun f ↦ homologyIsoOfEq_hom_naturality f h)

@[simp]
lemma cyclesFunctorIsoOfEq_hom_app
    {p q : ι} (h : p = q) (K : HomologicalComplex C c) :
    (cyclesFunctorIsoOfEq (C := C) h).hom.app K = (cyclesIsoOfEq K h).hom :=
  rfl

@[simp]
lemma cyclesFunctorIsoOfEq_inv_app
    {p q : ι} (h : p = q) (K : HomologicalComplex C c) :
    (cyclesFunctorIsoOfEq (C := C) h).inv.app K = (cyclesIsoOfEq K h).inv :=
  rfl

@[simp]
lemma opcyclesFunctorIsoOfEq_hom_app
    {p q : ι} (h : p = q) (K : HomologicalComplex C c) :
    (opcyclesFunctorIsoOfEq (C := C) h).hom.app K = (opcyclesIsoOfEq K h).hom :=
  rfl

@[simp]
lemma opcyclesFunctorIsoOfEq_inv_app
    {p q : ι} (h : p = q) (K : HomologicalComplex C c) :
    (opcyclesFunctorIsoOfEq (C := C) h).inv.app K = (opcyclesIsoOfEq K h).inv :=
  rfl

@[simp]
lemma homologyFunctorIsoOfEq_hom_app
    {p q : ι} (h : p = q) (K : HomologicalComplex C c) :
    (homologyFunctorIsoOfEq (C := C) h).hom.app K = (homologyIsoOfEq K h).hom :=
  rfl

@[simp]
lemma homologyFunctorIsoOfEq_inv_app
    {p q : ι} (h : p = q) (K : HomologicalComplex C c) :
    (homologyFunctorIsoOfEq (C := C) h).inv.app K = (homologyIsoOfEq K h).inv :=
  rfl

end FunctorIso

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the canonical homology isomorphism obtained by specifying
the predecessor and successor in a homological complex. -/
@[reassoc]
lemma homologyIsoSc'_hom_naturality
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology] :
    K.homologyMap f j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap
          ((shortComplexFunctor' C c i j k).map f) := by
  change
    ShortComplex.homologyMap ((shortComplexFunctor C c j).map f) ≫
        ShortComplex.homologyMap
          ((natIsoSc' C c i j k hi hk).hom.app L) =
      ShortComplex.homologyMap
          ((natIsoSc' C c i j k hi hk).hom.app K) ≫
        ShortComplex.homologyMap
          ((shortComplexFunctor' C c i j k).map f)
  exact ShortComplex.homologyMap_square
    ((natIsoSc' C c i j k hi hk).hom.naturality f)

/-- Inverse naturality of the canonical homology isomorphism obtained by
specifying the predecessor and successor in a homological complex. -/
@[reassoc]
lemma homologyIsoSc'_inv_naturality
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {ι : Type w}
    {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
    [K.HasHomology j] [L.HasHomology j]
    [(K.sc' i j k).HasHomology] [(L.sc' i j k).HasHomology] :
    ShortComplex.homologyMap ((shortComplexFunctor' C c i j k).map f) ≫
        (L.homologyIsoSc' i j k hi hk).inv =
      (K.homologyIsoSc' i j k hi hk).inv ≫ K.homologyMap f j := by
  rw [Iso.comp_inv_eq, Category.assoc,
    homologyIsoSc'_hom_naturality, Iso.inv_hom_id_assoc]

end HomologicalComplex
