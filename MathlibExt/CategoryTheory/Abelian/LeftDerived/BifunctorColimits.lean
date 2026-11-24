/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerivedBifunctor
public import MathlibExt.Algebra.Homology.ExactColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Exact coefficient colimits for a left-derived bifunctor

One projective resolution of the first variable computes the existing left-derived bifunctor
naturally in its second variable. Colimit preservation of the original degreewise functors,
followed by exact homology colimits, gives the canonical all-degree comparison. Only the first
category needs projective resolutions.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ w w'

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  (F : C₁ ⥤ C₂ ⥤ D) [∀ B : C₂, (F.flip.obj B).Additive]

/--
The original bifunctor applied to a fixed complex in its first variable. Coefficient maps are the
maps of homological complexes.
-/
def coefficientComplexFunctor (P : ChainComplex C₁ ℕ) : C₂ ⥤ ChainComplex D ℕ where
  obj B := ((F.flip.obj B).mapHomologicalComplex (ComplexShape.down ℕ)).obj P
  map b := (NatTrans.mapHomologicalComplex (F.flip.map b) (ComplexShape.down ℕ)).app P
  map_id B := by
    rw [F.flip.map_id, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  map_comp {B B' B''} b b' := by
    rw [F.flip.map_comp, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

/-- Each component is the coefficient map at the original stage. -/
theorem coefficientComplexFunctor_map_f (P : ChainComplex C₁ ℕ)
    {B B' : C₂} (b : B ⟶ B') (i : ℕ) :
    ((F.coefficientComplexFunctor P).map b).f i =
      ((F.obj (P.X i)).map b) := rfl

/-- Its differential is the original first-variable map of the differential. -/
theorem coefficientComplexFunctor_obj_d (P : ChainComplex C₁ ℕ)
    (B : C₂) (i j : ℕ) :
    ((F.coefficientComplexFunctor P).obj B).d i j =
      (F.map (P.d i j)).app B := rfl

/-- Evaluation exposes the original stage functor, including its maps. -/
def coefficientComplexFunctorEvalIso (P : ChainComplex C₁ ℕ) (i : ℕ) :
    F.coefficientComplexFunctor P ⋙
        HomologicalComplex.eval D (ComplexShape.down ℕ) i ≅
      F.obj (P.X i) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro B B' b
    change (F.obj (P.X i)).map b ≫ 𝟙 _ = 𝟙 _ ≫ (F.obj (P.X i)).map b
    rw [Category.comp_id, Category.id_comp])

/--
Degreewise colimit preservation gives the fixed-complex colimit. No exactness of the coefficient
or projectivity of its objects is needed.
-/
theorem coefficientComplexFunctor_preservesColimitsOfShape
    (J : Type w) [Category.{w'} J] (P : ChainComplex C₁ ℕ)
    [∀ i : ℕ, PreservesColimitsOfShape J (F.obj (P.X i))] :
    PreservesColimitsOfShape J (F.coefficientComplexFunctor P) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro i
  exact preservesColimitsOfShape_of_natIso
    (F.coefficientComplexFunctorEvalIso P i).symm

/--
The chain-colimit comparison is induced by the stagewise coefficient maps, before applying
homology.
-/
def coefficientComplexColimitIso
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J C₂]
    [HasColimitsOfShape J D] (P : ChainComplex C₁ ℕ)
    [∀ i : ℕ, PreservesColimitsOfShape J (F.obj (P.X i))]
    (K : J ⥤ C₂) :
    (F.coefficientComplexFunctor P).obj (colimit K) ≅
      colimit (K ⋙ F.coefficientComplexFunctor P) := by
  letI := F.coefficientComplexFunctor_preservesColimitsOfShape J P
  exact preservesColimitIso (F.coefficientComplexFunctor P) K

/-- Each original coefficient leg followed by the chain comparison is the chain-colimit injection. -/
theorem map_ι_coefficientComplexColimitIso_hom
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J C₂]
    [HasColimitsOfShape J D] (P : ChainComplex C₁ ℕ)
    [∀ i : ℕ, PreservesColimitsOfShape J (F.obj (P.X i))]
    (K : J ⥤ C₂) (j : J) :
    (F.coefficientComplexFunctor P).map (colimit.ι K j) ≫
        (F.coefficientComplexColimitIso J P K).hom =
      colimit.ι (K ⋙ F.coefficientComplexFunctor P) j := by
  let := F.coefficientComplexFunctor_preservesColimitsOfShape J P
  exact ι_preservesColimitIso_hom (F.coefficientComplexFunctor P) K j

variable [HasProjectiveResolutions C₁]

/--
The fixed-resolution computation of the existing derived bifunctor is natural in its coefficient,
with the original homology objects.
-/
def leftDerivedBifunctorResolutionIso {A : C₁} (P : ProjectiveResolution A) (n : ℕ) :
    (F.leftDerivedBifunctor n).obj A ≅
      F.coefficientComplexFunctor P.complex ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n :=
  NatIso.ofComponents (fun B => P.isoLeftDerivedObj (F.flip.obj B) n) (by
    intro B B' b
    let H := HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n
    let e := P.isoLeftDerivedObj (F.flip.obj B) n
    let e' := P.isoLeftDerivedObj (F.flip.obj B') n
    let t := (NatTrans.mapHomologicalComplex (F.flip.map b)
      (ComplexShape.down ℕ)).app P.complex
    have h : (NatTrans.leftDerived (F.flip.map b) n).app A =
        e.hom ≫ H.map t ≫ e'.inv :=
      ProjectiveResolution.leftDerived_app_eq (F.flip.map b) P n
    change (NatTrans.leftDerived (F.flip.map b) n).app A ≫ e'.hom = e.hom ≫ H.map t
    calc
      _ = (e.hom ≫ H.map t ≫ e'.inv) ≫ e'.hom :=
        congrArg (fun q => q ≫ e'.hom) h
      _ = _ := by rw [Category.assoc, Category.assoc, e'.inv_hom_id, Category.comp_id])

/-- Components are the existing projective-resolution comparison, with no
separate choice of an objectwise isomorphism. -/
theorem leftDerivedBifunctorResolutionIso_hom_app
    {A : C₁} (P : ProjectiveResolution A) (n : ℕ) (B : C₂) :
    (F.leftDerivedBifunctorResolutionIso P n).hom.app B =
      (P.isoLeftDerivedObj (F.flip.obj B) n).hom := rfl

/-- The inverse components are the same resolution inverse. -/
theorem leftDerivedBifunctorResolutionIso_inv_app
    {A : C₁} (P : ProjectiveResolution A) (n : ℕ) (B : C₂) :
    (F.leftDerivedBifunctorResolutionIso P n).inv.app B =
      (P.isoLeftDerivedObj (F.flip.obj B) n).inv := rfl

variable (J : Type w) [Category.{w'} J] [HasColimitsOfShape J D]
  [(colim (J := J) (C := D)).PreservesHomology]

/--
Exact target colimits commute with every degree when the original stage functors preserve those
colimits on projective first objects. Only the terms of a first-variable resolution are used.
-/
theorem leftDerivedBifunctor_obj_preservesColimitsOfShape_of_projective
    (A : C₁) (n : ℕ)
    (hF : ∀ X : C₁, Projective X → PreservesColimitsOfShape J (F.obj X)) :
    PreservesColimitsOfShape J ((F.leftDerivedBifunctor n).obj A) := by
  let P := projectiveResolution A
  let : ∀ i : ℕ, PreservesColimitsOfShape J (F.obj (P.complex.X i)) :=
    fun i => hF (P.complex.X i) (P.projective i)
  let : PreservesColimitsOfShape J (F.coefficientComplexFunctor P.complex) :=
    F.coefficientComplexFunctor_preservesColimitsOfShape J P.complex
  let : PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n) :=
    HomologicalComplex.homologyFunctor_preservesColimitsOfShape n
  exact preservesColimitsOfShape_of_natIso
    (F.leftDerivedBifunctorResolutionIso P n).symm

/-- Exact target colimits commute with every degree of the existing
left-derived bifunctor in its coefficient variable. -/
theorem leftDerivedBifunctor_obj_preservesColimitsOfShape
    (A : C₁) (n : ℕ) [∀ X : C₁, PreservesColimitsOfShape J (F.obj X)] :
    PreservesColimitsOfShape J ((F.leftDerivedBifunctor n).obj A) := by
  exact F.leftDerivedBifunctor_obj_preservesColimitsOfShape_of_projective
    (J := J) (A := A) (n := n) (hF := fun X _ => inferInstance)

variable [HasColimitsOfShape J C₂] [∀ X : C₁, PreservesColimitsOfShape J (F.obj X)]

/-- Canonical coefficient-colimit comparison on the derived objects. -/
def leftDerivedBifunctorCoefficientColimitIso (A : C₁) (n : ℕ) (K : J ⥤ C₂) :
    ((F.leftDerivedBifunctor n).obj A).obj (colimit K) ≅
      colimit (K ⋙ (F.leftDerivedBifunctor n).obj A) := by
  letI := F.leftDerivedBifunctor_obj_preservesColimitsOfShape J A n
  exact preservesColimitIso ((F.leftDerivedBifunctor n).obj A) K

/-- Original coefficient injections are the forward comparison's injections. -/
theorem map_ι_leftDerivedBifunctorCoefficientColimitIso_hom
    (A : C₁) (n : ℕ) (K : J ⥤ C₂) (j : J) :
    ((F.leftDerivedBifunctor n).obj A).map (colimit.ι K j) ≫
        (F.leftDerivedBifunctorCoefficientColimitIso J A n K).hom =
      colimit.ι (K ⋙ (F.leftDerivedBifunctor n).obj A) j := by
  let := F.leftDerivedBifunctor_obj_preservesColimitsOfShape J A n
  exact ι_preservesColimitIso_hom ((F.leftDerivedBifunctor n).obj A) K j

/-- The inverse retains the original coefficient injection maps. -/
theorem ι_leftDerivedBifunctorCoefficientColimitIso_inv
    (A : C₁) (n : ℕ) (K : J ⥤ C₂) (j : J) :
    colimit.ι (K ⋙ (F.leftDerivedBifunctor n).obj A) j ≫
        (F.leftDerivedBifunctorCoefficientColimitIso J A n K).inv =
      ((F.leftDerivedBifunctor n).obj A).map (colimit.ι K j) := by
  let := F.leftDerivedBifunctor_obj_preservesColimitsOfShape J A n
  exact ι_preservesColimitIso_inv ((F.leftDerivedBifunctor n).obj A) K j

/-- The inverse is precisely the colimit map induced by those legs. -/
theorem leftDerivedBifunctorCoefficientColimitIso_inv_eq_post
    (A : C₁) (n : ℕ) (K : J ⥤ C₂) :
    (F.leftDerivedBifunctorCoefficientColimitIso J A n K).inv =
      colimit.post K ((F.leftDerivedBifunctor n).obj A) := by
  apply colimit.hom_ext
  intro j
  exact (F.ι_leftDerivedBifunctorCoefficientColimitIso_inv J A n K j).trans
    (colimit.ι_post (F := K) (G := (F.leftDerivedBifunctor n).obj A) j).symm

/-- Naturality in the entire coefficient diagram uses colimit maps. -/
theorem leftDerivedBifunctorCoefficientColimitIso_hom_naturality
    (A : C₁) (n : ℕ) {K K' : J ⥤ C₂} (t : K ⟶ K') :
    ((F.leftDerivedBifunctor n).obj A).map (colimMap t) ≫
        (F.leftDerivedBifunctorCoefficientColimitIso J A n K').hom =
      (F.leftDerivedBifunctorCoefficientColimitIso J A n K).hom ≫
        colimMap (Functor.whiskerRight t ((F.leftDerivedBifunctor n).obj A)) := by
  let := F.leftDerivedBifunctor_obj_preservesColimitsOfShape J A n
  exact (preservesColimitNatIso ((F.leftDerivedBifunctor n).obj A)).hom.naturality t

/--
Naturality in the original resolved variable follows from the derived transformation and the two
canonical colimit leg equations.
-/
theorem leftDerivedBifunctorCoefficientColimitIso_hom_naturality_left
    {A A' : C₁} (a : A ⟶ A') (n : ℕ) (K : J ⥤ C₂) :
    ((F.leftDerivedBifunctor n).map a).app (colimit K) ≫
        (F.leftDerivedBifunctorCoefficientColimitIso J A' n K).hom =
      (F.leftDerivedBifunctorCoefficientColimitIso J A n K).hom ≫
        colimMap (Functor.whiskerLeft K ((F.leftDerivedBifunctor n).map a)) := by
  let G := (F.leftDerivedBifunctor n).obj A
  let G' := (F.leftDerivedBifunctor n).obj A'
  let t := (F.leftDerivedBifunctor n).map a
  let e := F.leftDerivedBifunctorCoefficientColimitIso J A n K
  let e' := F.leftDerivedBifunctorCoefficientColimitIso J A' n K
  apply (cancel_epi e.inv).1
  change e.inv ≫ (t.app (colimit K) ≫ e'.hom) =
    e.inv ≫ (e.hom ≫ colimMap (Functor.whiskerLeft K t))
  have h : e.inv ≫ (t.app (colimit K) ≫ e'.hom) =
      colimMap (Functor.whiskerLeft K t) := by
    apply colimit.hom_ext
    intro j
    have hι := F.ι_leftDerivedBifunctorCoefficientColimitIso_inv J A n K j
    have hι' := F.map_ι_leftDerivedBifunctorCoefficientColimitIso_hom J A' n K j
    calc
      colimit.ι (K ⋙ G) j ≫ (e.inv ≫ (t.app (colimit K) ≫ e'.hom)) =
          (G.map (colimit.ι K j) ≫ t.app (colimit K)) ≫ e'.hom := by
        rw [← Category.assoc, hι]
        simp only [Category.assoc]
        rfl
      _ = (t.app (K.obj j) ≫ G'.map (colimit.ι K j)) ≫ e'.hom :=
        congrArg (fun q => q ≫ e'.hom) (t.naturality (colimit.ι K j))
      _ = t.app (K.obj j) ≫ colimit.ι (K ⋙ G') j := by
        rw [Category.assoc, hι']
      _ = colimit.ι (K ⋙ G) j ≫ colimMap (Functor.whiskerLeft K t) :=
        (ι_colimMap (Functor.whiskerLeft K t) j).symm
  rw [h, ← Category.assoc, e.inv_hom_id, Category.id_comp]

end CategoryTheory.Functor
