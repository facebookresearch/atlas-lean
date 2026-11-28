/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.Algebra.Homology.HomologyMapSquare
public import MathlibExt.CategoryTheory.Abelian.Projective.ResolutionComparison

/-!
# Resolution and composition comparisons for left derivation

In abelian categories with projective resolutions in the source,
left-derived objects are canonically computed by any supplied projective
resolution. These comparisons are natural in maps and additive functors.
An additive homology-preserving postfunctor commutes with derivation.
An additive source functor preserving homology and projective objects
commutes with derivation by mapping source resolutions.
-/

/-
Authorship of the adapted portions: @toskua, Avocado.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe v v' v'' u u' u''

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasProjectiveResolutions C]

/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
`F : C → D` additive, and `P,Q` projective resolutions of `X`.
Their mapped chain homologies have the canonical comparison
`H_n(F(P)) ≅ H_n(F(Q))`, through `L_nF(X)`. -/
noncomputable def homologyComparisonIso {X : C}
    (P Q : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).obj
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).obj
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex) :=
  (P.isoLeftDerivedObj F n).symm.trans (Q.isoLeftDerivedObj F n)

@[simp]
theorem homologyComparisonIso_refl {X : C} (P : ProjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    homologyComparisonIso P P F n = Iso.refl _ := by
  apply Iso.ext
  exact Iso.inv_hom_id _

theorem homologyComparisonIso_symm {X : C}
    (P Q : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] (n : ℕ) :
    homologyComparisonIso Q P F n = (homologyComparisonIso P Q F n).symm := by
  rfl

@[simp]
theorem homologyComparisonIso_trans {X : C}
    (P Q S : ProjectiveResolution X) (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (homologyComparisonIso P Q F n).trans (homologyComparisonIso Q S F n) =
      homologyComparisonIso P S F n := by
  apply Iso.ext
  simp only [homologyComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- For abelian `C`, `D`, with projective resolutions in `C` and
additive `F : C → D`, take pairs of resolutions `P_X,Q_X` and
`P_Y,Q_Y` and resolution lifts of the same `f : X → Y`.
Their degree-`n` homology maps commute with the canonical
resolution-choice comparisons. -/
theorem homologyComparisonIso_naturality
    {X Y : C} {PX QX : ProjectiveResolution X}
    {PY QY : ProjectiveResolution Y} {f : X ⟶ Y}
    (φP : ProjectiveResolution.Hom PX PY f)
    (φQ : ProjectiveResolution.Hom QX QY f)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (homologyComparisonIso PX QX F n).hom ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map φQ.hom =
      (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map φP.hom ≫
        (homologyComparisonIso PY QY F n).hom := by
  have hQ : (F.leftDerived n).map f ≫ (QY.isoLeftDerivedObj F n).hom =
      (QX.isoLeftDerivedObj F n).hom ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map φQ.hom := by
    rw [F.leftDerived_map_eq n f φQ.hom φQ.hom_comp_π]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hP : (PX.isoLeftDerivedObj F n).inv ≫ (F.leftDerived n).map f =
      (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map φP.hom ≫
        (PY.isoLeftDerivedObj F n).inv := by
    rw [F.leftDerived_map_eq n f φP.hom φP.hom_comp_π]
    simp only [Iso.inv_hom_id_assoc]
  change ((PX.isoLeftDerivedObj F n).inv ≫ (QX.isoLeftDerivedObj F n).hom) ≫
      (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map φQ.hom =
      (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map φP.hom ≫
        ((PY.isoLeftDerivedObj F n).inv ≫ (QY.isoLeftDerivedObj F n).hom)
  simp only [Category.assoc]
  rw [← hQ, ← Category.assoc, hP, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
and let `F,G : C → D` be additive. For a resolution `P` of
`X` and `α : F → G`, the map on `H_n(F(P)) → H_n(G(P))`
commutes with the inverse comparisons to `L_nF(X)`, `L_nG(X)`. -/
@[reassoc]
theorem isoLeftDerivedObj_inv_naturality_functor
    {F G : C ⥤ D} [F.Additive] [G.Additive] {X : C}
    (P : ProjectiveResolution X) (α : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) n ≫
        (P.isoLeftDerivedObj G n).inv =
      (P.isoLeftDerivedObj F n).inv ≫ (NatTrans.leftDerived α n).app X := by
  rw [ProjectiveResolution.leftDerived_app_eq α P n,
    HomologicalComplex.homologyFunctor_map]
  simp only [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C`, `D` be abelian, with projective resolutions in `C`,
and let `F,G : C → D` be additive. For a resolution `P` of
`X` and `α : F → G`, the forward comparisons
`L_nF(X) → H_n(F(P))`, `L_nG(X) → H_n(G(P))` commute
with `L_nα` and the mapped homology transformation. -/
@[reassoc]
theorem isoLeftDerivedObj_hom_naturality_functor
    {F G : C ⥤ D} [F.Additive] [G.Additive] {X : C}
    (P : ProjectiveResolution X) (α : F ⟶ G) (n : ℕ) :
    (NatTrans.leftDerived α n).app X ≫ (P.isoLeftDerivedObj G n).hom =
      (P.isoLeftDerivedObj F n).hom ≫ HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app P.complex) n := by
  rw [ProjectiveResolution.leftDerived_app_eq α P n,
    HomologicalComplex.homologyFunctor_map]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {E : Type u''} [Category.{v''} E] [Abelian E]
variable [HasProjectiveResolutions C]

/-- Let `C`, `D`, `E` be abelian with projective resolutions in `C`.
If `F : C → D` is additive and `U : D → E` additive and
preserving homology, then `L_nF ⋙ U ≅ L_n(F ⋙ U)`
naturally in the resolved object. -/
noncomputable def leftDerivedCompIsoOfPreservesHomology
    (F : C ⥤ D) [F.Additive] (U : D ⥤ E) [U.Additive]
    [U.PreservesHomology] (n : ℕ) :
    F.leftDerived n ⋙ U ≅ (F ⋙ U).leftDerived n := by
  let eMap (P : ChainComplex C ℕ) :=
    (HomologicalComplex.mapHomologyFunctorIso
      (c := ComplexShape.down ℕ) n U).symm.app
        ((F.mapHomologicalComplex _).obj P)
  refine NatIso.ofComponents (fun X =>
    U.mapIso ((projectiveResolution X).isoLeftDerivedObj F n) ≪≫
      eMap (projectiveResolution X).complex ≪≫
      ((projectiveResolution X).isoLeftDerivedObj (F ⋙ U) n).symm) (fun {X Y} f => ?_)
  let φ := ProjectiveResolution.lift f (projectiveResolution X)
    (projectiveResolution Y)
  have hφ := ProjectiveResolution.lift_commutes_zero f
    (projectiveResolution X) (projectiveResolution Y)
  have hF := ProjectiveResolution.isoLeftDerivedObj_hom_naturality f
    (projectiveResolution X) (projectiveResolution Y) φ hφ F n
  have hFU := ProjectiveResolution.isoLeftDerivedObj_inv_naturality f
    (projectiveResolution X) (projectiveResolution Y) φ hφ (F ⋙ U) n
  have hmid : U.map ((F.mapHomologicalComplex _ ⋙
          HomologicalComplex.homologyFunctor _ _ n).map φ) ≫
      (eMap (projectiveResolution Y).complex).hom =
    (eMap (projectiveResolution X).complex).hom ≫
      (((F ⋙ U).mapHomologicalComplex _ ⋙
          HomologicalComplex.homologyFunctor _ _ n).map φ) :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor D (ComplexShape.down ℕ) n).map
        ((F.mapHomologicalComplex _).map φ)) U
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  conv_lhs => rw [← Category.assoc, ← U.map_comp, hF, U.map_comp, Category.assoc]
  congr 1
  conv_lhs => rw [← Category.assoc, hmid, Category.assoc]
  congr 1
  exact hFU.symm

end CategoryTheory.Functor

end


/- Proof implementation note.
## Source precomposition through mapped projective resolutions

The source functor preserves projectives and homology. The additive functor being derived has no
exactness hypothesis. Components use the mapped resolution, and the canonical complex-composition
dictionary supplies the middle isomorphism. No comparison or naturality certificate is supplied.
-/

/-!
## Derivation under a projective-preserving source functor

Let `C`, `D`, `E` be abelian, with projective resolutions in `C` and `D`.
If additive `U : C → D` preserves projective objects and homology,
and `L : D → E` is additive, a source resolution `P` maps to a
projective resolution `U(P)` and gives the natural comparison
`L_n(U ⋙ L) ≅ U ⋙ L_n(L)`.
-/

noncomputable section

universe v v' v'' u u' u''

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasProjectiveResolutions D]
  {E : Type u''} [Category.{v''} E] [Abelian E]
  (U : C ⥤ D) [U.Additive] [U.PreservesProjectiveObjects] [U.PreservesHomology]
  (L : D ⥤ E) [L.Additive]

/- Proof implementation note.
A source resolution gives the original derived precomposition component, using its image under the
source functor.
-/

/-- Let `C`, `D`, `E` be abelian with projective resolutions in `C`
and `D`, `U : C → D` additive and preserving projectives and
homology, and `L : D → E` additive. A projective resolution `P`
of `X` gives the component `L_n(U ⋙ L)(X) ≅ L_nL(U(X))`. -/
def leftDerivedPrecompIsoWithResolution (n : ℕ) {X : C} (P : ProjectiveResolution X) :
    ((U ⋙ L).leftDerived n).obj X ≅ (L.leftDerived n).obj (U.obj X) :=
  P.isoLeftDerivedObj (U ⋙ L) n ≪≫
    (HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n).mapIso
      (((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
        (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).app P.complex).symm) ≪≫
    ((U.mapProjectiveResolution P).isoLeftDerivedObj L n).symm

/- Proof implementation note.
The same original morphism and its mapped resolution lift give the precomposition naturality
square. No lift or square is an input.
-/

/-- For abelian `C`, `D`, `E` with projective resolutions in `C,D`,
additive homology- and projective-preserving `U : C → D`,
and additive `L : D → E`, the resolution-based precomposition
components commute with every original map `f : X → Y`. -/
theorem leftDerivedPrecompIsoWithResolution_naturality (n : ℕ)
    {X Y : C} (f : X ⟶ Y) (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    ((U ⋙ L).leftDerived n).map f ≫ (leftDerivedPrecompIsoWithResolution U L n Q).hom =
      (leftDerivedPrecompIsoWithResolution U L n P).hom ≫ (L.leftDerived n).map (U.map f) := by
  let H := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  let χ := Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)
  let aP := P.isoLeftDerivedObj (U ⋙ L) n
  let aQ := Q.isoLeftDerivedObj (U ⋙ L) n
  let bP := H.mapIso ((χ.app P.complex).symm)
  let bQ := H.mapIso ((χ.app Q.complex).symm)
  let cP := (U.mapProjectiveResolution P).isoLeftDerivedObj L n
  let cQ := (U.mapProjectiveResolution Q).isoLeftDerivedObj L n
  let φ : ProjectiveResolution.Hom P Q f :=
    { hom := ProjectiveResolution.lift f P Q
      hom_f_zero_comp_π_f_zero := by
        have h := ProjectiveResolution.lift_commutes_zero f P Q
        exact h.trans (congrArg (fun g : X ⟶ Y => P.π.f 0 ≫ g)
          (ChainComplex.single₀_map_f_zero f).symm) }
  let ψ := U.mapProjectiveResolutionHom φ
  have hφ : φ.hom.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f :=
    φ.hom_f_zero_comp_π_f_zero.trans (congrArg (fun g : X ⟶ Y => P.π.f 0 ≫ g)
      (ChainComplex.single₀_map_f_zero f))
  have hψ : ψ.hom.f 0 ≫ (U.mapProjectiveResolution Q).π.f 0 =
      (U.mapProjectiveResolution P).π.f 0 ≫ U.map f :=
    ψ.hom_f_zero_comp_π_f_zero.trans
      (congrArg (fun g : U.obj X ⟶ U.obj Y => (U.mapProjectiveResolution P).π.f 0 ≫ g)
        (ChainComplex.single₀_map_f_zero (U.map f)))
  have ha : ((U ⋙ L).leftDerived n).map f ≫ aQ.hom =
      aP.hom ≫ H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).map φ.hom) :=
    ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q φ.hom hφ (U ⋙ L) n
  have hb : H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).map φ.hom) ≫
      bQ.hom = bP.hom ≫ H.map ((L.mapHomologicalComplex (ComplexShape.down ℕ)).map ψ.hom) := by
    exact (isoWhiskerRight χ.symm H).hom.naturality φ.hom
  have hc : cP.inv ≫ (L.leftDerived n).map (U.map f) =
      H.map ((L.mapHomologicalComplex (ComplexShape.down ℕ)).map ψ.hom) ≫ cQ.inv :=
    ProjectiveResolution.isoLeftDerivedObj_inv_naturality (U.map f)
      (U.mapProjectiveResolution P) (U.mapProjectiveResolution Q) ψ.hom hψ L n
  change ((U ⋙ L).leftDerived n).map f ≫ (aQ.hom ≫ bQ.hom ≫ cQ.inv) =
    (aP.hom ≫ bP.hom ≫ cP.inv) ≫ (L.leftDerived n).map (U.map f)
  have sa : CommSq aP.hom (((U ⋙ L).leftDerived n).map f)
      (H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).map φ.hom)) aQ.hom :=
    ⟨ha.symm⟩
  have sb : CommSq bP.hom
      (H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.down ℕ)).map φ.hom))
      (H.map ((L.mapHomologicalComplex (ComplexShape.down ℕ)).map ψ.hom)) bQ.hom :=
    ⟨hb.symm⟩
  have sc : CommSq cP.inv
      (H.map ((L.mapHomologicalComplex (ComplexShape.down ℕ)).map ψ.hom))
      ((L.leftDerived n).map (U.map f)) cQ.inv := ⟨hc⟩
  exact (sa.horiz_comp (sb.horiz_comp sc)).w.symm


/-- For abelian `C`, `D`, `E` with projective resolutions in `C,D`,
additive homology- and projective-preserving `U : C → D`,
and additive `L : D → E`, any two projective resolutions of
`X` give the same degree-`n` precomposition component. -/
theorem leftDerivedPrecompIsoWithResolution_eq (n : ℕ) {X : C}
    (P Q : ProjectiveResolution X) :
    leftDerivedPrecompIsoWithResolution U L n P = leftDerivedPrecompIsoWithResolution U L n Q := by
  apply Iso.ext
  have h := leftDerivedPrecompIsoWithResolution_naturality U L n (𝟙 X) P Q
  simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

/-- Let `C`, `D`, `E` be abelian with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology,
and `L : D → E` additive. The component comparisons give
a natural isomorphism `L_n(U ⋙ L) ≅ U ⋙ L_nL`. -/
def leftDerivedPrecompIso (n : ℕ) :
    (U ⋙ L).leftDerived n ≅ U ⋙ L.leftDerived n :=
  NatIso.ofComponents
    (fun X => leftDerivedPrecompIsoWithResolution U L n (projectiveResolution X))
    (fun {X Y} f => leftDerivedPrecompIsoWithResolution_naturality U L n f
      (projectiveResolution X) (projectiveResolution Y))

/-- Let `C`, `D`, `E` be abelian, with projective resolutions in `C,D`,
`U : C → D` additive and preserving projectives and homology, and
`L : D → E` additive. The degree-`n` natural precomposition comparison
at `X` equals the comparison computed with any projective resolution
`P` of `X`. -/
theorem leftDerivedPrecompIso_app (n : ℕ) {X : C} (P : ProjectiveResolution X) :
    (leftDerivedPrecompIso U L n).app X = leftDerivedPrecompIsoWithResolution U L n P :=
  leftDerivedPrecompIsoWithResolution_eq U L n (projectiveResolution X) P

/- Proof implementation note.
The hom component is the resolution map, composition dictionary, and inverse of the
mapped-resolution comparison.
-/

/-- For abelian `C`, `D`, `E` with projective resolutions in `C,D`,
additive homology- and projective-preserving `U`, additive `L`,
and a resolution `P` of `X`, the forward precomposition
component is the comparison to `H_n((U ⋙ L)(P))`, followed
by the complex-composition identification and the inverse
comparison from `H_n(L(U(P)))` to `L_nL(U(X))`. -/
theorem leftDerivedPrecompIso_hom_app (n : ℕ) {X : C} (P : ProjectiveResolution X) :
    (leftDerivedPrecompIso U L n).hom.app X =
      (P.isoLeftDerivedObj (U ⋙ L) n).hom ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n).map
          ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
            (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).app P.complex).inv ≫
        ((U.mapProjectiveResolution P).isoLeftDerivedObj L n).inv := by
  rw [show (leftDerivedPrecompIso U L n).hom.app X =
      ((leftDerivedPrecompIso U L n).app X).hom from rfl, leftDerivedPrecompIso_app U L n P]
  rfl

/- Proof implementation note.
The inverse component uses the reversed comparisons and the same
complex-composition dictionary.
-/

/-- For abelian `C`, `D`, `E` with projective resolutions in `C,D`,
additive homology- and projective-preserving `U`, additive `L`,
and a resolution `P` of `X`, the inverse precomposition
component starts with the comparison to `H_n(L(U(P)))`,
uses the complex-composition identification, and finishes with
the inverse comparison to `L_n(U ⋙ L)(X)`. -/
theorem leftDerivedPrecompIso_inv_app (n : ℕ) {X : C} (P : ProjectiveResolution X) :
    (leftDerivedPrecompIso U L n).inv.app X =
      ((U.mapProjectiveResolution P).isoLeftDerivedObj L n).hom ≫
        (HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n).map
          ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
            (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).app P.complex).hom ≫
        (P.isoLeftDerivedObj (U ⋙ L) n).inv := by
  rw [show (leftDerivedPrecompIso U L n).inv.app X =
      ((leftDerivedPrecompIso U L n).app X).inv from rfl, leftDerivedPrecompIso_app U L n P]
  let H := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  let χ := (Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.down ℕ)).app P.complex
  let a := P.isoLeftDerivedObj (U ⋙ L) n
  let b := H.mapIso χ.symm
  let c := (U.mapProjectiveResolution P).isoLeftDerivedObj L n
  have tripleInv {X Y Z W : E} (a : X ≅ Y) (b : Y ≅ Z) (c : W ≅ Z) :
      (a ≪≫ b ≪≫ c.symm).inv = c.hom ≫ b.inv ≫ a.inv := by
    simp only [Iso.trans_inv, Iso.symm_inv]
    exact Category.assoc _ _ _
  change (a ≪≫ b ≪≫ c.symm).inv = c.hom ≫ H.map χ.hom ≫ a.inv
  exact (tripleInv a b c).trans
    (congrArg (fun f => c.hom ≫ f ≫ a.inv) (show b.inv = H.map χ.hom from rfl))


/-- For abelian `C`, `D`, `E` with projective resolutions in `C,D`,
additive homology- and projective-preserving `U : C → D`,
and additive `L₁,L₂ : D → E`, a transformation `α : L₁ → L₂`
commutes with the forward left-derived precomposition comparisons. -/
theorem leftDerivedPrecompIso_hom_naturality_functor
    {L₁ L₂ : D ⥤ E} [L₁.Additive] [L₂.Additive] (α : L₁ ⟶ L₂) (n : ℕ) :
    NatTrans.leftDerived (whiskerLeft U α) n ≫ (leftDerivedPrecompIso U L₂ n).hom =
      (leftDerivedPrecompIso U L₁ n).hom ≫ whiskerLeft U (NatTrans.leftDerived α n) := by
  apply NatTrans.ext
  funext X
  let P := projectiveResolution X
  let Q := U.mapProjectiveResolution P
  let H := HomologicalComplex.homologyFunctor E (ComplexShape.down ℕ) n
  let χ₁ := Functor.mapHomologicalComplexCompIso (F := U) (G := L₁)
    (Iso.refl (U ⋙ L₁)) (ComplexShape.down ℕ)
  let χ₂ := Functor.mapHomologicalComplexCompIso (F := U) (G := L₂)
    (Iso.refl (U ⋙ L₂)) (ComplexShape.down ℕ)
  let a₁ := P.isoLeftDerivedObj (U ⋙ L₁) n
  let a₂ := P.isoLeftDerivedObj (U ⋙ L₂) n
  let b₁ := H.mapIso ((χ₁.app P.complex).symm)
  let b₂ := H.mapIso ((χ₂.app P.complex).symm)
  let c₁ := Q.isoLeftDerivedObj L₁ n
  let c₂ := Q.isoLeftDerivedObj L₂ n
  let γ := (NatTrans.mapHomologicalComplex (whiskerLeft U α) (ComplexShape.down ℕ)).app P.complex
  let δ := (NatTrans.mapHomologicalComplex α (ComplexShape.down ℕ)).app Q.complex
  have ha : (NatTrans.leftDerived (whiskerLeft U α) n).app X ≫ a₂.hom =
      a₁.hom ≫ H.map γ := by
    have h := P.isoLeftDerivedObj_hom_naturality_functor (whiskerLeft U α) n
    change (NatTrans.leftDerived (whiskerLeft U α) n).app X ≫ a₂.hom =
      a₁.hom ≫ H.map γ at h
    exact h
  have hχ : γ ≫ (χ₂.app P.complex).inv = (χ₁.app P.complex).inv ≫ δ := by
    apply HomologicalComplex.hom_ext
    intro i
    change α.app (U.obj (P.complex.X i)) ≫ 𝟙 _ = 𝟙 _ ≫ α.app (U.obj (P.complex.X i))
    simp only [Category.id_comp, Category.comp_id]
  have hb : H.map γ ≫ b₂.hom = b₁.hom ≫ H.map δ := by
    change H.map γ ≫ H.map ((χ₂.app P.complex).inv) =
      H.map ((χ₁.app P.complex).inv) ≫ H.map δ
    exact (H.map_comp γ ((χ₂.app P.complex).inv)).symm.trans
      ((congrArg H.map hχ).trans (H.map_comp ((χ₁.app P.complex).inv) δ))
  have hc : c₁.inv ≫ (NatTrans.leftDerived α n).app (U.obj X) = H.map δ ≫ c₂.inv := by
    have h := (Q.isoLeftDerivedObj_inv_naturality_functor α n).symm
    change c₁.inv ≫ (NatTrans.leftDerived α n).app (U.obj X) = H.map δ ≫ c₂.inv at h
    exact h
  change (NatTrans.leftDerived (whiskerLeft U α) n).app X ≫
      (a₂.hom ≫ b₂.hom ≫ c₂.inv) =
    (a₁.hom ≫ b₁.hom ≫ c₁.inv) ≫ (NatTrans.leftDerived α n).app (U.obj X)
  have sa : CommSq a₁.hom ((NatTrans.leftDerived (whiskerLeft U α) n).app X)
      (H.map γ) a₂.hom := ⟨ha.symm⟩
  have sb : CommSq b₁.hom (H.map γ) (H.map δ) b₂.hom := ⟨hb.symm⟩
  have sc : CommSq c₁.inv (H.map δ)
      ((NatTrans.leftDerived α n).app (U.obj X)) c₂.inv := ⟨hc⟩
  exact (sa.horiz_comp (sb.horiz_comp sc)).w.symm


/-- For abelian `C`, `D`, `E` with projective resolutions in `C,D`,
additive homology- and projective-preserving `U : C → D`,
and additive `L₁,L₂ : D → E`, the inverse precomposition
comparisons commute with the derived transformation induced by
`α : L₁ → L₂`. -/
theorem leftDerivedPrecompIso_inv_naturality_functor
    {L₁ L₂ : D ⥤ E} [L₁.Additive] [L₂.Additive] (α : L₁ ⟶ L₂) (n : ℕ) :
    whiskerLeft U (NatTrans.leftDerived α n) ≫ (leftDerivedPrecompIso U L₂ n).inv =
      (leftDerivedPrecompIso U L₁ n).inv ≫ NatTrans.leftDerived (whiskerLeft U α) n := by
  have h := leftDerivedPrecompIso_hom_naturality_functor U α n
  have h' := congrArg (fun τ => (leftDerivedPrecompIso U L₁ n).inv ≫ τ ≫
    (leftDerivedPrecompIso U L₂ n).inv) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using h'.symm

end CategoryTheory.Functor

end
