/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.Projective.AugmentedExactComparison
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ResolutionComparison

/-!
# Left-derived maps into exact augmented complexes

In an abelian category, a projective resolution of `X` maps into any
augmentation quasi-isomorphism `Q → Y[0]` over any `f : X → Y`.
For an additive functor into an abelian category, mapped homology gives
`L_nF(X) → H_n(F(Q))`, independently of the chosen lift and source
resolution. The target terms need neither projectivity nor `F`-acyclicity.
These maps are natural in the source, augmented target complex, and
additive coefficient functor, and preserve degree-zero augmentations.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' v'


namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y : C}

/-- In an abelian category `C`, let `P` be a projective resolution of
`X`, `ρ : Q → Y[0]` a quasi-isomorphism of nonnegative chain
complexes, and `f : X → Y`. There is a chain map `a : P → Q`
satisfying `a ≫ ρ = π_P ≫ f[0]`. -/
def comparisonToAugmentedExact (P : ProjectiveResolution X) (Q : ChainComplex C ℕ)
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso ρ] (f : X ⟶ Y) :
    {a : P.complex ⟶ Q // a ≫ ρ = P.π ≫ (ChainComplex.single₀ C).map f} :=
  let h := exists_projectiveAugmentedExactComparison P.π ρ P.projective f
  ⟨h.choose, h.choose_spec⟩

end CategoryTheory.ProjectiveResolution

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {X : C} {Q : ChainComplex C ℕ}

/-- Let `C,D` be abelian, `F : C → D` additive, and
`ρ : Q → X[0]` a chain augmentation. Its mapped degree-zero map
descends to `opcycles₀(F(Q)) → F(X)`, without requiring exactness
of the mapped complex. -/
def mappedAugmentationDesc (F : C ⥤ D) [F.Additive]
    (ρ : Q ⟶ (single₀ C).obj X) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).opcycles 0 ⟶ F.obj X :=
  HomologicalComplex.descOpcycles _ (F.map (ρ.f 0)) 1 (by simp) (by
    change F.map (Q.d 1 0) ≫ F.map (ρ.f 0) = 0
    rw [← F.map_comp, ← ρ.comm 1 0, HomologicalComplex.single_obj_d,
      comp_zero, F.map_zero])

/-- Let `C,D` be abelian, `F : C → D` additive, and
`ρ : Q → X[0]` a chain augmentation. The quotient
`F(Q₀) → opcycles₀(F(Q))` followed by augmentation descent equals
`F(ρ₀)`. -/
theorem pOpcycles_comp_mappedAugmentationDesc (F : C ⥤ D) [F.Additive]
    (ρ : Q ⟶ (single₀ C).obj X) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).pOpcycles 0 ≫
      mappedAugmentationDesc F ρ = F.map (ρ.f 0) :=
  HomologicalComplex.p_descOpcycles _ _ _ _ _

/-- Let `C,D` be abelian, `F : C → D` additive, and
`ρ : Q → X[0]` a chain augmentation. The opcycles descent gives
a map `H₀(F(Q)) → F(X)` through the degree-zero homology-to-opcycles
identification. -/
def mappedAugmentationHomologyZero (F : C ⥤ D) [F.Additive]
    (ρ : Q ⟶ (single₀ C).obj X) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homology 0 ⟶ F.obj X :=
  ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homologyι 0 ≫
    mappedAugmentationDesc F ρ

end ChainComplex

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive, `ρ : Q → Y[0]` a quasi-isomorphism of
nonnegative chain complexes, and `f : X → Y`. A projective resolution `P` of `X` and an augmented
comparison
`P → Q` give the map `L_nF(X) → H_n(F(Q))`. -/
def leftDerivedObjToAugmentedHomWithResolution (F : C ⥤ D) [F.Additive]
    {X Y : C} (P : ProjectiveResolution X) (Q : ChainComplex C ℕ)
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso ρ] (f : X ⟶ Y) (n : ℕ) :
    (F.leftDerived n).obj X ⟶
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homology n :=
  (P.isoLeftDerivedObj F n).hom ≫
    (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
      HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map
        (P.comparisonToAugmentedExact Q ρ f).val

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive, `ρ : Q → Y[0]` a quasi-isomorphism of
nonnegative chain complexes, and `f : X → Y`. For any resolution `P` of `X` and chain map `a : P →
Q`
over `f`, the comparison is the canonical map to `H_n(F(P))`
followed by `H_n(F(a))`. -/
theorem leftDerivedObjToAugmentedHomWithResolution_eq (F : C ⥤ D) [F.Additive]
    {X Y : C} (P : ProjectiveResolution X) (Q : ChainComplex C ℕ)
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso ρ] (f : X ⟶ Y)
    (a : P.complex ⟶ Q) (ha : a ≫ ρ = P.π ≫ (ChainComplex.single₀ C).map f) (n : ℕ) :
    leftDerivedObjToAugmentedHomWithResolution F P Q ρ f n =
      (P.isoLeftDerivedObj F n).hom ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map a := by
  let H := F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n
  have h := projectiveAugmentedExactComparison_homologyMap_eq F ρ P.projective
    (P.comparisonToAugmentedExact Q ρ f).val a
    ((P.comparisonToAugmentedExact Q ρ f).property.trans ha.symm) n
  change H.map (P.comparisonToAugmentedExact Q ρ f).val = H.map a at h
  exact congrArg (fun g => (P.isoLeftDerivedObj F n).hom ≫ g) h

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive, `ρ : Q → Y[0]` a quasi-isomorphism of
nonnegative chain complexes, and `f : X → Y`. Any two source projective resolutions of `X` give the
same
comparison `L_nF(X) → H_n(F(Q))`. -/
theorem leftDerivedObjToAugmentedHomWithResolution_independent
    (F : C ⥤ D) [F.Additive] {X Y : C}
    (P P' : ProjectiveResolution X) (Q : ChainComplex C ℕ)
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso ρ] (f : X ⟶ Y) (n : ℕ) :
    leftDerivedObjToAugmentedHomWithResolution F P Q ρ f n =
      leftDerivedObjToAugmentedHomWithResolution F P' Q ρ f n := by
  let r := ProjectiveResolution.lift (𝟙 X) P P'
  let a := (P'.comparisonToAugmentedExact Q ρ f).val
  have hr : r ≫ P'.π = P.π := by
    simpa only [Functor.map_id, Category.comp_id] using
      ProjectiveResolution.lift_commutes (𝟙 X) P P'
  have ha : (r ≫ a) ≫ ρ = P.π ≫ (ChainComplex.single₀ C).map f := by
    rw [Category.assoc, (P'.comparisonToAugmentedExact Q ρ f).property,
      ← Category.assoc, hr]
  rw [leftDerivedObjToAugmentedHomWithResolution_eq F P Q ρ f (r ≫ a) ha n]
  let H := F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n
  have hI : (P.isoLeftDerivedObj F n).hom ≫ H.map r = (P'.isoLeftDerivedObj F n).hom := by
    have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 X) P P' r
      (by
        have h0 : @Eq (P.complex.X 0 ⟶ X) (r.f 0 ≫ P'.π.f 0) (P.π.f 0) :=
          HomologicalComplex.congr_hom hr 0
        exact h0.trans (Category.comp_id (P.π.f 0)).symm) F n
    simpa only [Functor.map_id, Category.id_comp] using h.symm
  change (P.isoLeftDerivedObj F n).hom ≫ H.map (r ≫ a) =
    (P'.isoLeftDerivedObj F n).hom ≫ H.map a
  rw [H.map_comp, ← Category.assoc, hI]

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive, `ρ : Q → Y[0]` a quasi-isomorphism of
nonnegative chain complexes, and `f : X → Y`. Using the chosen source resolution defines the
canonical
map `L_nF(X) → H_n(F(Q))`. -/
def leftDerivedObjToAugmentedHom (F : C ⥤ D) [F.Additive]
    {X Y : C} (Q : ChainComplex C ℕ)
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso ρ] (f : X ⟶ Y) (n : ℕ) :
    (F.leftDerived n).obj X ⟶
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q).homology n :=
  leftDerivedObjToAugmentedHomWithResolution F (projectiveResolution X) Q ρ f n

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive, `ρ : Q → Y[0]` a quasi-isomorphism of
nonnegative chain complexes, and `f : X → Y`. Any projective resolution `P` of `X` and any lift
`a : P → Q` over `f` compute the canonical comparison by
`L_nF(X) → H_n(F(P)) → H_n(F(Q))`. -/
theorem leftDerivedObjToAugmentedHom_eq (F : C ⥤ D) [F.Additive]
    {X Y : C} (P : ProjectiveResolution X) (Q : ChainComplex C ℕ)
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso ρ] (f : X ⟶ Y)
    (a : P.complex ⟶ Q) (ha : a ≫ ρ = P.π ≫ (ChainComplex.single₀ C).map f) (n : ℕ) :
    leftDerivedObjToAugmentedHom F Q ρ f n =
      (P.isoLeftDerivedObj F n).hom ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map a :=
  (leftDerivedObjToAugmentedHomWithResolution_independent F
      (projectiveResolution X) P Q ρ f n).trans
    (leftDerivedObjToAugmentedHomWithResolution_eq F P Q ρ f a ha n)

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive, `ρ : Q → Y[0]` a quasi-isomorphism of
nonnegative chain complexes, and `f : X → Y`. If `a : Q → Q′` lies over `g : Y → Z`, with exact
augmentation `Q′ → Z[0]`, then the comparison followed by
`H_n(F(a))` equals the comparison for `Q′` over `f ≫ g`. -/
theorem leftDerivedObjToAugmentedHom_naturality_target (F : C ⥤ D) [F.Additive]
    {X Y Z : C} {Q Q' : ChainComplex C ℕ}
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y)
    (ρ' : Q' ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ρ] [QuasiIso ρ']
    (f : X ⟶ Y) (g : Y ⟶ Z) (a : Q ⟶ Q')
    (ha : a ≫ ρ' = ρ ≫ (ChainComplex.single₀ C).map g) (n : ℕ) :
    leftDerivedObjToAugmentedHom F Q ρ f n ≫
        (F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n).map a =
      leftDerivedObjToAugmentedHom F Q' ρ' (f ≫ g) n := by
  let P := projectiveResolution X
  let r := (P.comparisonToAugmentedExact Q ρ f).val
  have hr : (r ≫ a) ≫ ρ' = P.π ≫ (ChainComplex.single₀ C).map (f ≫ g) := by
    rw [Category.assoc, ha, ← Category.assoc,
      (P.comparisonToAugmentedExact Q ρ f).property, Category.assoc, ← Functor.map_comp]
  rw [leftDerivedObjToAugmentedHom_eq F P Q ρ f r
      (P.comparisonToAugmentedExact Q ρ f).property n,
    leftDerivedObjToAugmentedHom_eq F P Q' ρ' (f ≫ g) (r ≫ a) hr n]
  let H := F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n
  change ((P.isoLeftDerivedObj F n).hom ≫ H.map r) ≫ H.map a =
    (P.isoLeftDerivedObj F n).hom ≫ H.map (r ≫ a)
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => (P.isoLeftDerivedObj F n).hom ≫ z) (H.map_comp r a).symm)

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive, and `ρ : Q → Z[0]` a quasi-isomorphism.
For `f : X → Y`, `g : Y → Z`, the map `L_nF(f)` followed by the
comparison for `g` equals the comparison for `f ≫ g`. -/
theorem leftDerivedObjToAugmentedHom_naturality_source (F : C ⥤ D) [F.Additive]
    {X Y Z : C} (Q : ChainComplex C ℕ)
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ρ]
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    (F.leftDerived n).map f ≫ leftDerivedObjToAugmentedHom F Q ρ g n =
      leftDerivedObjToAugmentedHom F Q ρ (f ≫ g) n := by
  let P := projectiveResolution X
  let P' := projectiveResolution Y
  let r := ProjectiveResolution.lift f P P'
  let a := (P'.comparisonToAugmentedExact Q ρ g).val
  have hr : (r ≫ a) ≫ ρ = P.π ≫ (ChainComplex.single₀ C).map (f ≫ g) := by
    rw [Category.assoc, (P'.comparisonToAugmentedExact Q ρ g).property,
      ← Category.assoc, ProjectiveResolution.lift_commutes,
      Category.assoc, ← Functor.map_comp]
  rw [leftDerivedObjToAugmentedHom_eq F P' Q ρ g a
      (P'.comparisonToAugmentedExact Q ρ g).property n,
    leftDerivedObjToAugmentedHom_eq F P Q ρ (f ≫ g) (r ≫ a) hr n]
  let H := F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙
    HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n
  have hI := ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P P' r
    (ProjectiveResolution.lift_commutes_zero f P P') F n
  change (F.leftDerived n).map f ≫ ((P'.isoLeftDerivedObj F n).hom ≫ H.map a) =
    (P.isoLeftDerivedObj F n).hom ≫ H.map (r ≫ a)
  rw [← Category.assoc, hI, H.map_comp, Category.assoc]

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive, `Q` a projective resolution of `Y`, and
`f : X → Y`. The canonical comparison to `H_n(F(Q))` is
`L_nF(f)` followed by the canonical resolution isomorphism for `Q`. -/
theorem leftDerivedObjToAugmentedHom_projective_target (F : C ⥤ D) [F.Additive]
    {X Y : C} (Q : ProjectiveResolution Y) (f : X ⟶ Y) (n : ℕ) :
    leftDerivedObjToAugmentedHom F Q.complex Q.π f n =
      (F.leftDerived n).map f ≫ (Q.isoLeftDerivedObj F n).hom := by
  let P := projectiveResolution X
  let a := (P.comparisonToAugmentedExact Q.complex Q.π f).val
  have ha₀ : a.f 0 ≫ Q.π.f 0 = P.π.f 0 ≫ f := by
    have h₀ : @Eq (P.complex.X 0 ⟶ Y)
        ((a ≫ Q.π).f 0) ((P.π ≫ (ChainComplex.single₀ C).map f).f 0) :=
      HomologicalComplex.congr_hom
        (P.comparisonToAugmentedExact Q.complex Q.π f).property 0
    have hL : @Eq (P.complex.X 0 ⟶ Y)
        ((a ≫ Q.π).f 0) (a.f 0 ≫ Q.π.f 0) :=
      HomologicalComplex.comp_f a Q.π 0
    have hR : @Eq (P.complex.X 0 ⟶ Y)
        ((P.π ≫ (ChainComplex.single₀ C).map f).f 0) (P.π.f 0 ≫ f) :=
      (HomologicalComplex.comp_f P.π ((ChainComplex.single₀ C).map f) 0).trans
        (congrArg (fun z => P.π.f 0 ≫ z) (ChainComplex.single₀_map_f_zero f))
    exact hL.symm.trans (h₀.trans hR)
  rw [leftDerivedObjToAugmentedHom_eq F P Q.complex Q.π f a
    (P.comparisonToAugmentedExact Q.complex Q.π f).property n]
  exact (ProjectiveResolution.isoLeftDerivedObj_hom_naturality f P Q a ha₀ F n).symm

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F,G : C → D` additive, `τ : F → G`, `ρ : Q → Y[0]` a
quasi-isomorphism, and `f : X → Y`. The comparisons commute with
`L_nτ_X` and the homology map of the termwise transformation `τ_Q`. -/
theorem leftDerivedObjToAugmentedHom_naturality_functor
    {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G)
    {X Y : C} (Q : ChainComplex C ℕ)
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso ρ] (f : X ⟶ Y) (n : ℕ) :
    (NatTrans.leftDerived τ n).app X ≫ leftDerivedObjToAugmentedHom G Q ρ f n =
      leftDerivedObjToAugmentedHom F Q ρ f n ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex τ (ComplexShape.down ℕ)).app Q) n := by
  let P := projectiveResolution X
  let a := (P.comparisonToAugmentedExact Q ρ f).val
  let H := HomologicalComplex.homologyFunctor D (ComplexShape.down ℕ) n
  let HF := F.mapHomologicalComplex (ComplexShape.down ℕ) ⋙ H
  let HG := G.mapHomologicalComplex (ComplexShape.down ℕ) ⋙ H
  let TP := (NatTrans.mapHomologicalComplex τ (ComplexShape.down ℕ)).app P.complex
  let TQ := (NatTrans.mapHomologicalComplex τ (ComplexShape.down ℕ)).app Q
  have hI : (NatTrans.leftDerived τ n).app X ≫ (P.isoLeftDerivedObj G n).hom =
      (P.isoLeftDerivedObj F n).hom ≫ H.map TP :=
    ProjectiveResolution.isoLeftDerivedObj_hom_naturality_functor P τ n
  have hSquare : HF.map a ≫ H.map TQ = H.map TP ≫ HG.map a := by
    simpa only [HF, HG, TP, TQ, Functor.comp_map, Functor.map_comp] using
      congrArg H.map ((NatTrans.mapHomologicalComplex τ
        (ComplexShape.down ℕ)).naturality a)
  rw [leftDerivedObjToAugmentedHom_eq F P Q ρ f a
      (P.comparisonToAugmentedExact Q ρ f).property n,
    leftDerivedObjToAugmentedHom_eq G P Q ρ f a
      (P.comparisonToAugmentedExact Q ρ f).property n]
  change (NatTrans.leftDerived τ n).app X ≫
      ((P.isoLeftDerivedObj G n).hom ≫ HG.map a) =
    ((P.isoLeftDerivedObj F n).hom ≫ HF.map a) ≫ H.map TQ
  rw [← Category.assoc, hI, Category.assoc, ← hSquare, ← Category.assoc]

/-- Let `C,D` be abelian, with projective resolutions in `C`,
`F : C → D` additive, `ρ : Q → Y[0]` a quasi-isomorphism of
nonnegative chain complexes, and `f : X → Y`. In degree zero, the comparison followed by the
homology
augmentation `H₀(F(Q)) → F(Y)` equals the canonical augmentation
`L₀F(X) → F(X)` followed by `F(f)`. -/
theorem leftDerivedObjToAugmentedHom_zero_augmentation (F : C ⥤ D) [F.Additive]
    {X Y : C} (Q : ChainComplex C ℕ)
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso ρ] (f : X ⟶ Y) :
    leftDerivedObjToAugmentedHom F Q ρ f 0 ≫
        ChainComplex.mappedAugmentationHomologyZero F ρ =
      F.fromLeftDerivedZero.app X ≫ F.map f := by
  let P := projectiveResolution X
  let a := (P.comparisonToAugmentedExact Q ρ f).val
  let KP := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let KQ := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q
  let b := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map a
  have ha₀ : a.f 0 ≫ ρ.f 0 = P.π.f 0 ≫ f := by
    have h₀ : @Eq (P.complex.X 0 ⟶ Y)
        ((a ≫ ρ).f 0) ((P.π ≫ (ChainComplex.single₀ C).map f).f 0) :=
      HomologicalComplex.congr_hom (P.comparisonToAugmentedExact Q ρ f).property 0
    have hL : @Eq (P.complex.X 0 ⟶ Y) ((a ≫ ρ).f 0) (a.f 0 ≫ ρ.f 0) :=
      HomologicalComplex.comp_f a ρ 0
    have hR : @Eq (P.complex.X 0 ⟶ Y)
        ((P.π ≫ (ChainComplex.single₀ C).map f).f 0) (P.π.f 0 ≫ f) :=
      (HomologicalComplex.comp_f P.π ((ChainComplex.single₀ C).map f) 0).trans
        (congrArg (fun z => P.π.f 0 ≫ z) (ChainComplex.single₀_map_f_zero f))
    exact hL.symm.trans (h₀.trans hR)
  have hDesc : HomologicalComplex.opcyclesMap b 0 ≫
      ChainComplex.mappedAugmentationDesc F ρ = P.fromLeftDerivedZero' F ≫ F.map f := by
    apply (cancel_epi (KP.pOpcycles 0)).1
    rw [HomologicalComplex.p_opcyclesMap_assoc,
      ChainComplex.pOpcycles_comp_mappedAugmentationDesc,
      ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc]
    change F.map (a.f 0) ≫ F.map (ρ.f 0) = F.map (P.π.f 0) ≫ F.map f
    exact (F.map_comp (a.f 0) (ρ.f 0)).symm.trans
      ((congrArg F.map ha₀).trans (F.map_comp (P.π.f 0) f))
  rw [leftDerivedObjToAugmentedHom_eq F P Q ρ f a
    (P.comparisonToAugmentedExact Q ρ f).property 0]
  change ((P.isoLeftDerivedObj F 0).hom ≫ HomologicalComplex.homologyMap b 0) ≫
    (KQ.homologyι 0 ≫ ChainComplex.mappedAugmentationDesc F ρ) =
      F.fromLeftDerivedZero.app X ≫ F.map f
  rw [Category.assoc, HomologicalComplex.homologyι_naturality_assoc, hDesc]
  rw [P.fromLeftDerivedZero_eq F]
  simp only [Category.assoc]
  rfl

end CategoryTheory.Functor
