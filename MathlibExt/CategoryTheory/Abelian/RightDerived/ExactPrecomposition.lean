/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionNaturality
public import MathlibExt.CategoryTheory.Abelian.RightDerived.Precomposition
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Directional right-derived comparison under source change

Let `C`, `D`, `A` be abelian categories, with injective resolutions in
`C,D`, let `U : C → D` be additive and preserve homology, and let
`L : D → A` be additive. Mapping a coaugmented injective resolution
of `X` by `U` gives a coaugmented complex resolving `U(X)`.
Comparison with an injective resolution of `U(X)` gives the natural map
`R^n(U ⋙ L)(X) → R^nL(U(X))`.

This construction needs no injectivity of the terms of the mapped
complex and no left exactness of `L`. If `U` preserves injectives, the
map is the forward morphism of the right-derived precomposition
isomorphism. All category object and morphism universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD uA vA

namespace CategoryTheory.Functor


variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {A : Type uA} [Category.{vA} A] [Abelian A]

/-- For abelian `C`, `D` and additive `U : C → D`, a coaugmentation
`ι : X[0] → K` of a nonnegative cochain complex maps to the
coaugmentation `U(X)[0] → U(K)`, using the identification of `U(X[0])`
with the complex concentrated at degree zero. -/
def mapCochainCoaugmentation (U : C ⥤ D) [U.Additive]
    {X : C} {K : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ K) :
    (CochainComplex.single₀ D).obj (U.obj X) ⟶
      (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K :=
  (HomologicalComplex.singleMapHomologicalComplex U (ComplexShape.up ℕ) 0).inv.app X ≫
    (U.mapHomologicalComplex (ComplexShape.up ℕ)).map ι

/-- For abelian `C`, `D`, additive `U : C → D`, and a coaugmentation
`ι : X[0] → K`, the degree-zero map of the induced coaugmentation
`U(X)[0] → U(K)` is `U(ι⁰)`. -/
theorem mapCochainCoaugmentation_f_zero (U : C ⥤ D) [U.Additive]
    {X : C} {K : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ K) :
    (mapCochainCoaugmentation U ι).f 0 = U.map (ι.f 0) := by
  dsimp only [mapCochainCoaugmentation]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv]
  erw [Functor.map_id]
  change (𝟙 (U.obj X) ≫ 𝟙 (U.obj X)) ≫ U.map (ι.f 0) = U.map (ι.f 0)
  simp only [Category.id_comp]
  rfl

/-- For abelian `C`, `D` and additive homology-preserving `U : C → D`,
a quasi-isomorphism `ι : X[0] → K` induces a quasi-isomorphism
`U(X)[0] → U(K)`. -/
theorem mapCochainCoaugmentation_quasiIso (U : C ⥤ D) [U.Additive]
    [U.PreservesHomology] {X : C} {K : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ K) [QuasiIso ι] :
    QuasiIso (mapCochainCoaugmentation U ι) := by
  unfold mapCochainCoaugmentation
  infer_instance

/-- For abelian `C`, `D` and additive `U : C → D`, suppose
`ι : X[0] → K`, `κ : Y[0] → K′`, `f : X → Y` and `a : K → K′`
satisfy `ι ≫ a = f[0] ≫ κ`. Their induced coaugmentations satisfy
`U(ι) ≫ U(a) = U(f)[0] ≫ U(κ)`. -/
theorem mapCochainCoaugmentation_naturality (U : C ⥤ D) [U.Additive]
    {X Y : C} {K K' : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ K)
    (κ : (CochainComplex.single₀ C).obj Y ⟶ K')
    (f : X ⟶ Y) (a : K ⟶ K')
    (ha : ι ≫ a = (CochainComplex.single₀ C).map f ≫ κ) :
    mapCochainCoaugmentation U ι ≫
        (U.mapHomologicalComplex (ComplexShape.up ℕ)).map a =
      (CochainComplex.single₀ D).map (U.map f) ≫ mapCochainCoaugmentation U κ := by
  unfold mapCochainCoaugmentation
  rw [Category.assoc, ← Functor.map_comp, ha, Functor.map_comp, ← Category.assoc]
  have h := (HomologicalComplex.singleMapHomologicalComplex U
    (ComplexShape.up ℕ) 0).inv.naturality f
  change (CochainComplex.single₀ D).map (U.map f) ≫
      (HomologicalComplex.singleMapHomologicalComplex U (ComplexShape.up ℕ) 0).inv.app Y =
    (HomologicalComplex.singleMapHomologicalComplex U (ComplexShape.up ℕ) 0).inv.app X ≫
      (U.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((CochainComplex.single₀ C).map f) at h
  rw [← h, Category.assoc]

section Derived

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  (U : C ⥤ D) [U.Additive] [U.PreservesHomology]
  (L : D ⥤ A) [L.Additive]

/-- Let `C`, `D`, `A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology, and `L : D → A` additive.
An injective resolution `I` of `X` computes the directional comparison
`R^n(U ⋙ L)(X) → R^nL(U(X))` through the exact coaugmented complex
`U(I)`. -/
def rightDerivedPrecompHomWithResolution (n : ℕ) {X : C} (I : InjectiveResolution X) :
    ((U ⋙ L).rightDerived n).obj X ⟶ (L.rightDerived n).obj (U.obj X) := by
  let : QuasiIso (mapCochainCoaugmentation U I.ι) :=
    mapCochainCoaugmentation_quasiIso U I.ι
  exact (I.isoRightDerivedObj (U ⋙ L) n).hom ≫
    HomologicalComplex.homologyMap
      ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
        (Iso.refl (U ⋙ L)) (ComplexShape.up ℕ)).inv.app I.cocomplex) n ≫
      L.augmentedResolutionToRightDerivedHom
        ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
        (mapCochainCoaugmentation U I.ι) n

/-- Let `C`, `D`, `A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology, and `L : D → A` additive.
For `f : X → Y` and injective resolutions of `X,Y`, the computed
comparisons commute with `R^n(U ⋙ L)(f)` and `R^nL(U(f))`. -/
theorem rightDerivedPrecompHomWithResolution_naturality (n : ℕ)
    {X Y : C} (f : X ⟶ Y) (I : InjectiveResolution X) (J : InjectiveResolution Y) :
    ((U ⋙ L).rightDerived n).map f ≫ rightDerivedPrecompHomWithResolution U L n J =
      rightDerivedPrecompHomWithResolution U L n I ≫ (L.rightDerived n).map (U.map f) := by
  let a := InjectiveResolution.descHom f I J
  let b := (U.mapHomologicalComplex (ComplexShape.up ℕ)).map a.hom
  let ι := mapCochainCoaugmentation U I.ι
  let κ := mapCochainCoaugmentation U J.ι
  let : QuasiIso ι := mapCochainCoaugmentation_quasiIso U I.ι
  let : QuasiIso κ := mapCochainCoaugmentation_quasiIso U J.ι
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n
  let χ := Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.up ℕ)
  let cI := L.augmentedResolutionToRightDerivedHom
    ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ι n
  let cJ := L.augmentedResolutionToRightDerivedHom
    ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex) κ n
  have hι : ι ≫ b = (CochainComplex.single₀ D).map (U.map f) ≫ κ :=
    mapCochainCoaugmentation_naturality U I.ι J.ι f a.hom a.ι_comp_hom
  have h₁ : ((U ⋙ L).rightDerived n).map f ≫ (J.isoRightDerivedObj (U ⋙ L) n).hom =
      (I.isoRightDerivedObj (U ⋙ L) n).hom ≫
        H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.up ℕ)).map a.hom) :=
    InjectiveResolution.isoRightDerivedObj_hom_naturality f I J a.hom
      (by
        have h : @Eq (X ⟶ J.cocomplex.X 0) (I.ι.f 0 ≫ a.hom.f 0)
            (f ≫ J.ι.f 0) :=
          (a.ι_f_zero_comp_hom_f_zero).trans
            (congrArg (fun q => q ≫ J.ι.f 0) (CochainComplex.single₀_map_f_zero f))
        exact h) (U ⋙ L) n
  have h₂ : H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.up ℕ)).map a.hom) ≫
      H.map (χ.inv.app J.cocomplex) =
    H.map (χ.inv.app I.cocomplex) ≫
      H.map ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map b) :=
    (isoWhiskerRight χ.symm H).hom.naturality a.hom
  have h₃ : H.map ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map b) ≫ cJ =
      cI ≫ (L.rightDerived n).map (U.map f) :=
    L.augmentedResolutionToRightDerivedHom_naturality ι κ (U.map f) b hι n
  have s₁ : CommSq (I.isoRightDerivedObj (U ⋙ L) n).hom
      (((U ⋙ L).rightDerived n).map f)
      (H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.up ℕ)).map a.hom))
      (J.isoRightDerivedObj (U ⋙ L) n).hom := ⟨h₁.symm⟩
  have s₂ : CommSq (H.map (χ.inv.app I.cocomplex))
      (H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.up ℕ)).map a.hom))
      (H.map ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map b))
      (H.map (χ.inv.app J.cocomplex)) := ⟨h₂.symm⟩
  have s₃ : CommSq cI (H.map ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map b))
      ((L.rightDerived n).map (U.map f)) cJ := ⟨h₃.symm⟩
  change ((U ⋙ L).rightDerived n).map f ≫
      (J.isoRightDerivedObj (U ⋙ L) n).hom ≫ H.map (χ.inv.app J.cocomplex) ≫ cJ =
    ((I.isoRightDerivedObj (U ⋙ L) n).hom ≫ H.map (χ.inv.app I.cocomplex) ≫ cI) ≫
      (L.rightDerived n).map (U.map f)
  exact (s₁.horiz_comp (s₂.horiz_comp s₃)).w.symm

/-- Let `C`, `D`, `A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology, and `L : D → A` additive.
Any two injective resolutions of `X` compute the same map
`R^n(U ⋙ L)(X) → R^nL(U(X))`. -/
theorem rightDerivedPrecompHomWithResolution_independent (n : ℕ) {X : C}
    (I J : InjectiveResolution X) :
    rightDerivedPrecompHomWithResolution U L n I =
      rightDerivedPrecompHomWithResolution U L n J := by
  have h := rightDerivedPrecompHomWithResolution_naturality U L n (𝟙 X) I J
  simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using h.symm

/-- Let `C`, `D`, `A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology, and `L : D → A` additive.
The resolution comparisons give a natural transformation
`R^n(U ⋙ L) → U ⋙ R^nL`. -/
def rightDerivedPrecompHomOfPreservesHomology (n : ℕ) :
    (U ⋙ L).rightDerived n ⟶ U ⋙ L.rightDerived n where
  app X := rightDerivedPrecompHomWithResolution U L n (injectiveResolution X)
  naturality {X Y} f := rightDerivedPrecompHomWithResolution_naturality U L n f
    (injectiveResolution X) (injectiveResolution Y)

/-- Let `C`, `D`, `A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology, and `L : D → A` additive.
At `X`, the natural transformation `R^n(U ⋙ L) → U ⋙ R^nL`
is computed by any injective resolution `I` of `X`. -/
theorem rightDerivedPrecompHomOfPreservesHomology_app (n : ℕ) {X : C}
    (I : InjectiveResolution X) :
    (rightDerivedPrecompHomOfPreservesHomology U L n).app X =
      rightDerivedPrecompHomWithResolution U L n I :=
  rightDerivedPrecompHomWithResolution_independent U L n (injectiveResolution X) I

/-- Let `C`, `D`, `A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology and injective objects,
and `L : D → A` additive. The directional comparison
`R^n(U ⋙ L) → U ⋙ R^nL` is the forward map of the canonical
precomposition isomorphism. -/
theorem rightDerivedPrecompHomOfPreservesHomology_eq_hom
    [U.PreservesInjectiveObjects] (n : ℕ) :
    rightDerivedPrecompHomOfPreservesHomology U L n = (rightDerivedPrecompIso U L n).hom := by
  apply NatTrans.ext
  funext X
  let I := injectiveResolution X
  let J := U.mapInjectiveResolution I
  let : QuasiIso (mapCochainCoaugmentation U I.ι) := mapCochainCoaugmentation_quasiIso U I.ι
  rw [rightDerivedPrecompHomOfPreservesHomology_app U L n I,
    rightDerivedPrecompIso_hom_app_eq U L n I]
  unfold rightDerivedPrecompHomWithResolution rightDerivedPrecompIsoWithResolution
  dsimp only
  change (I.isoRightDerivedObj (U ⋙ L) n).hom ≫
      HomologicalComplex.homologyMap
        ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
          (Iso.refl (U ⋙ L)) (ComplexShape.up ℕ)).inv.app I.cocomplex) n ≫
        L.augmentedResolutionToRightDerivedHom J.cocomplex J.ι n = _
  rw [augmentedResolutionToRightDerivedHom_injectiveResolution]
  simp only [Iso.trans_hom, Iso.symm_hom]
  unfold rightDerivedPrecompHomologyIso
  rfl

end Derived

section FunctorNaturality

variable [HasInjectiveResolutions C]

private theorem augmentedComparison_naturality_functor
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    {X : C} (K : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ K) [QuasiIso ι] (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) n ≫
      G.augmentedResolutionToRightDerivedHom K ι n =
    F.augmentedResolutionToRightDerivedHom K ι n ≫ (NatTrans.rightDerived α n).app X := by
  let J := injectiveResolution X
  let r := augmentedResolutionComparison K ι
  let H := HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n
  let β := NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)
  have hSquare : H.map (β.app K) ≫ H.map ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map r.val) =
      H.map ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map r.val) ≫ H.map (β.app J.cocomplex) :=
    (H.map_comp _ _).symm.trans
      ((congrArg H.map (β.naturality r.val).symm).trans (H.map_comp _ _))
  have hLast := J.isoRightDerivedObj_inv_naturality_functor α n
  change H.map (β.app J.cocomplex) ≫ (J.isoRightDerivedObj G n).inv =
    (J.isoRightDerivedObj F n).inv ≫ (NatTrans.rightDerived α n).app X at hLast
  change H.map (β.app K) ≫
      (H.map ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map r.val) ≫
        (J.isoRightDerivedObj G n).inv) =
    (H.map ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map r.val) ≫
      (J.isoRightDerivedObj F n).inv) ≫ (NatTrans.rightDerived α n).app X
  calc
    _ = (H.map (β.app K) ≫ H.map ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map r.val)) ≫
        (J.isoRightDerivedObj G n).inv := (Category.assoc _ _ _).symm
    _ = (H.map ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map r.val) ≫
        H.map (β.app J.cocomplex)) ≫ (J.isoRightDerivedObj G n).inv :=
      congrArg (fun f => f ≫ (J.isoRightDerivedObj G n).inv) hSquare
    _ = H.map ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map r.val) ≫
        (H.map (β.app J.cocomplex) ≫ (J.isoRightDerivedObj G n).inv) := Category.assoc _ _ _
    _ = H.map ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map r.val) ≫
        ((J.isoRightDerivedObj F n).inv ≫ (NatTrans.rightDerived α n).app X) :=
      congrArg (fun f => H.map ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map r.val) ≫ f) hLast
    _ = _ := (Category.assoc _ _ _).symm

variable [HasInjectiveResolutions D]
  (U : C ⥤ D) [U.Additive] [U.PreservesHomology]

/-- Let `C`, `D`, `A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology, and `L,M : D → A` additive.
For `α : L → M`, the directional comparisons satisfy
`R^n(U ⋙ α) ≫ η_M = η_L ≫ (U ⋙ R^nα)`. -/
@[reassoc]
theorem rightDerivedPrecompHomOfPreservesHomology_naturality_functor
    {L M : D ⥤ A} [L.Additive] [M.Additive] (α : L ⟶ M) (n : ℕ) :
    NatTrans.rightDerived (whiskerLeft U α) n ≫
        rightDerivedPrecompHomOfPreservesHomology U M n =
      rightDerivedPrecompHomOfPreservesHomology U L n ≫
        whiskerLeft U (NatTrans.rightDerived α n) := by
  apply NatTrans.ext
  funext X
  let I := injectiveResolution X
  let K := (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let ι := mapCochainCoaugmentation U I.ι
  let : QuasiIso ι := mapCochainCoaugmentation_quasiIso U I.ι
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n
  let χL := Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.up ℕ)
  let χM := Functor.mapHomologicalComplexCompIso (F := U) (G := M)
    (Iso.refl (U ⋙ M)) (ComplexShape.up ℕ)
  let a := (NatTrans.mapHomologicalComplex (whiskerLeft U α)
    (ComplexShape.up ℕ)).app I.cocomplex
  let b := (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K
  have h₁ := I.isoRightDerivedObj_hom_naturality_functor (whiskerLeft U α) n
  have hχ : a ≫ χM.inv.app I.cocomplex = χL.inv.app I.cocomplex ≫ b := by
    apply HomologicalComplex.hom_ext
    intro i
    change α.app (U.obj (I.cocomplex.X i)) ≫ 𝟙 _ =
      𝟙 _ ≫ α.app (U.obj (I.cocomplex.X i))
    rw [Category.comp_id, Category.id_comp]
  have h₂ : H.map a ≫ H.map (χM.inv.app I.cocomplex) =
      H.map (χL.inv.app I.cocomplex) ≫ H.map b :=
    (H.map_comp _ _).symm.trans ((congrArg H.map hχ).trans (H.map_comp _ _))
  have h₃ := augmentedComparison_naturality_functor α K ι n
  let cL := L.augmentedResolutionToRightDerivedHom K ι n
  let cM := M.augmentedResolutionToRightDerivedHom K ι n
  have s₁ : CommSq (I.isoRightDerivedObj (U ⋙ L) n).hom
      ((NatTrans.rightDerived (whiskerLeft U α) n).app X) (H.map a)
      (I.isoRightDerivedObj (U ⋙ M) n).hom := ⟨h₁.symm⟩
  have s₂ : CommSq (H.map (χL.inv.app I.cocomplex)) (H.map a) (H.map b)
      (H.map (χM.inv.app I.cocomplex)) := ⟨h₂.symm⟩
  have s₃ : CommSq cL (H.map b) ((NatTrans.rightDerived α n).app (U.obj X)) cM := ⟨h₃.symm⟩
  change (NatTrans.rightDerived (whiskerLeft U α) n).app X ≫
      ((I.isoRightDerivedObj (U ⋙ M) n).hom ≫ H.map (χM.inv.app I.cocomplex) ≫ cM) =
    ((I.isoRightDerivedObj (U ⋙ L) n).hom ≫ H.map (χL.inv.app I.cocomplex) ≫ cL) ≫
      (NatTrans.rightDerived α n).app (U.obj X)
  exact (s₁.horiz_comp (s₂.horiz_comp s₃)).w.symm

end FunctorNaturality

section AugmentedSource

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  (U : C ⥤ D) [U.Additive] [U.PreservesHomology]
  (L : D ⥤ A) [L.Additive]

/-- Let `C`, `D`, `A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology, and `L : D → A` additive.
For any coaugmentation quasi-isomorphism `ι : X[0] → K`, composing
`Hⁿ((U ⋙ L)(K)) → R^n(U ⋙ L)(X)` with the directional comparison
equals the comparison `Hⁿ(L(U(K))) → R^nL(U(X))`, after the natural
identification of the two mapped complexes. -/
theorem augmentedResolutionToRightDerivedHom_precomp
    {X : C} (K : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ K) [QuasiIso ι] (n : ℕ) :
    (U ⋙ L).augmentedResolutionToRightDerivedHom K ι n ≫
        (rightDerivedPrecompHomOfPreservesHomology U L n).app X =
      letI : QuasiIso (mapCochainCoaugmentation U ι) := mapCochainCoaugmentation_quasiIso U ι
      HomologicalComplex.homologyMap
        ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
          (Iso.refl (U ⋙ L)) (ComplexShape.up ℕ)).inv.app K) n ≫
        L.augmentedResolutionToRightDerivedHom
          ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
          (mapCochainCoaugmentation U ι) n := by
  let I := injectiveResolution X
  let r := augmentedResolutionComparison K ι
  let M := U.mapHomologicalComplex (ComplexShape.up ℕ)
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n
  let χ := Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.up ℕ)
  let κ := mapCochainCoaugmentation U ι
  let κI := mapCochainCoaugmentation U I.ι
  let : QuasiIso κ := mapCochainCoaugmentation_quasiIso U ι
  let : QuasiIso κI := mapCochainCoaugmentation_quasiIso U I.ι
  have hρ : ι ≫ r.val = (CochainComplex.single₀ C).map (𝟙 X) ≫ I.ι := by
    simpa only [Functor.map_id, Category.id_comp] using r.property
  have hκ := mapCochainCoaugmentation_naturality U ι I.ι (𝟙 X) r.val hρ
  have hκ' : κ ≫ M.map r.val = (CochainComplex.single₀ D).map (𝟙 (U.obj X)) ≫ κI := by
    simpa only [Functor.map_id] using hκ
  have hAug := L.augmentedResolutionToRightDerivedHom_naturality κ κI
    (𝟙 (U.obj X)) (M.map r.val) hκ' n
  have hLast : H.map ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map (M.map r.val)) ≫
      L.augmentedResolutionToRightDerivedHom (M.obj I.cocomplex) κI n =
    L.augmentedResolutionToRightDerivedHom (M.obj K) κ n := by
    change HomologicalComplex.homologyMap
      ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map (M.map r.val)) n ≫
        L.augmentedResolutionToRightDerivedHom
          ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) κI n = _
    exact hAug.trans
      ((congrArg (fun q => L.augmentedResolutionToRightDerivedHom
        ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) κ n ≫ q)
          ((L.rightDerived n).map_id (U.obj X))).trans (Category.comp_id _))
  have hχ : H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.up ℕ)).map r.val) ≫
      H.map (χ.inv.app I.cocomplex) = H.map (χ.inv.app K) ≫
        H.map ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map (M.map r.val)) :=
    (isoWhiskerRight χ.symm H).hom.naturality r.val
  rw [rightDerivedPrecompHomOfPreservesHomology_app U L n I]
  change (H.map (((U ⋙ L).mapHomologicalComplex (ComplexShape.up ℕ)).map r.val) ≫
      (I.isoRightDerivedObj (U ⋙ L) n).inv) ≫
    ((I.isoRightDerivedObj (U ⋙ L) n).hom ≫ H.map (χ.inv.app I.cocomplex) ≫
      L.augmentedResolutionToRightDerivedHom (M.obj I.cocomplex) κI n) = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hχ, Category.assoc, hLast]
  rfl

end AugmentedSource

end CategoryTheory.Functor
