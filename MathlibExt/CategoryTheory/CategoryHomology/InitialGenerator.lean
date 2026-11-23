/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.InitialVanishing
public import MathlibExt.Algebra.Homology.HomologyMapSquare
public import MathlibExt.Algebra.Homology.ChainComplex.HomologyZero

/-!
# Canonical coefficient homology classes in degree zero

Every coefficient object maps canonically to degree-zero coefficient homology
through its alternating-bar summand. These maps are natural in the coefficients.
At an initial object, an arrow-inverting coefficient functor gives the identity
under the canonical initial-object H₀ isomorphism.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe uC vC uD vD

namespace CategoryTheory.CategoryHomology

variable {D : Type uD} [Category.{vD} D] [Abelian D]

/-- Deprecated compatibility name for the canonical degree-zero chain class.
New clients can use `ChainComplex.homologyZeroClass` under its weaker hypotheses. -/
@[deprecated ChainComplex.homologyZeroClass (since := "2026-10-25")]
abbrev homologyZeroProjection (K : ChainComplex D ℕ) :
    K.X 0 ⟶ K.homology 0 :=
  ChainComplex.homologyZeroClass K

/-- Deprecated compatibility statement for naturality of the canonical class. -/
@[deprecated ChainComplex.homologyZeroClass_naturality (since := "2026-10-25"), reassoc]
theorem homologyZeroProjection_naturality
    {K L : ChainComplex D ℕ} (f : K ⟶ L) :
    homologyZeroProjection K ≫ HomologicalComplex.homologyMap f 0 =
      f.f 0 ≫ homologyZeroProjection L :=
  ChainComplex.homologyZeroClass_naturality f

attribute [deprecated ChainComplex.homologyZeroClass_naturality_assoc
  (since := "2026-10-25")] homologyZeroProjection_naturality_assoc

/-- Projecting a degree-zero map gives the homology class of its cycle lift. -/
theorem comp_homologyZeroProjection_eq_class
    (K : ChainComplex D ℕ) {V : D} (k : V ⟶ K.X 0) :
    k ≫ ChainComplex.homologyZeroClass K =
      K.liftCycles k 0 (by simp) (by simp) ≫ K.homologyπ 0 := by
  change k ≫ ChainComplex.homologyZeroClass K =
    K.liftCycles k 0 (by simp) (by simp) ≫ K.homologyπ 0
  rw [← cancel_mono (K.homologyι 0)]
  have h : K.isoHomologyι₀.inv ≫ K.homologyι 0 = 𝟙 _ :=
    K.isoHomologyι₀.inv_hom_id
  simp only [ChainComplex.homologyZeroClass,
    Category.assoc, h, Category.comp_id,
    HomologicalComplex.homology_π_ι, HomologicalComplex.liftCycles_i_assoc]

variable {C : Type uC} [Category.{vC} C]
  [HasCoproducts.{max uC vC} D]

/-- The canonical normalized-to-alternating comparison on coefficient H₀. -/
@[reducible]
def coefficientHomologyZeroComparison (M : C ⥤ D) :
    homologyWithCoefficients M 0 ≅ (coefficientBarComplex M).homology 0 :=
  (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := coefficientBarSimplicial M)).toHomologyIso 0

/-- The degree-zero coefficient homology class of the bar summand at an object. -/
def coefficientHomologyClass (M : C ⥤ D) (i : C) :
    M.obj i ⟶ homologyWithCoefficients M 0 :=
  coefficientBarι M (ComposableArrows.mk₀ i) ≫
    ChainComplex.homologyZeroClass (coefficientBarComplex M) ≫
    (coefficientHomologyZeroComparison M).inv

/-- The inverse normalized-to-alternating comparison is natural in coefficients. -/
@[reassoc]
theorem coefficientHomologyZeroComparison_inv_naturality
    {M N : C ⥤ D} (α : M ⟶ N) :
    (coefficientHomologyZeroComparison M).inv ≫
        (homologyWithCoefficientsFunctor 0).map α =
      HomologicalComplex.homologyMap
          ((AlgebraicTopology.alternatingFaceMapComplex D).map
            (coefficientBarSimplicialMap α)) 0 ≫
        (coefficientHomologyZeroComparison N).inv := by
  change HomologicalComplex.homologyMap
      (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
        (coefficientBarSimplicial M)) 0 ≫
      HomologicalComplex.homologyMap
        ((AlgebraicTopology.normalizedMooreComplex D).map
          (coefficientBarSimplicialMap α)) 0 =
      HomologicalComplex.homologyMap
        ((AlgebraicTopology.alternatingFaceMapComplex D).map
          (coefficientBarSimplicialMap α)) 0 ≫
      HomologicalComplex.homologyMap
        (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex
          (coefficientBarSimplicial N)) 0
  exact HomologicalComplex.homologyMap_square
    (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex_naturality
      (coefficientBarSimplicialMap α)).symm 0

/-- Coefficient homology classes are natural in the coefficient functor. -/
@[reassoc]
theorem coefficientHomologyClass_naturality
    {M N : C ⥤ D} (α : M ⟶ N) (i : C) :
    coefficientHomologyClass M i ≫ (homologyWithCoefficientsFunctor 0).map α =
      α.app i ≫ coefficientHomologyClass N i := by
  let K := coefficientBarComplex M
  let L := coefficientBarComplex N
  let f : K ⟶ L := (AlgebraicTopology.alternatingFaceMapComplex D).map
    (coefficientBarSimplicialMap α)
  let ιM : M.obj i ⟶ K.X 0 := coefficientBarι M (ComposableArrows.mk₀ i)
  let ιN : N.obj i ⟶ L.X 0 := coefficientBarι N (ComposableArrows.mk₀ i)
  let eM : homologyWithCoefficients M 0 ≅ K.homology 0 :=
    coefficientHomologyZeroComparison M
  let eN : homologyWithCoefficients N 0 ≅ L.homology 0 :=
    coefficientHomologyZeroComparison N
  let Hα : homologyWithCoefficients M 0 ⟶ homologyWithCoefficients N 0 :=
    (homologyWithCoefficientsFunctor 0).map α
  let Hf : K.homology 0 ⟶ L.homology 0 := HomologicalComplex.homologyMap f 0
  have hι : ιM ≫ f.f 0 = α.app i ≫ ιN := by
    have hf : f.f 0 = coefficientBarMap α 0 := by
      change ((AlgebraicTopology.alternatingFaceMapComplex D).map
        (coefficientBarSimplicialMap α)).f 0 = _
      rw [AlgebraicTopology.alternatingFaceMapComplex_map_f]
      exact SimplicialObject.Data.toSimplicialNatTrans_app_mk
        (coefficientBarDataMap α) 0
    rw [hf]
    exact coefficientBarι_map α (ComposableArrows.mk₀ i)
  have hρ : eM.inv ≫ Hα =
      Hf ≫ eN.inv :=
    coefficientHomologyZeroComparison_inv_naturality α
  have hp : ChainComplex.homologyZeroClass K ≫ Hf =
      f.f 0 ≫ ChainComplex.homologyZeroClass L := ChainComplex.homologyZeroClass_naturality f
  change (ιM ≫ ChainComplex.homologyZeroClass K ≫ eM.inv) ≫
      Hα =
    α.app i ≫ (ιN ≫ ChainComplex.homologyZeroClass L ≫ eN.inv)
  calc
    _ = ιM ≫ ChainComplex.homologyZeroClass K ≫
        (eM.inv ≫ Hα) := by
      simp only [Category.assoc]
    _ = ιM ≫ ChainComplex.homologyZeroClass K ≫
        (Hf ≫ eN.inv) := by rw [hρ]
    _ = ιM ≫ (ChainComplex.homologyZeroClass K ≫ Hf) ≫
        eN.inv := by simp only [Category.assoc]
    _ = ιM ≫ (f.f 0 ≫ ChainComplex.homologyZeroClass L) ≫ eN.inv := by rw [hp]
    _ = (ιM ≫ f.f 0) ≫ ChainComplex.homologyZeroClass L ≫ eN.inv := by
      simp only [Category.assoc]
    _ = (α.app i ≫ ιN) ≫ ChainComplex.homologyZeroClass L ≫ eN.inv := by rw [hι]
    _ = _ := by simp only [Category.assoc]

/-- Under the normalized-to-alternating comparison, a coefficient homology class
is the projection of its original bar summand. -/
@[reassoc]
theorem coefficientHomologyClass_comp_coefficientHomologyZeroComparison_hom
    (M : C ⥤ D) (i : C) :
    coefficientHomologyClass M i ≫ (coefficientHomologyZeroComparison M).hom =
      coefficientBarι M (ComposableArrows.mk₀ i) ≫
        ChainComplex.homologyZeroClass (coefficientBarComplex M) := by
  dsimp only [coefficientHomologyClass]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private lemma constantCoefficientBarι_comp_complexIso
    (R : D) (i : C) :
    coefficientBarι ((Functor.const C).obj R) (ComposableArrows.mk₀ i) ≫
        (constantCoefficientBarComplexIso C D R).hom.f 0 =
      (nerve C).ιChainComplex (ComposableArrows.mk₀ i) := by
  let τ := (sigmaConst : D ⥤ (Type (max uC vC) ⥤ D)).obj R
  have hs : (constantCoefficientBarSimplicialIso C D R).hom.app
      (Opposite.op (SimplexCategory.mk 0)) = 𝟙 _ := by
    change (SimplicialObject.Data.toSimplicialObject_mapObjIso
        τ (nerveData C)).inv.app (Opposite.op (SimplexCategory.mk 0)) ≫
      τ.map ((nerveDataSimplicialIso C).hom.app
        (Opposite.op (SimplexCategory.mk 0))) = 𝟙 _
    erw [SimplicialObject.Data.toSimplicialObject_mapObjIso_inv_app_mk,
      nerveDataSimplicialIso_hom_app, Functor.map_id, Category.id_comp]
    rfl
  change coefficientBarι ((Functor.const C).obj R) (ComposableArrows.mk₀ i) ≫
    ((AlgebraicTopology.alternatingFaceMapComplex D).map
      (constantCoefficientBarSimplicialIso C D R).hom).f 0 = _
  erw [AlgebraicTopology.alternatingFaceMapComplex_map_f, hs, Category.comp_id]
  rfl

private lemma constant_coefficientHomologyClass_augmentation
    {i : C} (hi : IsInitial i) (R : D) :
    coefficientHomologyClass ((Functor.const C).obj R) i ≫
        (homologyWithConstantCoefficientsIso C D R 0).hom ≫
        (nerveInitialHomologyZeroIso hi R).hom = 𝟙 R := by
  let M : C ⥤ D := (Functor.const C).obj R
  let K := coefficientBarComplex M
  let L := (nerve C).chainComplex R
  let e : homologyWithCoefficients M 0 ≅ K.homology 0 :=
    coefficientHomologyZeroComparison M
  let c : K ≅ L := constantCoefficientBarComplexIso C D R
  let ι : R ⟶ K.X 0 := coefficientBarι M (ComposableArrows.mk₀ i)
  let ιN : R ⟶ L.X 0 := (nerve C).ιChainComplex (ComposableArrows.mk₀ i)
  let ε : L.homology 0 ⟶ R := (nerve C).homology₀ε R
  have hc : (homologyWithConstantCoefficientsIso C D R 0).hom =
      e.hom ≫ HomologicalComplex.homologyMap c.hom 0 := by rfl
  have hz : (nerveInitialHomologyZeroIso hi R).hom = ε := by rfl
  have hp : ChainComplex.homologyZeroClass K ≫ HomologicalComplex.homologyMap c.hom 0 =
      c.hom.f 0 ≫ ChainComplex.homologyZeroClass L :=
    ChainComplex.homologyZeroClass_naturality c.hom
  have hι : ι ≫ c.hom.f 0 = ιN := constantCoefficientBarι_comp_complexIso R i
  change (ι ≫ ChainComplex.homologyZeroClass K ≫ e.inv) ≫
      (homologyWithConstantCoefficientsIso C D R 0).hom ≫
      (nerveInitialHomologyZeroIso hi R).hom = 𝟙 R
  rw [hc, hz]
  calc
    _ = ι ≫ ChainComplex.homologyZeroClass K ≫ (e.inv ≫ e.hom) ≫
        HomologicalComplex.homologyMap c.hom 0 ≫ ε := by simp only [Category.assoc]
    _ = ι ≫ ChainComplex.homologyZeroClass K ≫ HomologicalComplex.homologyMap c.hom 0 ≫ ε := by
      rw [e.inv_hom_id]
      erw [Category.id_comp]
    _ = ι ≫ (ChainComplex.homologyZeroClass K ≫ HomologicalComplex.homologyMap c.hom 0) ≫ ε := by
      simp only [Category.assoc]
    _ = ι ≫ (c.hom.f 0 ≫ ChainComplex.homologyZeroClass L) ≫ ε := by rw [hp]
    _ = (ι ≫ c.hom.f 0) ≫ ChainComplex.homologyZeroClass L ≫ ε := by simp only [Category.assoc]
    _ = ιN ≫ ChainComplex.homologyZeroClass L ≫ ε := by rw [hι]
    _ = (L.liftCycles ιN 0 (by simp) (by simp) ≫ L.homologyπ 0) ≫ ε := by
      simpa only [Category.assoc] using congrArg
        (fun k : R ⟶ L.homology 0 ↦ k ≫ ε) (comp_homologyZeroProjection_eq_class L ιN)
    _ = 𝟙 R := by
      simpa only [ιN, L, ε, Category.assoc] using
        SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
          (X := nerve C) (R := R) (ComposableArrows.mk₀ i)

/-- The actual initial coefficient-bar summand represents the identity under
its existing canonical initial-object H₀ isomorphism. The summand passes
through the actual alternating quotient and inverse Dold–Kan homology map. -/
theorem coefficientBarι_comp_homologyWithCoefficientsZeroIsoOfIsInitial_hom
    (M : C ⥤ D) [∀ {X Y : C} (f : X ⟶ Y), IsIso (M.map f)]
    (i : C) (hi : IsInitial i) :
    let K : ChainComplex D ℕ := coefficientBarComplex M
    let e : homologyWithCoefficients M 0 ≅ K.homology 0 :=
      (AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
          (Y := coefficientBarSimplicial M)).toHomologyIso 0
    coefficientBarι M (ComposableArrows.mk₀ i) ≫
        K.pOpcycles 0 ≫ K.isoHomologyι₀.inv ≫ e.inv ≫
        (homologyWithCoefficientsZeroIsoOfIsInitial M i hi).hom =
      𝟙 (M.obj i) := by
  let t := constIsoOfIsInitial M i hi
  have ht : t.hom.app i = 𝟙 (M.obj i) := by
    change M.map (hi.to i) = 𝟙 _
    rw [hi.hom_ext (hi.to i) (𝟙 i), M.map_id]
  have hti : t.inv.app i = 𝟙 (M.obj i) := by
    have h : t.hom.app i ≫ t.inv.app i = 𝟙 (M.obj i) :=
      NatTrans.congr_app t.hom_inv_id i
    erw [ht, Category.id_comp] at h
    exact h
  have hn := coefficientHomologyClass_naturality t.inv i
  rw [hti, Category.id_comp] at hn
  suffices h : coefficientHomologyClass M i ≫
      (homologyWithCoefficientsZeroIsoOfIsInitial M i hi).hom = 𝟙 (M.obj i) by
    dsimp only [coefficientHomologyClass, ChainComplex.homologyZeroClass,
      coefficientHomologyZeroComparison] at h
    erw [Category.assoc, Category.assoc, Category.assoc] at h
    exact h
  have hz : (homologyWithCoefficientsZeroIsoOfIsInitial M i hi).hom =
      (homologyWithCoefficientsFunctor 0).map t.inv ≫
        (homologyWithConstantCoefficientsIso C D (M.obj i) 0).hom ≫
        (nerveInitialHomologyZeroIso hi (M.obj i)).hom := by
    rfl
  erw [hz, ← Category.assoc (coefficientHomologyClass M i)
      ((homologyWithCoefficientsFunctor 0).map t.inv)
      ((homologyWithConstantCoefficientsIso C D (M.obj i) 0).hom ≫
        (nerveInitialHomologyZeroIso hi (M.obj i)).hom), hn]
  exact constant_coefficientHomologyClass_augmentation hi (M.obj i)


end CategoryTheory.CategoryHomology
