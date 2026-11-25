/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.DerivedCategory.LeftDerivedMinusNaturality

/-!
# Families of canonical left derived functors

An arbitrary parameter category may index a family of additive functors
between abelian categories. The native derived natural transformations
make the family functorial. On any bounded-above projective source complex,
the canonical counit gives a natural computation isomorphism in the parameter.

The parameter is unrestricted. No exactness of its functors is assumed.
Source, target, parameter and derived-category universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.DerivedCategory

universe uC vC uD vD uI vI wC wCo wD wDo

namespace DerivedCategory.CanonicalLeft.Family

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wCo} Cᵒᵖ]
  [HasDerivedCategory.{wD} D] [HasDerivedCategory.{wDo} Dᵒᵖ]
  [EnoughProjectives C]
  {I : Type uI} [Category.{vI} I]
  (F : I ⥤ (C ⥤ D)) [∀ i : I, (F.obj i).Additive]

/-- Derive every functor in the actual parameter family using native lifted maps. -/
def derived : I ⥤ (DerivedCategory.Minus C ⥤ DerivedCategory.Minus D) where
  obj i := CanonicalLeft.leftDerived (F.obj i)
  map f := Naturality.lift (F.map f)
  map_id i := by rw [F.map_id i, Naturality.lift_id]
  map_comp f g := by rw [F.map_comp f g, Naturality.lift_comp]

/-- Uncurrying retains the actual parameter and the canonical derived source object. -/
def bifunctor : I × DerivedCategory.Minus C ⥤ DerivedCategory.Minus D :=
  Functor.uncurry.obj (derived F)

/-- The same additive functor family on bounded-above complexes before derivation. -/
def underived : I ⥤ (BoundedAboveDual.Complex C ⥤ DerivedCategory.Minus D) where
  obj i := CanonicalLeft.underived (F.obj i)
  map f := Naturality.underivedMap (F.map f)
  map_id i := by rw [F.map_id i, Naturality.underivedMap_id]
  map_comp f g := by rw [F.map_comp f g, Naturality.underivedMap_comp]

section FamilyMaps

variable {F} {G H : I ⥤ (C ⥤ D)} [∀ i : I, (G.obj i).Additive]
  [∀ i : I, (H.obj i).Additive]

/-- A natural map of additive-functor families induces the actual derived family map. -/
def derivedMap (τ : F ⟶ G) : derived F ⟶ derived G where
  app i := Naturality.lift (τ.app i)
  naturality {i j} f := by
    exact (Naturality.lift_comp (F.map f) (τ.app j)).symm.trans
      ((congrArg Naturality.lift (τ.naturality f)).trans
        (Naturality.lift_comp (τ.app i) (G.map f)))

/-- The same family map on actual bounded-above complexes before derivation. -/
def underivedMap (τ : F ⟶ G) : underived F ⟶ underived G where
  app i := Naturality.underivedMap (τ.app i)
  naturality {i j} f := by
    exact (Naturality.underivedMap_comp (F.map f) (τ.app j)).symm.trans
      ((congrArg Naturality.underivedMap (τ.naturality f)).trans
        (Naturality.underivedMap_comp (τ.app i) (G.map f)))

/-- Derivation preserves the actual identity transformation of a parameter family. -/
theorem derivedMap_id : derivedMap (𝟙 F) = 𝟙 (derived F) := by
  apply NatTrans.ext
  funext i
  exact Naturality.lift_id (F.obj i)

/-- Derivation preserves actual composition of family transformations. -/
theorem derivedMap_comp (τ : F ⟶ G) (σ : G ⟶ H) :
    derivedMap (τ ≫ σ) = derivedMap τ ≫ derivedMap σ := by
  apply NatTrans.ext
  funext i
  exact Naturality.lift_comp (τ.app i) (σ.app i)

/-- The underived family construction preserves identity transformations. -/
theorem underivedMap_id : underivedMap (𝟙 F) = 𝟙 (underived F) := by
  apply NatTrans.ext
  funext i
  exact Naturality.underivedMap_id (F.obj i)

/-- The underived family construction preserves actual composition of transformations. -/
theorem underivedMap_comp (τ : F ⟶ G) (σ : G ⟶ H) :
    underivedMap (τ ≫ σ) = underivedMap τ ≫ underivedMap σ := by
  apply NatTrans.ext
  funext i
  exact Naturality.underivedMap_comp (τ.app i) (σ.app i)

end FamilyMaps

/-- Evaluate the derived family at an actual canonical Minus object. -/
def atObject (X : DerivedCategory.Minus C) : I ⥤ DerivedCategory.Minus D :=
  derived F ⋙ (evaluation (DerivedCategory.Minus C) (DerivedCategory.Minus D)).obj X

/-- Evaluate the original family on a bounded-above complex followed by native localization. -/
def atComplex (K : BoundedAboveDual.Complex C) : I ⥤ DerivedCategory.Minus D :=
  underived F ⋙ (evaluation (BoundedAboveDual.Complex C) (DerivedCategory.Minus D)).obj K

/-- The native counit is natural in every map of the original parameter category. -/
def counit (K : BoundedAboveDual.Complex C) :
    atObject F ((CanonicalLeft.Q C).obj K) ⟶ atComplex F K where
  app i := (CanonicalLeft.counit (F.obj i)).app K
  naturality {_ _} f := Naturality.counit_square_app (F.map f) K

/-- Native localization maps an actual bounded-above source arrow in every parameter. -/
def sourceMap {K L : BoundedAboveDual.Complex C} (f : K ⟶ L) :
    atObject F ((CanonicalLeft.Q C).obj K) ⟶ atObject F ((CanonicalLeft.Q C).obj L) where
  app i := (CanonicalLeft.leftDerived (F.obj i)).map ((CanonicalLeft.Q C).map f)
  naturality {_ _} g := ((Naturality.lift (F.map g)).naturality ((CanonicalLeft.Q C).map f)).symm

/-- The actual underived source arrow remains natural in the original parameter. -/
def underivedSourceMap {K L : BoundedAboveDual.Complex C} (f : K ⟶ L) :
    atComplex F K ⟶ atComplex F L where
  app i := (CanonicalLeft.underived (F.obj i)).map f
  naturality {_ _} g := ((Naturality.underivedMap (F.map g)).naturality f).symm

/-- Parameter-natural source transport commutes with the same native counit. -/
theorem sourceMap_counit {K L : BoundedAboveDual.Complex C} (f : K ⟶ L) :
    sourceMap F f ≫ counit F L = counit F K ≫ underivedSourceMap F f := by
  apply NatTrans.ext
  funext i
  exact (CanonicalLeft.counit (F.obj i)).naturality f

/-- Source identity retains the actual identity map of each derived parameter functor. -/
theorem sourceMap_id (K : BoundedAboveDual.Complex C) : sourceMap F (𝟙 K) = 𝟙 _ := by
  apply NatTrans.ext
  funext i
  exact (congrArg (CanonicalLeft.leftDerived (F.obj i)).map
    ((CanonicalLeft.Q C).map_id K)).trans
      ((CanonicalLeft.leftDerived (F.obj i)).map_id ((CanonicalLeft.Q C).obj K))

/-- Source composition retains the actual native functor composition in every parameter. -/
theorem sourceMap_comp {K L M : BoundedAboveDual.Complex C} (f : K ⟶ L) (g : L ⟶ M) :
    sourceMap F (f ≫ g) = sourceMap F f ≫ sourceMap F g := by
  apply NatTrans.ext
  funext i
  exact (congrArg (CanonicalLeft.leftDerived (F.obj i)).map
    ((CanonicalLeft.Q C).map_comp f g)).trans
      ((CanonicalLeft.leftDerived (F.obj i)).map_comp
        ((CanonicalLeft.Q C).map f) ((CanonicalLeft.Q C).map g))

/-- Underived source identity is the native functor identity in each parameter. -/
theorem underivedSourceMap_id (K : BoundedAboveDual.Complex C) :
    underivedSourceMap F (𝟙 K) = 𝟙 _ := by
  apply NatTrans.ext
  funext i
  exact (CanonicalLeft.underived (F.obj i)).map_id K

/-- Underived source composition is retained in the parameter-natural original family. -/
theorem underivedSourceMap_comp {K L M : BoundedAboveDual.Complex C}
    (f : K ⟶ L) (g : L ⟶ M) :
    underivedSourceMap F (f ≫ g) = underivedSourceMap F f ≫ underivedSourceMap F g := by
  apply NatTrans.ext
  funext i
  exact (CanonicalLeft.underived (F.obj i)).map_comp f g

/-- The counit square commutes when both the parameter and actual source complex change. -/
theorem counit_parameter_source {i j : I} (g : i ⟶ j)
    {K L : BoundedAboveDual.Complex C} (f : K ⟶ L) :
    (atObject F ((CanonicalLeft.Q C).obj K)).map g ≫
        (sourceMap F f).app j ≫ (counit F L).app j =
      (counit F K).app i ≫ (underivedSourceMap F f).app i ≫ (atComplex F L).map g := by
  have hparam := (counit F K).naturality g
  have hsource := (CanonicalLeft.counit (F.obj j)).naturality f
  have hmap := (underivedSourceMap F f).naturality g
  calc
    _ = (atObject F ((CanonicalLeft.Q C).obj K)).map g ≫
        ((counit F K).app j ≫ (underivedSourceMap F f).app j) :=
      congrArg (fun a => (atObject F ((CanonicalLeft.Q C).obj K)).map g ≫ a) hsource
    _ = ((counit F K).app i ≫ (atComplex F K).map g) ≫
        (underivedSourceMap F f).app j :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun a => a ≫ (underivedSourceMap F f).app j) hparam)
    _ = (counit F K).app i ≫
        ((underivedSourceMap F f).app i ≫ (atComplex F L).map g) :=
      (Category.assoc _ _ _).trans (congrArg (fun a => (counit F K).app i ≫ a) hmap)
    _ = _ := rfl

section CounitFamilyMaps

variable {F} {G : I ⥤ (C ⥤ D)} [∀ i : I, (G.obj i).Additive]

/-- Evaluate a genuine derived-family transformation at an original canonical source. -/
def mapAtObject (τ : F ⟶ G) (X : DerivedCategory.Minus C) : atObject F X ⟶ atObject G X :=
  Functor.whiskerRight (derivedMap τ)
    ((evaluation (DerivedCategory.Minus C) (DerivedCategory.Minus D)).obj X)

/-- Evaluate the original underived-family transformation at the actual bounded-above complex. -/
def mapAtComplex (τ : F ⟶ G) (K : BoundedAboveDual.Complex C) : atComplex F K ⟶ atComplex G K :=
  Functor.whiskerRight (underivedMap τ)
    ((evaluation (BoundedAboveDual.Complex C) (DerivedCategory.Minus D)).obj K)

/-- Maps of additive parameter families commute with the actual canonical counit. -/
theorem mapAtObject_counit (τ : F ⟶ G) (K : BoundedAboveDual.Complex C) :
    mapAtObject τ ((CanonicalLeft.Q C).obj K) ≫ counit G K =
      counit F K ≫ mapAtComplex τ K := by
  apply NatTrans.ext
  funext i
  exact Naturality.counit_square_app (τ.app i) K

end CounitFamilyMaps

variable (K : CochainComplex C ℤ) (d : ℤ) [K.IsStrictlyLE d]

/-- The actual source cochain complex as its native bounded-above object. -/
abbrev sourceComplex : BoundedAboveDual.Complex C :=
  BoundedAboveDual.ofBoundedAbove K d

/-- The canonical localization isomorphism and native counit give the actual computation map. -/
def comparison : atObject F (CanonicalLeft.objectOfBoundedAbove K d) ⟶
    atComplex F (sourceComplex K d) where
  app i := (CanonicalLeft.leftDerived (F.obj i)).map (CanonicalLeft.nativeLocalizationIso K d).inv ≫
    (CanonicalLeft.counit (F.obj i)).app (sourceComplex K d)
  naturality {i j} f := by
    let τ := F.map f
    let T := sourceComplex K d
    let X := CanonicalLeft.objectOfBoundedAbove K d
    let Y := (CanonicalLeft.Q C).obj T
    let e : Y ≅ X := CanonicalLeft.nativeLocalizationIso K d
    let Fi := CanonicalLeft.leftDerived (F.obj i)
    let Fj := CanonicalLeft.leftDerived (F.obj j)
    have h : (Naturality.lift τ).app X ≫ Fj.map e.inv =
        Fi.map e.inv ≫ (Naturality.lift τ).app Y :=
      ((Naturality.lift τ).naturality e.inv).symm
    have hc := Naturality.counit_square_app τ T
    calc
      _ = ((Naturality.lift τ).app X ≫ Fj.map e.inv) ≫
          (CanonicalLeft.counit (F.obj j)).app T := (Category.assoc _ _ _).symm
      _ = (Fi.map e.inv ≫ (Naturality.lift τ).app Y) ≫
          (CanonicalLeft.counit (F.obj j)).app T :=
        congrArg (fun a => a ≫ (CanonicalLeft.counit (F.obj j)).app T) h
      _ = Fi.map e.inv ≫ ((CanonicalLeft.counit (F.obj i)).app T ≫
          (Naturality.underivedMap τ).app T) :=
        (Category.assoc _ _ _).trans (congrArg (fun a => Fi.map e.inv ≫ a) hc)
      _ = _ := (Category.assoc _ _ _).symm

variable [∀ n : ℤ, Projective (K.X n)]

/-- Projectivity of the source complex earns invertibility for every functor in the family. -/
theorem comparison_isIso (i : I) : IsIso ((comparison F K d).app i) := by
  let Fi := F.obj i
  let T := sourceComplex K d
  let _ : IsIso ((BoundedAboveDual.counit Fi).app T) :=
    BoundedAboveDual.counit_isIso_of_projective Fi K d
  let G := (DerivedCategory.minusOppositeEquivalence D).inverse
  let ε := (BoundedAboveDual.counit Fi).app T
  let Y := (BoundedAboveDual.Q C).obj T
  let e := (CanonicalLeft.localizationComputationIso Fi).app Y ≪≫ G.mapIso (asIso ε)
  have hCounit : (CanonicalLeft.counit Fi).app T = e.hom := Naturality.counit_app Fi T
  let _ : IsIso ((CanonicalLeft.counit Fi).app T) :=
    hCounit.symm ▸ (inferInstance : IsIso e.hom)
  change IsIso ((CanonicalLeft.leftDerived Fi).map
    (CanonicalLeft.nativeLocalizationIso K d).inv ≫ (CanonicalLeft.counit Fi).app T)
  infer_instance

/-- The parameter-natural computation on any actual bounded-above projective complex. -/
def computationIso : atObject F (CanonicalLeft.objectOfBoundedAbove K d) ≅
    atComplex F (sourceComplex K d) :=
  NatIso.ofComponents (fun i => by
    let _ := comparison_isIso F K d i
    exact asIso ((comparison F K d).app i))
    (fun {i j} f => (comparison F K d).naturality f)

/-- Every original parameter map commutes with the earned computation isomorphism. -/
theorem computation_naturality {i j : I} (f : i ⟶ j) :
    (atObject F (CanonicalLeft.objectOfBoundedAbove K d)).map f ≫ (computationIso F K d).hom.app j =
      (computationIso F K d).hom.app i ≫ (atComplex F (sourceComplex K d)).map f :=
  (computationIso F K d).hom.naturality f

end DerivedCategory.CanonicalLeft.Family
