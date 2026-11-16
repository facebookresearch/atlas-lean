/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The functorial resolution specification is adapted from
AxiomMath/Stacks at c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/Homology/Injectives/Spaltenstein/FunctorialResolution.lean,
licensed under Apache 2.0. That source has no individual author or
copyright notice. Modification notice: retain the canonical cochain
functor, natural quasi-isomorphism and K-injectivity as explicit input;
no generic resolution-existence request is introduced.
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import MathlibExt.AlgebraicGeometry.NearbyCycleGeometry

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# Actual cochain nearby and vanishing cycles

All operators use rational sheaves on the explicit exponential cover.
Specialization is the ordinary inverse-image/direct-image unit followed
by the natural K-injective resolution map. Vanishing cycles are the
functorial cochain mapping cone of that particular specialization.

Generic functorial K-injective resolutions are explicit canonically
characterized toolbox input. Their unconditional producers in Axiom's
Stacks library are
`StacksFrontier/Homology/Injectives/KInjective/Enlargement.lean`,
`Stacks.Injectives.exists_functorialInjectiveResolution` (Tag 079N), and
`StacksFrontier/Homology/Injectives/KInjective/FunctorialResolution.lean`,
`Stacks.Injectives.exists_functorial_quasiIso_isKInjective` (Tag 079P).
The Spaltenstein specification cited in the attribution is conditional;
these KInjective files discharge its injective-enlargement input.
-/

namespace MathlibExt.AlgebraicGeometry.NearbyCycleComplexes

open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization
open CategoryTheory.Functor
open TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.ComplexAnalytification
open _root_.MathlibExt.AlgebraicGeometry.PerverseSheaves
open _root_.MathlibExt.AlgebraicGeometry.ConstructibleComplexes
open _root_.MathlibExt.AlgebraicGeometry.NearbyCycleGeometry

attribute [local instance] HasDerivedCategory.standard

abbrev QSheaf (Z : TopCat.{0}) := RationalSheaf Z
abbrev QCochain (Z : TopCat.{0}) := CochainComplex (QSheaf Z) ℤ
abbrev QDerived (Z : TopCat.{0}) := RationalDerived Z

/-- The existing functorial K-injective resolution toolbox, on actual
cochain complexes of rational sheaves. -/
structure FunctorialResolution (Z : TopCat.{0}) where
  functor : QCochain Z ⥤ QCochain Z
  inclusion : 𝟭 (QCochain Z) ⟶ functor
  quasiIso : ∀ K, QuasiIso (inclusion.app K)
  isKInjective : ∀ K, (functor.obj K).IsKInjective

/-- Cochain inverse image, from the completed exact sheaf inverse image. -/
abbrev cochainPullback {Z W : TopCat.{0}} (f : Z ⟶ W) :
    QCochain W ⥤ QCochain Z :=
  (pullback ℚ f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Cochain direct image of the actual sheaf functor. -/
abbrev cochainPushforward {Z W : TopCat.{0}} (f : Z ⟶ W) :
    QCochain Z ⥤ QCochain W :=
  (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Actual direct-image composition; its components are identities on
the same presheaf sections. -/
def sheafPushforwardComp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ⋙
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) g ≅
        TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (f ≫ g) :=
  NatIso.ofComponents (fun F ↦ Iso.refl _) (by intro F G a; rfl)

/-- The equality comparison for the fixed direct-image functor. -/
def sheafPushforwardCongr {X Y : TopCat.{0}} {f g : X ⟶ Y} (h : f = g) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ≅
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) g :=
  eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ)) h)

/-- Canonical inverse-image composition, fixed as the adjunction mate
of the identity-on-sections direct-image composition. -/
def sheafPullbackComp {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback ℚ g ⋙ pullback ℚ f ≅ pullback ℚ (f ≫ g) :=
  Adjunction.leftAdjointCompIso
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) (f ≫ g))
    (sheafPushforwardComp f g)

/-- The actual sheaf pushforward equivalence induced by a homeomorphism. -/
def sheafPushforwardEquivalence {X Y : TopCat.{0}} (d : X ≅ Y) :
    QSheaf X ≌ QSheaf Y :=
  CategoryTheory.Equivalence.mk
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) d.hom)
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) d.inv)
    ((sheafPushforwardComp d.hom d.inv ≪≫
    sheafPushforwardCongr d.hom_inv_id ≪≫
      NatIso.ofComponents (fun F ↦ Iso.refl _) (by intro F G a; rfl)).symm)
    (sheafPushforwardComp d.inv d.hom ≪≫
    sheafPushforwardCongr d.inv_hom_id ≪≫
      NatIso.ofComponents (fun F ↦ Iso.refl _) (by intro F G a; rfl))

/-- The inverse-image/direct-image unit of a homeomorphism is an
isomorphism, by the actual direct-image equivalence. -/
instance homeomorphismUnitIso {X Y : TopCat.{0}} (d : X ≅ Y) :
    IsIso (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) d.hom).unit := by
  let e := sheafPushforwardEquivalence d
  have : (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) d.hom).IsEquivalence :=
    e.isEquivalence_functor
  infer_instance

/-- The actual cochain adjunction unit. -/
def cochainUnit {Z W : TopCat.{0}} (f : Z ⟶ W) :
    𝟭 (QCochain W) ⟶ cochainPullback f ⋙ cochainPushforward f where
  app K :=
    { f n := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app (K.X n)
      comm' i j hij := by
        exact ((TopCat.Sheaf.pullbackPushforwardAdjunction
          (ModuleCat.{0} ℚ) f).unit.naturality (K.d i j)).symm }
  naturality K L a := by
    ext n
    exact (TopCat.Sheaf.pullbackPushforwardAdjunction
      (ModuleCat.{0} ℚ) f).unit.naturality (a.f n)

/-- The actual cochain nearby operator i⁻¹ q_* R(q⁻¹ K): pull to the cover,
resolve there, push back, and restrict to the zero fiber. -/
def nearbyCochain {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    QCochain (space X) ⥤ QCochain (space A.Z) :=
  cochainPullback (coverProjection X s) ⋙ R.functor ⋙
    cochainPushforward (coverProjection X s) ⋙ cochainPullback (spaceMap A.i)

set_option backward.isDefEq.respectTransparency false in
/-- The actual specialization map, with its normalization fixed by the
ordinary sheaf adjunction unit and the resolution inclusion. -/
def specializationCochain {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    cochainPullback (spaceMap A.i) ⟶ nearbyCochain A R where
  app K := (cochainPullback (spaceMap A.i)).map
    ((cochainUnit (coverProjection X s)).app K ≫
      (cochainPushforward (coverProjection X s)).map
        (R.inclusion.app ((cochainPullback (coverProjection X s)).obj K)))
  naturality K L a := by
    dsimp [nearbyCochain]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    have e₀ : a ≫ (cochainUnit (coverProjection X s)).app L =
        (cochainUnit (coverProjection X s)).app K ≫
          (cochainPushforward (coverProjection X s)).map
            ((cochainPullback (coverProjection X s)).map a) :=
      (cochainUnit (coverProjection X s)).naturality a
    have e : (cochainPullback (coverProjection X s)).map a ≫
        R.inclusion.app ((cochainPullback (coverProjection X s)).obj L) =
        R.inclusion.app ((cochainPullback (coverProjection X s)).obj K) ≫
          R.functor.map ((cochainPullback (coverProjection X s)).map a) :=
      R.inclusion.naturality ((cochainPullback (coverProjection X s)).map a)
    rw [← Category.assoc, e₀, Category.assoc, ← CategoryTheory.Functor.map_comp,
      e, CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]

/-- The functorial cochain cone of that particular specialization.
This is unshifted Rφ; Rφ[-1] is the perverse normalization. -/
def vanishingCochain {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    QCochain (space X) ⥤ QCochain (space A.Z) where
  obj K := CochainComplex.mappingCone ((specializationCochain A R).app K)
  map a := CochainComplex.mappingCone.map _ _
    ((cochainPullback (spaceMap A.i)).map a) ((nearbyCochain A R).map a)
    ((specializationCochain A R).naturality a).symm
  map_id K := by
    change CochainComplex.mappingCone.map _ _
      ((cochainPullback (spaceMap A.i)).map (𝟙 K)) ((nearbyCochain A R).map (𝟙 K)) _ = _
    simp only [CategoryTheory.Functor.map_id, CochainComplex.mappingCone.map_id]
  map_comp a b := by
    simp only [CategoryTheory.Functor.map_comp]
    apply CochainComplex.mappingCone.map_comp


/-- Functoriality and the two-out-of-three property force the resolution
functor to preserve quasi-isomorphisms. -/
lemma resolutionMapQuasi {Z : TopCat.{0}} (R : FunctorialResolution Z)
    {K L : QCochain Z} (a : K ⟶ L) (ha : QuasiIso a) :
    QuasiIso (R.functor.map a) := by
  let W := HomologicalComplex.quasiIso (QSheaf Z) (ComplexShape.up ℤ)
  have h : W (a ≫ R.inclusion.app L) :=
    W.comp_mem a (R.inclusion.app L) ha (R.quasiIso L)
  have e : a ≫ R.inclusion.app L = R.inclusion.app K ≫ R.functor.map a :=
    R.inclusion.naturality a
  have h' : W (R.inclusion.app K ≫ R.functor.map a) := e ▸ h
  exact (W.precomp_iff (W' := W)
    (R.inclusion.app K) (R.functor.map a) (R.quasiIso K)).mp h'

/-- The cover resolution is K-injective, so the actual direct image
preserves the homotopy equivalences occurring between resolved complexes. -/
lemma nearbyCochainMapQuasi {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    {K L : QCochain (space X)} (a : K ⟶ L) (ha : QuasiIso a) :
    QuasiIso ((nearbyCochain A R).map a) := by
  have : QuasiIso a := ha
  let q := coverProjection X s
  let P := cochainPullback q
  let B := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) q
  have hp : QuasiIso (P.map a) := by dsimp [P]; infer_instance
  have hr : QuasiIso (R.functor.map (P.map a)) := resolutionMapQuasi R _ hp
  have : (R.functor.obj (P.obj K)).IsKInjective := R.isKInjective _
  have : (R.functor.obj (P.obj L)).IsKInjective := R.isKInjective _
  have he := (CochainComplex.IsKInjective.quasiIso_iff
    (R.functor.map (P.map a))).mp hr
  have hb : QuasiIso ((cochainPushforward q).map (R.functor.map (P.map a))) :=
    homotopyEquivalences_le_quasiIso _ _ _
      (B.homotopyEquivalences_mapHomologicalComplex_map _ he)
  have : QuasiIso ((cochainPushforward q).map (R.functor.map (P.map a))) := hb
  change QuasiIso
    ((cochainPullback (spaceMap A.i)).map
      ((cochainPushforward q).map (R.functor.map (P.map a))))
  infer_instance

/-- The actual cochain specialization triangles, including functorial
cone maps. -/
def cochainCycleTriangles {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    QCochain (space X) ⥤ CategoryTheory.Pretriangulated.Triangle (QDerived (space A.Z)) where
  obj K := DerivedCategory.Q.mapTriangle.obj
    (CochainComplex.mappingCone.triangle ((specializationCochain A R).app K))
  map a := DerivedCategory.Q.mapTriangle.map
    (CochainComplex.mappingCone.triangleMap _ _
      ((cochainPullback (spaceMap A.i)).map a) ((nearbyCochain A R).map a)
      ((specializationCochain A R).naturality a).symm)
  map_id K := by
    apply CategoryTheory.Pretriangulated.Triangle.hom_ext
    · change DerivedCategory.Q.map ((cochainPullback (spaceMap A.i)).map (𝟙 K)) = _
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl
    · change DerivedCategory.Q.map ((nearbyCochain A R).map (𝟙 K)) = _
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl
    · change DerivedCategory.Q.map ((vanishingCochain A R).map (𝟙 K)) = _
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      rfl
  map_comp a b := by
    apply CategoryTheory.Pretriangulated.Triangle.hom_ext
    · change DerivedCategory.Q.map ((cochainPullback (spaceMap A.i)).map (a ≫ b)) = _
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      rfl
    · change DerivedCategory.Q.map ((nearbyCochain A R).map (a ≫ b)) = _
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      rfl
    · change DerivedCategory.Q.map ((vanishingCochain A R).map (a ≫ b)) = _
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
      rfl

/-- The derived image of a map of these triangles is an isomorphism when
the input cochain map is a quasi-isomorphism. -/
lemma cochainCycleTrianglesInverts {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    (HomologicalComplex.quasiIso (QSheaf (space X)) (.up ℤ)).IsInvertedBy
      (cochainCycleTriangles A R) := by
  intro K L a ha
  have : QuasiIso a := ha
  have : QuasiIso ((nearbyCochain A R).map a) := nearbyCochainMapQuasi A R a ha
  let b := (cochainCycleTriangles A R).map a
  have h₁ : IsIso b.hom₁ := by
    change IsIso (DerivedCategory.Q.map ((cochainPullback (spaceMap A.i)).map a))
    infer_instance
  have h₂ : IsIso b.hom₂ := by
    change IsIso (DerivedCategory.Q.map ((nearbyCochain A R).map a))
    infer_instance
  have h₃ : IsIso b.hom₃ :=
    CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ b
      (DerivedCategory.mappingCone_triangle_distinguished _)
      (DerivedCategory.mappingCone_triangle_distinguished _) h₁ h₂
  exact CategoryTheory.Pretriangulated.Triangle.isIso_of_isIsos b h₁ h₂ h₃

/-- The global derived cycle triangle functor, obtained by actual
localization of the functorial cochain triangles. -/
def cycleTriangles {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    QDerived (space X) ⥤ CategoryTheory.Pretriangulated.Triangle (QDerived (space A.Z)) :=
  Localization.lift (cochainCycleTriangles A R) (cochainCycleTrianglesInverts A R)
    DerivedCategory.Q

/-- Unshifted Rψ on the actual rational-sheaf derived category. -/
def nearbyFunctor {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    QDerived (space X) ⥤ QDerived (space A.Z) :=
  cycleTriangles A R ⋙ CategoryTheory.Pretriangulated.Triangle.π₂

/-- Unshifted Rφ, the derived functor fixed by the cochain mapping cone.
Its perverse normalization is Rφ[-1]. -/
def vanishingFunctor {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    QDerived (space X) ⥤ QDerived (space A.Z) :=
  cycleTriangles A R ⋙ CategoryTheory.Pretriangulated.Triangle.π₃



/-- The first vertex is the actual exact inverse image, with its
canonical cochain comparison. -/
instance cycleFirstLifting {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (QSheaf (space X)) (.up ℤ))
      (cochainPullback (spaceMap A.i) ⋙ DerivedCategory.Q)
      (cycleTriangles A R ⋙ CategoryTheory.Pretriangulated.Triangle.π₁) where
  iso := (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      (Localization.fac (cochainCycleTriangles A R) (cochainCycleTrianglesInverts A R)
        DerivedCategory.Q) _ ≪≫
          NatIso.ofComponents (fun K ↦ Iso.refl _) (by intro K L a; rfl)

/-- The nearby vertex is pinned to the actual resolved cochain formula. -/
instance nearbyFunctorLifting {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (QSheaf (space X)) (.up ℤ))
      (nearbyCochain A R ⋙ DerivedCategory.Q) (nearbyFunctor A R) where
  iso := (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      (Localization.fac (cochainCycleTriangles A R) (cochainCycleTrianglesInverts A R)
        DerivedCategory.Q) _ ≪≫
          NatIso.ofComponents (fun K ↦ Iso.refl _) (by intro K L a; rfl)

/-- Every value of the global cycle-triangle functor is the derived
image of the actual functorial specialization cone. -/
lemma cycleTriangles_distinguished {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s))
    (K : QDerived (space X)) :
    (cycleTriangles A R).obj K ∈
      CategoryTheory.Pretriangulated.distinguishedTriangles (C := QDerived (space A.Z)) := by
  let L := DerivedCategory.Q.objPreimage K
  let e := (cycleTriangles A R).mapIso (DerivedCategory.Q.objObjPreimageIso K)
  let a := (Localization.fac (cochainCycleTriangles A R)
    (cochainCycleTrianglesInverts A R) DerivedCategory.Q).app L
  exact CategoryTheory.Pretriangulated.isomorphic_distinguished _
    (DerivedCategory.mappingCone_triangle_distinguished _) _ (e.symm ≪≫ a)

/-- Canonical identification of the first vertex with i*. -/
def cycleFirstIso {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    cycleTriangles A R ⋙ CategoryTheory.Pretriangulated.Triangle.π₁ ≅
      derivedPullback ℚ (spaceMap A.i) := by
  letI : Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (QSheaf (space X)) (.up ℤ))
      (cochainPullback (spaceMap A.i) ⋙ DerivedCategory.Q)
      (derivedPullback ℚ (spaceMap A.i)) :=
    ⟨(pullback ℚ (spaceMap A.i)).mapDerivedCategoryFactors⟩
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (QSheaf (space X)) (.up ℤ))
    (cochainPullback (spaceMap A.i) ⋙ DerivedCategory.Q)
    (cochainPullback (spaceMap A.i) ⋙ DerivedCategory.Q)
    _ _ (Iso.refl _)



/-- The vanishing vertex is pinned to its actual functorial cochain cone. -/
instance vanishingFunctorLifting {X : ComplexScheme} {s : Γ(X.left, ⊤)}
    (A : ZeroFiber X s) (R : FunctorialResolution (exponentialCover X s)) :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (QSheaf (space X)) (.up ℤ))
      (vanishingCochain A R ⋙ DerivedCategory.Q) (vanishingFunctor A R) where
  iso := (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      (Localization.fac (cochainCycleTriangles A R) (cochainCycleTrianglesInverts A R)
        DerivedCategory.Q) _ ≪≫
          NatIso.ofComponents (fun K ↦ Iso.refl _) (by intro K L a; rfl)


end MathlibExt.AlgebraicGeometry.NearbyCycleComplexes

