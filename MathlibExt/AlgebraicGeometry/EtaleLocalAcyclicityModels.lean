/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteEtaleConstructibleModels
public import MathlibExt.AlgebraicGeometry.EtaleStrictLocalizationModels
public import MathlibExt.AlgebraicGeometry.CotangentTransversalTests
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Actual Milnor specialization and cotangent microsupport tests

The specialization goes from the actual geometric stalk to derived
sections of the actual Milnor fibre. It first inverts the native
strict-local closed-stalk restriction and then uses the native derived
inverse-image/direct-image unit to restrict to the Milnor fibre. A
vanishing model is the cochain cone of that particular arrow.

Local acyclicity tests invertibility of these arrows at every geometric
point and generization. Microsupport quantifies over the actual smooth
cotangent-transversal test pairs. The finite-coefficient toolbox contains
ordinary constructibility and closed-stalk adapters, with no local
acyclicity or singular-support conclusion as an input.

Sources: Beilinson, arXiv:1505.06768v8, Sections 1.1--1.3; Saito,
arXiv:1510.03018v4, Section 1.1, printed pages 4--5; SGA 4, local acyclicity.
The finite discrete pro-étale realization uses the same native scheme
maps and the ordinary finite étale/pro-étale coefficient comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EtaleLocalAcyclicityModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open AdicDerivedContracts FiniteEtaleConstructibleModels
open CotangentBundleTestModels CotangentTransversalTests EtaleStrictLocalizationModels

export FiniteEtaleConstructibleModels (geometricStalk)

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ] [DerivedFunctorTheory Λ]

/-- The generic geometric strict-localization construction, independently
of all coefficients, local acyclicity and cotangent cones. -/
structure StrictLocalizationSystem where
  model : ∀ (X : Scheme.{0}) (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ X),
    StrictLocalization Ω x
  localMap : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (Ω : GeometricField)
    (x : Spec (.of Ω.carrier) ⟶ X) (LX : StrictLocalization Ω x)
    (LY : StrictLocalization Ω (x ≫ f)), LocalMorphism Ω x f LX LY

/-- Derived restriction is fixed by the actual adjunction and global-section units. -/
def globalRestriction {Z W : Scheme.{0}} (f : Z ⟶ W) (K : Derived Λ W) :
    (derivedSections Λ W).obj K ⟶
      (derivedSections Λ Z).obj ((derivedPullback Λ f).obj K) :=
  (derivedSections Λ W).map
      ((DerivedAdjunction.adjunction (R := Λ) (f := f)).unit.app K) ≫
    (GlobalSectionsPushforward.comparison (R := Λ) (f := f)).hom.app
      ((derivedPullback Λ f).obj K)

variable {X : Scheme.{0}} (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ X)
  (L : StrictLocalization Ω x) (K : Derived Λ X)

/-- The native comparison around the strict-local closed point. -/
def pointPullbackIso : derivedPullback Λ L.map ⋙ derivedPullback Λ L.point ≅
    derivedPullback Λ x :=
  (DerivedPullbackPasting.comparison (R := Λ) (f := L.point) (g := L.map)) ≪≫
    eqToIso (congrArg (derivedPullback Λ) L.point_map)

/-- The closed-stalk arrow is the actual derived restriction, followed by
the normalized native pullback composition comparison. -/
def closedStalkArrow :
    (derivedSections Λ L.scheme).obj ((derivedPullback Λ L.map).obj K) ⟶
      geometricStalk Λ Ω x K :=
  globalRestriction Λ L.point ((derivedPullback Λ L.map).obj K) ≫
    (derivedSections Λ (Spec (.of Ω.carrier))).map ((pointPullbackIso Λ Ω x L).hom.app K)

/-- Ordinary strict-local stalk integration on one actual constructible
complex. It is independent of any map f or acyclicity test. -/
structure ClosedStalkSystem {X : Scheme.{0}} (K : Derived Λ X) : Prop where
  isIso : ∀ (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ X)
    (L : StrictLocalization Ω x), IsIso (closedStalkArrow Λ Ω x L K)

variable {Y : Scheme.{0}} (f : X ⟶ Y)
  (LX : StrictLocalization Ω x) (LY : StrictLocalization Ω (x ≫ f))
  (M : LocalMorphism Ω x f LX LY) (t : Generization Ω x f LY)

/-- Derived sections of the literal scheme Milnor fibre, with the same pulled coefficient. -/
def milnorSections : DerivedCategory.Plus (ModuleCat.{1} Λ) :=
  (derivedSections Λ (milnorFibre Ω x f LX LY M t)).obj
    ((derivedPullback Λ (milnorProjection Ω x f LX LY M t)).obj
      ((derivedPullback Λ LX.map).obj K))

/-- The source specialization is fixed by two actual derived restriction maps. -/
def specialization [IsIso (closedStalkArrow Λ Ω x LX K)] :
    geometricStalk Λ Ω x K ⟶ milnorSections Λ Ω x K f LX LY M t :=
  inv (closedStalkArrow Λ Ω x LX K) ≫
    globalRestriction Λ (milnorProjection Ω x f LX LY M t)
      ((derivedPullback Λ LX.map).obj K)

/-- A cochain enhancement of that exact specialization arrow. -/
structure VanishingModel [IsIso (closedStalkArrow Λ Ω x LX K)] where
  source : CochainComplex (ModuleCat.{1} Λ) ℤ
  target : CochainComplex (ModuleCat.{1} Λ) ℤ
  sourceIso : DerivedCategory.Q.obj source ≅ (geometricStalk Λ Ω x K).obj
  targetIso : DerivedCategory.Q.obj target ≅ (milnorSections Λ Ω x K f LX LY M t).obj
  arrow : source ⟶ target
  normalized : DerivedCategory.Q.map arrow ≫ targetIso.hom =
    sourceIso.hom ≫ (specialization Λ Ω x K f LX LY M t).hom

def VanishingModel.object [IsIso (closedStalkArrow Λ Ω x LX K)]
    (V : VanishingModel Λ Ω x K f LX LY M t) : DerivedCategory (ModuleCat.{1} Λ) :=
  DerivedCategory.Q.obj (CochainComplex.mappingCone V.arrow)

variable {Ω x K}

/-- Local acyclicity quantifies over every geometric point and every actual algebraic
generization in its strict local base (its field algebraic over the residue field of its
image, as in Saito §1.2). -/
def IsLocalAcyclic (G : StrictLocalizationSystem) {X Y : Scheme.{0}}
    (f : X ⟶ Y) (K : Derived Λ X) (S : ClosedStalkSystem Λ K) : Prop :=
  ∀ (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ X)
    (t : Generization Ω x f (G.model Y Ω (x ≫ f))),
    t.IsAlgebraic →
    let LX := G.model X Ω x
    let LY := G.model Y Ω (x ≫ f)
    letI := S.isIso Ω x LX
    IsIso (specialization Λ Ω x K f LX LY (G.localMap f Ω x LX LY) t)

variable (k : Type) [Field k]

/-- Stability and closed-stalk properties of bounded constructible complexes
(`IsBoundedConstructible`) of pro-étale sheaves of $\Lambda$-modules on $k$-schemes that are locally
of finite type and quasi-compact over $k$, for the given derived functor data
`DerivedFunctorTheory Λ`: derived pullback along every $k$-morphism between such schemes preserves
bounded constructibility; and for every such complex $K$ on such a scheme $X$, every geometric point
$x$ of $X$ and every strict localization $X_{(x)}$ of $X$ at $x$, the restriction map from the
derived sections of $K$ over $X_{(x)}$ to the geometric stalk of $K$ at $x$ is an isomorphism
(`ClosedStalkSystem`). -/
structure ConstructibleTheory where
  pullback : ∀ (X U : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (h : U ⟶ X) (K : Derived Λ X.left), IsBoundedConstructible Λ k X K →
      IsBoundedConstructible Λ k U ((derivedPullback Λ h.left).obj K)
  closed : ∀ (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (K : Derived Λ X.left), IsBoundedConstructible Λ k X K → ClosedStalkSystem Λ K

variable (G : StrictLocalizationSystem) (T : ConstructibleTheory Λ k)
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  {BX : CotangentBundle X} (C : ClosedCone X BX)
  (K : Derived Λ X.left) (constructible : IsBoundedConstructible Λ k X K)

/-- Beilinson's microsupport predicate on the actual cotangent-transversal
test pairs and the actual pulled coefficient complex. -/
def MicroSupported : Prop :=
  ∀ P : TestPair (X := X), P.IsTransversal C →
    IsLocalAcyclic Λ G P.f.left ((derivedPullback Λ P.h.left).obj K)
      (T.closed P.U _ (T.pullback X P.U P.h K constructible))

/-- Singular support is the smallest actual closed conical microsupport. -/
def IsSingularSupport : Prop :=
  MicroSupported Λ k G T X C K constructible ∧
    ∀ D : ClosedCone X BX, MicroSupported Λ k G T X D K constructible →
      C.support ⊆ D.support

end MathlibExt.AlgebraicGeometry.EtaleLocalAcyclicityModels
