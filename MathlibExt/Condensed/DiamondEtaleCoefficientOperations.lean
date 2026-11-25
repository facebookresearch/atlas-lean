/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Actual derived etale coefficient operations for overconvergence

The site is the actual representable-etale slice of the specified
v-sheaf. Base change is native pullback of its actual sheaf arrows.
Direct image is actual sheaf restriction on this base-change functor;
inverse image is its native chosen left adjoint. Their derived functors
are native Kan-derived functors of these fixed cochain sources.

The derived adjunction unit is fixed by its complete cochain comparison
square with the ordinary adjunction unit and both native derived maps.
Overconvergence is tested on that unit for the original geometric
point's inclusion Spa(C,C-circle) -> Spa(C,C-plus). The inclusion has the
actual same-field isomorphism and actual maximal plus ring.

Scope: `Derived` is the ordinary unbounded derived category of sheaves on
the small representable-etale site, a naive small-site analogue of
Scholze's `D_et`. The latter is defined by v-descent, and even for locally
spatial diamonds it compares with the left completion of this category
(Scholze, arXiv:1709.07343v4, Def. 14.13, Rem. 14.14, Prop. 14.15); on
strictly totally disconnected charts the two agree. The overconvergence
condition below is Mann's condition transported to this analogue; its
comparison with `D_et` in general is not asserted here.

Source: Mann, arXiv:2206.02022v1, Definition 3.9.17.
No generic unnamed source or target functor substitutes for these maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.DiamondEtaleCoefficientOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
open MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites
open MathlibExt.AlgebraicGeometry.AnalyticAdicDiamondification
open MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry

variable (p : ℕ) [Fact p.Prime]

attribute [local instance] HasDerivedCategory.standard

/-- Universe-bounded native etale Fp-module sheaves on the actual slice site. -/
abbrev Coefficients (G : VSheaf p) :=
  Sheaf (diamondEtaleTopology p G) (ModuleCat.{2} (ULift.{2} (ZMod p)))

/-- The derived etale coefficient category: the ordinary unbounded derived category of sheaves
on the small representable-etale site, a naive small-site analogue of Scholze's `D_et` (which is
defined by v-descent and compares with the left completion of this category in general). -/
abbrev Derived (G : VSheaf p) := DerivedCategory (Coefficients p G)

/-- Stability refers to the actual native sheaf pullback. -/
def Stable {F G : VSheaf p} (f : F ⟶ G) : Prop :=
  ∀ T : DiamondEtaleSite p G,
    IsRepresentableEtale p ((Over.pullback f).obj T.obj).hom

/-- The real etale base-change functor on every pullback object and arrow. -/
def baseChange {F G : VSheaf p} (f : F ⟶ G) (h : Stable p f) :
    DiamondEtaleSite p G ⥤ DiamondEtaleSite p F where
  obj T := ⟨(Over.pullback f).obj T.obj, h T⟩
  map a := ObjectProperty.homMk ((Over.pullback f).map a.hom)

section Operations

variable {F G : VSheaf p} (f : F ⟶ G) (h : Stable p f)
  [(baseChange p f h).IsContinuous (diamondEtaleTopology p G) (diamondEtaleTopology p F)]

/-- Actual etale direct image is restriction along native base change. -/
def directImage : Coefficients p F ⥤ Coefficients p G :=
  (baseChange p f h).sheafPushforwardContinuous
    (ModuleCat.{2} (ULift.{2} (ZMod p)))
    (diamondEtaleTopology p G) (diamondEtaleTopology p F)

instance directImage_additive : (directImage p f h).Additive where
  map_add := rfl

variable [(directImage p f h).IsRightAdjoint]

/-- Native inverse image of these actual etale Fp sheaves. -/
def inverseImage : Coefficients p G ⥤ Coefficients p F :=
  (directImage p f h).leftAdjoint

/-- The ordinary source adjunction is the native restriction adjunction. -/
def ordinaryAdjunction : inverseImage p f h ⊣ directImage p f h :=
  Adjunction.ofIsRightAdjoint (directImage p f h)

instance inverseImage_additive : (inverseImage p f h).Additive :=
  (ordinaryAdjunction p f h).left_adjoint_additive

/-- The ordinary cochain unit includes the native identity and composition comparisons. -/
def cochainUnit (K : CochainComplex (Coefficients p G) ℤ) :
    K ⟶ ((inverseImage p f h).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (directImage p f h).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  (Functor.mapHomologicalComplexIdIso (Coefficients p G) (ComplexShape.up ℤ)).inv.app K ≫
    ((ordinaryAdjunction p f h).unit.mapHomologicalComplex (ComplexShape.up ℤ)).app K ≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (inverseImage p f h ⋙ directImage p f h)) (ComplexShape.up ℤ)).inv.app K

attribute [local instance] HasDerivedCategory.standard

/-- The fixed ordinary inverse-image cochain source. -/
def inverseSource := (inverseImage p f h).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
  (DerivedCategory.Q : CochainComplex (Coefficients p F) ℤ ⥤ Derived p F)

/-- The fixed ordinary direct-image cochain source. -/
def directSource := (directImage p f h).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
  (DerivedCategory.Q : CochainComplex (Coefficients p G) ℤ ⥤ Derived p G)

/-- Derived existence is requested for these actual sources. -/
class DerivedExistence : Prop where
  left : (inverseSource p f h).HasLeftDerivedFunctor
    (HomologicalComplex.quasiIso (Coefficients p G) (ComplexShape.up ℤ))
  right : (directSource p f h).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (Coefficients p F) (ComplexShape.up ℤ))

attribute [instance] DerivedExistence.left DerivedExistence.right

variable [DerivedExistence p f h]

/-- Native Kan-derived etale inverse image. -/
def derivedInverse : Derived p G ⥤ Derived p F :=
  (inverseSource p f h).totalLeftDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (Coefficients p G) (ComplexShape.up ℤ))

/-- Native Kan-derived etale direct image. -/
def derivedDirect : Derived p F ⥤ Derived p G :=
  (directSource p f h).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (Coefficients p F) (ComplexShape.up ℤ))

/-- The exact native left-derived source counit. -/
def leftComparison : DerivedCategory.Q ⋙ derivedInverse p f h ⟶ inverseSource p f h :=
  (inverseSource p f h).totalLeftDerivedCounit DerivedCategory.Q
    (HomologicalComplex.quasiIso (Coefficients p G) (ComplexShape.up ℤ))

/-- The exact native right-derived source unit. -/
def rightComparison : directSource p f h ⟶ DerivedCategory.Q ⋙ derivedDirect p f h :=
  (directSource p f h).totalRightDerivedUnit DerivedCategory.Q
    (HomologicalComplex.quasiIso (Coefficients p F) (ComplexShape.up ℤ))

end Operations

attribute [local instance] HasDerivedCategory.standard

/-- Derived adjunction is fixed on its entire original cochain unit square. -/
structure OperationModel {F G : VSheaf p} (f : F ⟶ G) where
  stable : Stable p f
  [continuous : (baseChange p f stable).IsContinuous
    (diamondEtaleTopology p G) (diamondEtaleTopology p F)]
  [adjoint : (directImage p f stable).IsRightAdjoint]
  [derived : DerivedExistence p f stable]
  adjunction : derivedInverse p f stable ⊣ derivedDirect p f stable
  unit_source : ∀ K : CochainComplex (Coefficients p G) ℤ,
    adjunction.unit.app (DerivedCategory.Q.obj K) ≫
      (derivedDirect p f stable).map ((leftComparison p f stable).app K) =
    DerivedCategory.Q.map (cochainUnit p f stable K) ≫
      (rightComparison p f stable).app
        ((inverseImage p f stable).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj K)

/-- A geometric inclusion `Spa(C, 𝒪_C) → Spa(C, C⁺)` of one complete algebraically closed field
`C` with two plus rings (Mann, Def. 3.9.17): the bundled Huber ring of `original` is itself a field
(with its own ring operations), algebraically closed for that field structure, whose plus ring `C⁺`
is a valuation subring; the map is the identity of the topological field `C` (its ring map is a
homeomorphism), and the plus ring of `maximal` is the full ring of power-bounded elements `𝒪_C`. -/
structure IntegralGeometricInclusion where
  maximal : AffineUntilting p
  original : AffineUntilting p
  /-- The original Huber ring is a field. -/
  isField : IsField original.pair.ring
  /-- It is algebraically closed, for the field structure of its own ring operations. -/
  closed : letI := isField.toField; IsAlgClosed original.pair.ring
  /-- The original plus ring is a valuation subring: every element or its inverse lies in it. -/
  plus_valuation : ∀ a : original.pair.ring,
    a ∈ original.pair.plus ∨ ∃ b ∈ original.pair.plus, a * b = 1
  map : maximal ⟶ original
  /-- The map identifies the two topological fields: its ring map is a homeomorphism. -/
  same_field : IsHomeomorph map.original.hom
  maximal_plus : maximal.pair.plus = maximal.pair.powerbounded

/-- Overconvergence is the actual derived j-adjunction unit after actual i-inverse image. -/
def IsOverconvergent (R : AffineRealization p) (G : VSheaf p) (K : Derived p G) : Prop :=
  ∀ (T : IntegralGeometricInclusion p)
    (i : (diamondFunctor p R).obj ((realizationFunctor p R).obj T.original) ⟶ G)
    (I : OperationModel p i)
    (J : OperationModel p ((diamondFunctor p R).map ((realizationFunctor p R).map T.map))),
      letI := I.continuous
      letI := I.adjoint
      letI := I.derived
      IsIso (J.adjunction.unit.app ((derivedInverse p i I.stable).obj K))

end MathlibExt.Condensed.DiamondEtaleCoefficientOperations
