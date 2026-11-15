/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicDerivedContracts
public import MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules
public import MathlibExt.AlgebraicGeometry.GeometricAdicGaloisOperators
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.Topology.KrullDimension

/-!
# Actual rational-adic constructible and perverse dependency contracts

Constructibility uses a finite algebraic stratification and local
triviality on actual pro-etale covers by actual continuous Q_ell^r
coefficients. The cohomology sheaves, pullbacks, stalk restrictions and
point-supported derived objects belong to the fixed small-site category.

`PerverseTheory` is a named input, characterized by the support/cosupport
conditions in every degree. Its category and t-structure are not opaque.
Providing it, and the constructible-preservation comparisons needed by
consumers, is separate from these completed definitions.

`CoefficientPresentation` explicitly links this ambient presentation to
the actual continuous ring `E_X` and its native module derived category.
It records exact forgetful normalization and equivalence only on the
specified constructible scope. The costalk comparison is bijectivity of
precomposition by the actual point coefficient map. These adapters are
pending dependencies, not claims that section 6.8 proves that comparison
or identifies the entire ambient category.

References: BBD, *Faisceaux pervers*, section 2.2; Bhatt--Scholze,
*The pro-etale topology for schemes*, sections 6.5--6.8.
https://www.numdam.org/item/AST_1982__100__1_0/
https://arxiv.org/abs/1309.1198
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.AdicConstructibleContracts

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open _root_.TopologicalSpace
open ContinuousAdicCoefficients AdicDerivedContracts

attribute [local instance] HasDerivedCategory.standard

variable (ell : ℕ) [Fact ell.Prime]

/-- The actual finite-dimensional topological coefficient module. -/
abbrev FiniteCoefficients (r : ℕ) := ULift.{1} (Fin r → ℚ_[ell])

instance finiteCoefficients_continuous (r : ℕ) :
    ContinuousConstSMul ℚ_[ell] (FiniteCoefficients ell r) where
  continuous_const_smul a :=
    continuous_uliftUp.comp ((continuous_const_smul
      (T := Fin r → ℚ_[ell]) a).comp continuous_uliftDown)

/-- Finite-rank lisse means actual pro-etale local triviality, with the
actual topology on the coefficient vector space. -/
def IsFiniteRankLisse (Y : Scheme) (F : ModuleSheaf ℚ_[ell] Y) : Prop :=
  ∃ 𝒰 : Y.Cover.{1} proetalePrecoverage, ∀ i : 𝒰.I₀, ∃ r : ℕ,
    Nonempty (((ProEtaleCohomologyFunctoriality.pullback ℚ_[ell] (𝒰.f
      i)).obj F) ≅
      continuousModuleSheaf ℚ_[ell] (FiniteCoefficients ell r) (𝒰.X i))

variable (k : Type) [Field k]

/-- A finite partition by actual smooth locally closed schemes over k. -/
structure Stratification (X : Over (Spec (.of k))) where
  count : ℕ
  stratum : Fin count → Over (Spec (.of k))
  inclusion : ∀ i, stratum i ⟶ X
  immersion : ∀ i, IsImmersion (inclusion i).left
  smooth : ∀ i, Smooth (stratum i).hom
  quasiCompact : ∀ i, QuasiCompact (stratum i).hom
  separated : ∀ i, IsSeparated (stratum i).hom
  disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (inclusion i).left) (Set.range (inclusion j).left)
  cover : (⋃ i, Set.range (inclusion i).left) = Set.univ

/-- Bounded actual cohomology with one finite algebraic lisse stratification. -/
def boundedConstructible (X : Over (Spec (.of k))) :
    ObjectProperty (Derived ℚ_[ell] X.left) := fun K ↦
  (∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j →
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf ℚ_[ell]
      X.left) j).obj K)) ∧
  ∃ S : Stratification k X, ∀ i j,
    IsFiniteRankLisse ell (S.stratum i).left
      ((ProEtaleCohomologyFunctoriality.pullback ℚ_[ell]
        (S.inclusion i).left).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf ℚ_[ell]
            X.left) j).obj K))

/-- The actual k-rational point object. Over algebraically closed k,
these detect the constructible support on finite-type schemes. -/
abbrev pointObject : Over (Spec (.of k)) := Over.mk (𝟙 _)

/-- Stalk-support detection by the actual inverse-image derived functor. -/
def stalkSupport (X : Over (Spec (.of k))) (K : Derived ℚ_[ell] X.left)
    (j : ℤ) : Set X.left :=
  {y | ∃ x : pointObject k ⟶ X, y ∈ Set.range x.left ∧
    ¬ IsZero ((DerivedCategory.Plus.homologyFunctor
      (ModuleSheaf ℚ_[ell] (Spec (.of k))) j).obj
        ((derivedPullback ℚ_[ell] x.left).obj K))}

/-- The actual point-supported discrete coefficient object. Its derived
Hom computes costalk cohomology, with the unshifted point object. -/
def pointSupported (X : Over (Spec (.of k))) (x : pointObject k ⟶ X) :
    Derived ℚ_[ell] X.left :=
  (derivedPushforward ℚ_[ell] x.left).obj
    (single ℚ_[ell] (ProEtaleCohomologyFunctoriality.constantUnit ℚ_[ell]
      (Spec (.of k))))

/-- The same actual point direct image with the continuous coefficient unit. -/
def continuousPointSupported (X : Over (Spec (.of k)))
    (x : pointObject k ⟶ X) : Derived ℚ_[ell] X.left :=
  (derivedPushforward ℚ_[ell] x.left).obj
    (single ℚ_[ell] (continuousModuleSheaf ℚ_[ell] (ULift.{1} ℚ_[ell])
      (Spec (.of k))))

/-- The fixed point coefficient map, from constant continuous functions
through the actual direct-image functor. -/
def pointCoefficientMap (X : Over (Spec (.of k))) (x : pointObject k ⟶ X) :
    pointSupported ell k X x ⟶ continuousPointSupported ell k X x :=
  (derivedPushforward ℚ_[ell] x.left).map
    (singleMap ℚ_[ell] (ContinuousAdicRingModules.unitCoefficientMap
      ℚ_[ell] (Spec (.of k))))

/-- Costalk Hom comparison by the actual coefficient-map precomposition. -/
def pointHomComparison (X : Over (Spec (.of k)))
    (K : Derived ℚ_[ell] X.left) (x : pointObject k ⟶ X) (j : ℤ) :
    (continuousPointSupported ell k X x ⟶ K⟦j⟧) →
      (pointSupported ell k X x ⟶ K⟦j⟧) :=
  fun f ↦ pointCoefficientMap ell k X x ≫ f

/-- Costalk support is read from actual derived maps out of the point object. -/
def costalkSupport (X : Over (Spec (.of k))) (K : Derived ℚ_[ell] X.left)
    (j : ℤ) : Set X.left :=
  {y | ∃ x : pointObject k ⟶ X, y ∈ Set.range x.left ∧
    ¬ Subsingleton (pointSupported ell k X x ⟶ K⟦j⟧)}

/-- A negative support bound means the support is empty. -/
def SupportDimensionLE (X : Scheme) (s : Set X) (d : ℤ) : Prop :=
  if d < 0 then s = ∅ else
    topologicalKrullDim (closure s) ≤ ((d.toNat : ℕ∞) : WithBot ℕ∞)

/-- Constructible scope inside the native continuous-ring derived category,
using the fixed underlying functor and the same actual lisse strata. -/
def coefficientConstructible (X : Over (Spec (.of k)))
    [EnoughInjectives (ContinuousAdicRingModules.CoefficientModules
      ℚ_[ell] X.left)] :
    ObjectProperty (ContinuousAdicRingModules.CoefficientDerived ℚ_[ell]
      X.left) := fun K ↦
  boundedConstructible ell k X
    ((ContinuousAdicRingModules.derivedUnderlying ℚ_[ell] X.left).obj K)

/-- The specified constructible forgetful comparison, with no chosen functor. -/
def constructibleComparison (X : Over (Spec (.of k)))
    [EnoughInjectives (ContinuousAdicRingModules.CoefficientModules
      ℚ_[ell] X.left)] :
    (coefficientConstructible ell k X).FullSubcategory ⥤
      (boundedConstructible ell k X).FullSubcategory where
  obj K := ⟨(ContinuousAdicRingModules.derivedUnderlying ℚ_[ell]
    X.left).obj K.obj, K.property⟩
  map f := ObjectProperty.homMk
    ((ContinuousAdicRingModules.derivedUnderlying ℚ_[ell] X.left).map f.hom)
  map_id K := by
    apply ObjectProperty.hom_ext
    exact (ContinuousAdicRingModules.derivedUnderlying ℚ_[ell]
      X.left).map_id K.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (ContinuousAdicRingModules.derivedUnderlying ℚ_[ell]
      X.left).map_comp f.hom g.hom

/-- Explicit pending coefficient-presentation adapters. The derived functor,
units, object scope and costalk map are all already fixed constructions.
No whole-ambient equivalence or freely chosen Hom equivalence is assumed. -/
class CoefficientPresentation (ell : ℕ) [Fact ell.Prime] (k : Type)
    [Field k] (X : Over (Spec (.of k))) where
  [enoughInjectives : EnoughInjectives
    (ContinuousAdicRingModules.CoefficientModules ℚ_[ell] X.left)]
  forgetUnitIsIso : ∀ K, IsIso
    ((ContinuousAdicRingModules.underlying ℚ_[ell]
      X.left).rightDerivedFunctorPlusUnit.app K)
  [comparisonIsEquivalence :
    (constructibleComparison ell k X).IsEquivalence]
  pointConstructible : ∀ x, boundedConstructible ell k X
    (continuousPointSupported ell k X x)
  costalkCompatibility : ∀ K, boundedConstructible ell k X K → ∀ x j,
    Function.Bijective (pointHomComparison ell k X K x j)

attribute [instance] CoefficientPresentation.enoughInjectives
  CoefficientPresentation.comparisonIsEquivalence

/-- The actual middle perverse t-structure on the specified constructible
category, characterized by its support and cosupport conditions. -/
class PerverseTheory (ell : ℕ) [Fact ell.Prime] (k : Type)
    [Field k] [IsAlgClosed k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [CoefficientPresentation ell k X] where
  ell_invertible : (ell : k) ≠ 0
  [isTriangulated : (boundedConstructible ell k X).IsTriangulated]
  t : CategoryTheory.Triangulated.TStructure
    (boundedConstructible ell k X).FullSubcategory
  le_iff : ∀ K n, t.le n K ↔ ∀ j,
    SupportDimensionLE X.left (stalkSupport ell k X K.obj j) (n - j)
  ge_iff : ∀ K n, t.ge n K ↔ ∀ j,
    SupportDimensionLE X.left (costalkSupport ell k X K.obj j) (j - n)

attribute [instance] PerverseTheory.isTriangulated

/-- The actual heart of that characterized structure. -/
abbrev PerverseHeart (ell : ℕ) [Fact ell.Prime] (k : Type)
    [Field k] [IsAlgClosed k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [CoefficientPresentation ell k X]
    [PerverseTheory ell k X] :=
  (PerverseTheory.t (ell := ell) (k := k) (X := X)).heart.FullSubcategory

/-- The actual heart inclusion into the fixed rational-adic derived category. -/
def heartInclusion (ell : ℕ) [Fact ell.Prime] (k : Type)
    [Field k] [IsAlgClosed k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [CoefficientPresentation ell k X]
    [PerverseTheory ell k X] :
    PerverseHeart ell k X ⥤ Derived ℚ_[ell] X.left :=
  (PerverseTheory.t (ell := ell) (k := k) (X := X)).heart.ι ⋙
    (boundedConstructible ell k X).ι

instance heartInclusion_full (ell : ℕ) [Fact ell.Prime] (k : Type)
    [Field k] [IsAlgClosed k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [CoefficientPresentation ell k X]
    [PerverseTheory ell k X] : (heartInclusion ell k X).Full := by
  dsimp [heartInclusion]
  infer_instance

instance heartInclusion_faithful (ell : ℕ) [Fact ell.Prime] (k : Type)
    [Field k] [IsAlgClosed k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [CoefficientPresentation ell k X]
    [PerverseTheory ell k X] : (heartInclusion ell k X).Faithful := by
  dsimp [heartInclusion]
  infer_instance

end MathlibExt.AlgebraicGeometry.AdicConstructibleContracts
