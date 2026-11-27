/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralArcCoverModels
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# General finite-ring étale coefficient complexes on qcqs schemes

Coefficients are left modules over any ring, including noncommutative
rings. Schemes are arbitrary qcqs schemes, including non-Noetherian and
empty schemes. The small étale site and every base-change test scheme are
native. Inverse image is the native left adjoint to that same base-change
pushforward; the derived functor is its literal quasi-isomorphism lift.

Constructibility uses finite quasi-compact locally closed strata and
actual finite constant modules after étale inverse image. No finite
Tor-dimension is imposed. Full K-injective/DG enhancement and coherent
arc descent are separate source constructions and theorem requests.

Source: Bhatt--Mathew arXiv:1807.04725v4, Notation 5.8, Remark 5.9,
Propositions 5.10--5.12 and Theorem 5.13, pp. 41--43. The native étale
and localization operations retain their Mathlib source attribution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralEtaleCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open GeneralArcCoverModels
open CochainComplex.HomComplex
open scoped ZeroObject

variable (Λ : Type) [Ring Λ]
  [∀ X : Scheme.{0}, HasSheafify X.smallEtaleTopology (ModuleCat.{1} Λ)]

/-- Actual left-Λ module sheaves on the full native small étale site. -/
abbrev CoefficientSheaves (X : Scheme.{0}) :=
  Sheaf X.smallEtaleTopology (ModuleCat.{1} Λ)

/-- Actual unbounded cochain complexes of these same étale module sheaves. -/
abbrev CoefficientComplexes (X : Scheme.{0}) :=
  CochainComplex (CoefficientSheaves Λ X) ℤ

/-- The native constant module sheaf, without commutativity of Λ. -/
def constantModule (X : Scheme.{0}) (M : ModuleCat.{1} Λ) : CoefficientSheaves Λ X :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{1} Λ)).obj M

/-- Ordinary inverse-image source data contains only native site/adjoint
properties. No constructible or arc descent conclusion is a field. -/
structure EtalePullbackSource {X Y : Scheme.{0}} (f : X ⟶ Y) where
  [continuous : (MorphismProperty.Over.pullback (@Etale) ⊤ f).IsContinuous
    Y.smallEtaleTopology X.smallEtaleTopology]
  [rightAdjoint : ((MorphismProperty.Over.pullback (@Etale) ⊤ f).sheafPushforwardContinuous
    (ModuleCat.{1} Λ) Y.smallEtaleTopology X.smallEtaleTopology).IsRightAdjoint]
  [additive : ((MorphismProperty.Over.pullback (@Etale) ⊤ f).sheafPullback
    (ModuleCat.{1} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
  [leftExact : PreservesFiniteLimits ((MorphismProperty.Over.pullback (@Etale) ⊤ f).sheafPullback
    (ModuleCat.{1} Λ) Y.smallEtaleTopology X.smallEtaleTopology)]

/-- Native base-change pushforward of module sheaves. -/
def pushforward {X Y : Scheme.{0}} {f : X ⟶ Y} (S : EtalePullbackSource Λ f) :
    CoefficientSheaves Λ X ⥤ CoefficientSheaves Λ Y :=
  letI := S.continuous
  (MorphismProperty.Over.pullback (@Etale) ⊤ f).sheafPushforwardContinuous
    (ModuleCat.{1} Λ) Y.smallEtaleTopology X.smallEtaleTopology

/-- The actual ordinary étale inverse image, with all left-Λ actions retained. -/
def pullback {X Y : Scheme.{0}} {f : X ⟶ Y} (S : EtalePullbackSource Λ f) :
    CoefficientSheaves Λ Y ⥤ CoefficientSheaves Λ X :=
  letI := S.continuous
  letI := S.rightAdjoint
  (MorphismProperty.Over.pullback (@Etale) ⊤ f).sheafPullback
    (ModuleCat.{1} Λ) Y.smallEtaleTopology X.smallEtaleTopology

instance pullbackAdditive {X Y : Scheme.{0}} {f : X ⟶ Y}
    (S : EtalePullbackSource Λ f) : (pullback Λ S).Additive := S.additive

/-- Native termwise inverse image of the actual coefficient complexes. -/
def complexPullback {X Y : Scheme.{0}} {f : X ⟶ Y} (S : EtalePullbackSource Λ f) :
    CoefficientComplexes Λ Y ⥤ CoefficientComplexes Λ X :=
  (pullback Λ S).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Exactness is tested on the actual termwise pullback quasi-isomorphisms. -/
def IsExactPullback {X Y : Scheme.{0}} {f : X ⟶ Y} (S : EtalePullbackSource Λ f) : Prop :=
  ∀ (A B : CoefficientComplexes Λ Y) (a : A ⟶ B),
    QuasiIso a → QuasiIso ((complexPullback Λ S).map a)

attribute [local instance] HasDerivedCategory.standard

/-- Actual native quasi-isomorphism localization of these module complexes. -/
abbrev CoefficientDerived (X : Scheme.{0}) := DerivedCategory (CoefficientSheaves Λ X)

/-- The exact source functor really inverts the specified quasi-isomorphisms. -/
theorem pullback_inverts {X Y : Scheme.{0}} {f : X ⟶ Y} (S : EtalePullbackSource Λ f)
    (hS : IsExactPullback Λ S) :
    (HomologicalComplex.quasiIso (CoefficientSheaves Λ Y) (ComplexShape.up ℤ)).IsInvertedBy
      (complexPullback Λ S ⋙ DerivedCategory.Q) := by
  intro A B a ha
  exact Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso (CoefficientSheaves Λ X) (ComplexShape.up ℤ))
    ((complexPullback Λ S).map a) (hS A B a ha)

/-- Canonical derived inverse image, from the actual localization universal property. -/
def derivedPullback {X Y : Scheme.{0}} {f : X ⟶ Y} (S : EtalePullbackSource Λ f)
    (hS : IsExactPullback Λ S) : CoefficientDerived Λ Y ⥤ CoefficientDerived Λ X :=
  Localization.lift (complexPullback Λ S ⋙ DerivedCategory.Q)
    (pullback_inverts Λ S hS) DerivedCategory.Q

/-- The fixed Q/pullback comparison, rather than a supplied cohomology equivalence. -/
def derivedPullbackComparison {X Y : Scheme.{0}} {f : X ⟶ Y}
    (S : EtalePullbackSource Λ f) (hS : IsExactPullback Λ S) :
    DerivedCategory.Q ⋙ derivedPullback Λ S hS ≅ complexPullback Λ S ⋙ DerivedCategory.Q :=
  Localization.fac _ (pullback_inverts Λ S hS) DerivedCategory.Q

/-- A genuine finite locally closed qcqs partition, without a field or
finite-type condition on the original scheme or its strata. -/
structure Stratification (X : QcqsScheme) where
  count : ℕ
  stratum : Fin count → QcqsScheme
  inclusion : ∀ i, (stratum i).scheme ⟶ X.scheme
  immersion : ∀ i, IsImmersion (inclusion i)
  quasiCompact : ∀ i, QuasiCompact (inclusion i)
  disjoint : Pairwise fun i j => Disjoint (Set.range (inclusion i)) (Set.range (inclusion j))
  cover : (⋃ i, Set.range (inclusion i)) = Set.univ

variable (S : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y), EtalePullbackSource Λ f)

/-- Finite local constancy on an actual étale cover by actual finite left modules. -/
def IsFiniteLocallyConstant (X : Scheme.{0}) (F : CoefficientSheaves Λ X) : Prop :=
  ∃ U : X.Cover.{1} etalePrecoverage, ∀ i : U.I₀,
    ∃ M : ModuleCat.{1} Λ, Finite M ∧
      Nonempty ((pullback Λ (S (U.f i))).obj F ≅ constantModule Λ (U.X i) M)

/-- Actual cohomological amplitude of a coefficient complex. -/
def InAmplitude {X : Scheme.{0}} (K : CoefficientComplexes Λ X) (a b : ℤ) : Prop :=
  ∀ n : ℤ, n < a ∨ b < n → IsZero (K.homology n)

/-- Source bounded constructibility, with one finite partition for the
finitely many possible nonzero cohomology degrees. No finite Tor clause is added. -/
def IsBoundedConstructible (X : QcqsScheme) (K : CoefficientComplexes Λ X.scheme) : Prop :=
  (∃ a b : ℤ, InAmplitude Λ K a b) ∧
  ∃ P : Stratification X, ∀ (i : Fin P.count) (n : ℤ),
    IsFiniteLocallyConstant Λ S (P.stratum i).scheme
      ((pullback Λ (S (P.inclusion i))).obj (K.homology n))

/-- K-injectivity uses all genuine shifted homogeneous module cochains. -/
def IsKInjective {X : Scheme.{0}} (K : CoefficientComplexes Λ X) : Prop :=
  ∀ A : CoefficientComplexes Λ X, (∀ n : ℤ, IsZero (A.homology n)) →
    ∀ (n : ℤ) (a : Cochain A K n), δ n (n + 1) a = 0 →
      ∃ b : Cochain A K (n - 1), δ (n - 1) n b = a

end MathlibExt.AlgebraicGeometry.GeneralEtaleCoefficientModels
