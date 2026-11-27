/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AdicDerivedContracts
public import MathlibExt.AlgebraicGeometry.CotangentBundleTestModels
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Flat.Basic

/-!
# Finite discrete constructible coefficients and actual geometric stalks

The coefficient is an actual module, with a distinct discrete carrier;
this changes no topology on any other module. Lisse means local triviality
on actual pro-étale covers by that finite discrete module. Constructibility
uses finite locally closed algebraic strata. No smoothness of a stratum
over an imperfect base field is assumed.

Geometric stalks use the native inverse image and derived global sections.
Finite Tor amplitude means an actual bounded flat complex representing
each such stalk, with one uniform bound. It contains no vanishing-cycle or
characteristic-cycle conclusion.

Sources: Beilinson, arXiv:1505.06768v8, Section 1.1; Saito,
arXiv:1510.03018v4, Section 1.1; Bhatt--Scholze, arXiv:1309.1198,
the finite discrete étale/pro-étale coefficient comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteEtaleConstructibleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.TopologicalSpace _root_.AlgebraicGeometry.Scheme
open ContinuousAdicCoefficients ProEtaleCohomologyFunctoriality AdicDerivedContracts
open CotangentBundleTestModels

attribute [local instance] HasDerivedCategory.standard

variable (Λ : Type) [CommRing Λ]

/-- The same actual coefficient module in a distinct discrete carrier. -/
structure DiscreteCoefficient (M : ModuleCat.{0} Λ) where
  value : ULift.{1} M

def coefficientEquiv (M : ModuleCat.{0} Λ) : DiscreteCoefficient Λ M ≃ ULift.{1} M where
  toFun := DiscreteCoefficient.value
  invFun := DiscreteCoefficient.mk
  left_inv := by rintro ⟨x⟩; rfl
  right_inv := by intro x; rfl

instance (M : ModuleCat.{0} Λ) : AddCommGroup (DiscreteCoefficient Λ M) :=
  (coefficientEquiv Λ M).addCommGroup

def coefficientAddEquiv (M : ModuleCat.{0} Λ) :
    DiscreteCoefficient Λ M ≃+ ULift.{1} M :=
  { coefficientEquiv Λ M with map_add' := by intro x y; rfl }

instance (M : ModuleCat.{0} Λ) : Module Λ (DiscreteCoefficient Λ M) :=
  (coefficientAddEquiv Λ M).module Λ

instance (M : ModuleCat.{0} Λ) : TopologicalSpace (DiscreteCoefficient Λ M) := ⊥

instance (M : ModuleCat.{0} Λ) : DiscreteTopology (DiscreteCoefficient Λ M) := ⟨rfl⟩

instance (M : ModuleCat.{0} Λ) : IsTopologicalAddGroup (DiscreteCoefficient Λ M) :=
  inferInstance

instance (M : ModuleCat.{0} Λ) : ContinuousConstSMul Λ (DiscreteCoefficient Λ M) where
  continuous_const_smul _ := continuous_of_discreteTopology

def discreteSheaf (M : ModuleCat.{0} Λ) (X : Scheme.{0}) : ModuleSheaf Λ X :=
  continuousModuleSheaf Λ (DiscreteCoefficient Λ M) X

/-- Finite local systems, with the actual discrete finite module and cover. -/
def IsFiniteLisse (X : Scheme.{0}) (F : ModuleSheaf Λ X) : Prop :=
  ∃ 𝒰 : X.Cover.{1} proetalePrecoverage, ∀ i : 𝒰.I₀,
    ∃ M : ModuleCat.{0} Λ, Finite M ∧
      Nonempty (((ProEtaleCohomologyFunctoriality.pullback Λ (𝒰.f i)).obj F) ≅
        discreteSheaf Λ M (𝒰.X i))

variable (k : Type) [Field k]

/-- A finite locally closed partition of actual finite-type k-schemes. -/
structure Stratification (X : Over (Spec (.of k))) where
  count : ℕ
  stratum : Fin count → Over (Spec (.of k))
  inclusion : ∀ i, stratum i ⟶ X
  immersion : ∀ i, IsImmersion (inclusion i).left
  finiteType : ∀ i, LocallyOfFiniteType (stratum i).hom
  quasiCompact : ∀ i, QuasiCompact (stratum i).hom
  disjoint : Pairwise fun i j ↦
    Disjoint (Set.range (inclusion i).left) (Set.range (inclusion j).left)
  cover : (⋃ i, Set.range (inclusion i).left) = Set.univ

/-- Bounded actual cohomology locally constant on one finite algebraic partition. -/
def IsBoundedConstructible (X : Over (Spec (.of k))) (K : Derived Λ X.left) : Prop :=
  (∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j →
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf Λ X.left) j).obj K)) ∧
  ∃ S : Stratification k X, ∀ i j,
    IsFiniteLisse Λ (S.stratum i).left
      ((ProEtaleCohomologyFunctoriality.pullback Λ (S.inclusion i).left).obj
        ((DerivedCategory.Plus.homologyFunctor (ModuleSheaf Λ X.left) j).obj K))

variable {k} {X : Over (Spec (.of k))}

/-- Actual stalk sections at a geometric point of a scheme, with no independently given
representation space. -/
def geometricStalk {Y : Scheme.{0}} (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ Y)
    (K : Derived Λ Y) : DerivedCategory.Plus (ModuleCat.{1} Λ) :=
  (derivedSections Λ (Spec (.of Ω.carrier))).obj ((derivedPullback Λ x).obj K)

/-- Finite Tor amplitude on the actual stalks, uniformly over geometric points. -/
def HasFiniteTorAmplitude (K : Derived Λ X.left) : Prop :=
  ∃ a b : ℤ, ∀ (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ X.left),
    ∃ C : CochainComplex (ModuleCat.{1} Λ) ℤ,
      (∀ j : ℤ, j < a ∨ b < j → IsZero (C.X j)) ∧
      (∀ j : ℤ, Module.Flat Λ (C.X j)) ∧
      Nonempty (DerivedCategory.Q.obj C ≅ (geometricStalk Λ Ω x K).obj)

end MathlibExt.AlgebraicGeometry.FiniteEtaleConstructibleModels
