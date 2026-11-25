/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricPerfKFrontDoors
public import MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Actual finite-projective ring K0 and its native enhanced Perf comparison

The ring group is defined independently: integral generators are actual
finite projective R-modules, modulo native module isomorphisms and
binary direct-sum decompositions. Multiplication uses the actual native
R-module tensor product, with its unit the original regular module.

The Perf object is fixed by a genuine native DG-module augmentation to
the original degree-zero ordinary module. This fixes its K0 class without
using K to choose a module. Quotient descent and comparison bijectivity
remain separate source proofs. All commutative rings, including zero
rings, are permitted.

Sources: Bass, Algebraic K-theory, ChapterII; Thomason--Trobaugh;
BGT1001.2282v4 Sections4/7. Native module, tensor, Hom and DG source
operations retain their exact pins and licenses in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeRingK0Models

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open OrdinarySchemeModuleFamilies OrdinaryConstantCoefficientModels GeometricPerfKFrontDoors
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.StableInfinityGrothendieckGroups
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.DGSource
open scoped Simplicial TensorProduct

attribute [local instance 2000] ModuleCat.instLinear

variable (A : OrdinaryAlgebras)

/-- The original finite projective module carrier. -/
structure FiniteProjective where
  module : ModuleCat.{0} A
  [finite : Module.Finite A module]
  [projective : Module.Projective A module]

attribute [instance] FiniteProjective.finite FiniteProjective.projective

abbrev RingCycles := FreeAbelianGroup (FiniteProjective A)

/-- The independently defined ordinary module isomorphism/direct-sum relations. -/
def RingRelation (r : RingCycles A) : Prop :=
  (∃ P Q : FiniteProjective A, Nonempty (P.module ≅ Q.module) ∧
    r = FreeAbelianGroup.of P - FreeAbelianGroup.of Q) ∨
  ∃ P Q T : FiniteProjective A, Nonempty (P.module ≅ Q.module ⊞ T.module) ∧
    r = FreeAbelianGroup.of P - FreeAbelianGroup.of Q - FreeAbelianGroup.of T

def ringRelations : AddSubgroup (RingCycles A) := AddSubgroup.closure {r | RingRelation A r}

/-- The actual ordinary ring K0 quotient, before any enhanced/spectral comparison. -/
abbrev RingK0 := RingCycles A ⧸ ringRelations A

def moduleClass (P : FiniteProjective A) : RingK0 A := QuotientAddGroup.mk (FreeAbelianGroup.of P)

def regularModule : FiniteProjective A where
  module := ModuleCat.of A A
  finite := inferInstance
  projective := inferInstance

/-- The tensor source retains the actual native ordinary R-module tensor. -/
structure ProjectiveTensorSource where
  tensor : FiniteProjective A → FiniteProjective A → FiniteProjective A
  normalized : ∀ P Q : FiniteProjective A,
    (tensor P Q).module ≅ ModuleCat.of A (P.module ⊗[A] Q.module)

/-- Ring operations are normalized to the existing quotient addition and actual module tensor generators. -/
structure RingK0Structure (T : ProjectiveTensorSource A) where
  ring : CommRing (RingK0 A)
  additive_normalization : ring.toAddCommGroup = (inferInstance : AddCommGroup (RingK0 A))
  one_normalization : letI := ring; (1 : RingK0 A) = moduleClass A (regularModule A)
  multiplication : letI := ring
    ∀ P Q : FiniteProjective A, moduleClass A P * moduleClass A Q = moduleClass A (T.tensor P Q)

variable (N : ShuffleAlgebraFunctor ℤ) (C : ConstantRingSource A N)
  (J : OrdinaryModuleSource A N C) (I : RingPerfectInput A N)

/-- The selected native perfect object augments to the original ordinary projective module, with all DG action retained. -/
structure ProjectivePerfSource where
  object : FiniteProjective A → I.model.category
  augmentation : ∀ P : FiniteProjective A,
    (I.model.realization.obj (object P)).obj ⟶ J.functor.obj (discreteModule A P.module)
  quasi : ∀ P : FiniteProjective A,
    QuasiIso (moduleComponent (augmentation P) (op PUnit.unit))

variable (P : ProjectivePerfSource A N C J I)

/-- This is the actual native coherent-nerve vertex of that same perfect source object. -/
def projectivePerfVertex (M : FiniteProjective A) : I.input.category.toStableInfinityCategory.toSSet _⦋0⦌ :=
  (eqToHom I.input.normalized.symm).app (op ⦋0⦌) (objectVertex (P.object M))

def ringCycleToPerf : RingCycles A →+ GrothendieckGroup I.input.category.toStableInfinityCategory :=
  FreeAbelianGroup.lift (fun M => objectClass I.input.category.toStableInfinityCategory
    (projectivePerfVertex A N C J I P M))

def RingRelationDescent : Prop := ringRelations A ≤ (ringCycleToPerf A N C J I P).ker

/-- The canonical ring-to-Perf K0 group map is descent of the explicitly fixed native module classes. -/
def ringK0ToPerf (h : RingRelationDescent A N C J I P) :
    RingK0 A →+ GrothendieckGroup I.input.category.toStableInfinityCategory :=
  QuotientAddGroup.lift (ringRelations A) (ringCycleToPerf A N C J I P) h

end MathlibExt.AlgebraicGeometry.NativeRingK0Models
