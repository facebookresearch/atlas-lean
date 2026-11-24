/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiMarkedCurveExtensions

/-!
# The actual universal source extension used in Li's delta

The identity tensor of F1 with its native dual fixes the actual marked
curve extension. Pullback along d-dual is compared to the literal trivial
curve family, preserving reduction and all marks. Its class translation
is fixed by the negative identity tensor of F0.
These actual schemes and maps are the source of the local lift differences
in delta0/delta1, not freely chosen homomorphisms of complexes.
Source: Jun Li arXiv:math/0110113v1, equations1.15--1.19, printed pp13--15.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiUniversalSourceExtensions

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MarkedCurveStabilization StackBundleCones LiFiniteComplexPresentations LiMarkedCurveExtensions
open scoped TensorProduct BigOperators

attribute [local instance] LiMarkedCurveExtensions.oppositeModule
  LiMarkedCurveExtensions.centralModule LiMarkedCurveExtensions.oppositeComm LiMarkedCurveExtensions.oppositeTower

variable {A : Type} [CommRing A] (P : Matrix A)

def rightDual : ModuleCat.{0} A := ModuleCat.of A (right P →ₗ[A] A)
def leftDual : ModuleCat.{0} A := ModuleCat.of A (left P →ₗ[A] A)

def dualMap : rightDual P ⟶ leftDual P := ModuleCat.ofHom P.differential.dualMap

def rightIdentity : rightCoefficient P (rightDual P) :=
  ∑ i : Fin P.rightRank, Pi.single i (1 : A) ⊗ₜ[A] (LinearMap.proj i : right P →ₗ[A] A)

def leftIdentity : leftCoefficient P (leftDual P) :=
  ∑ i : Fin P.leftRank, Pi.single i (1 : A) ⊗ₜ[A] (LinearMap.proj i : left P →ₗ[A] A)

variable {n g : ℕ} (F : MarkedFamily (Spec (.of A)) n g)

def trivialBase (I : ModuleCat.{0} A) : Spec (.of (TrivSqZeroExt A I)) ⟶ Spec (.of A) :=
  Spec.algebraMap A (TrivSqZeroExt A I)

structure Trivial (I : ModuleCat.{0} A) where
  family : Family F I
  iso : family.curve.X ≅ pullback F.π (trivialBase I)
  projection : iso.hom ≫ pullback.snd F.π (trivialBase I) = family.curve.π
  reduction_source : family.reduction ≫ iso.hom ≫ pullback.fst F.π (trivialBase I) = 𝟙 F.X
  reduction_base : family.reduction ≫ iso.hom ≫ pullback.snd F.π (trivialBase I) =
    F.π ≫ LiMarkedCurveExtensions.reduction A I
  markings : ∀ i : Fin n, family.curve.marking i ≫ iso.hom ≫ pullback.fst F.π (trivialBase I) =
    trivialBase I ≫ F.marking i

variable (C : Classification F)

structure Data where
  universal : Family F (rightDual C.matrix)
  universalClass : (C.functor (rightDual C.matrix)).obj universal ≅
    (⟨rightIdentity C.matrix⟩ : AdditiveQuotient (tensorDifferential C.matrix (rightDual C.matrix)).hom)
  trivial : Trivial F (leftDual C.matrix)
  trivialClass : (C.functor (leftDual C.matrix)).obj trivial.family ≅
    (⟨0⟩ : AdditiveQuotient (tensorDifferential C.matrix (leftDual C.matrix)).hom)
  trivialization : (C.reindex (dualMap C.matrix)).obj universal ≅ trivial.family
  translation :
    (((quotientReindex C.matrix (dualMap C.matrix)).map universalClass.inv ≫
      (C.naturality (dualMap C.matrix)).inv.app universal ≫
      (C.functor (leftDual C.matrix)).map trivialization.hom ≫ trivialClass.hom).translation) =
        -leftIdentity C.matrix

end MathlibExt.AlgebraicGeometry.LiUniversalSourceExtensions
