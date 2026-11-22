/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FunctionSpectrum.Delooping
import MathlibExt.CategoryTheory.Functor.Iteration
import MathlibExt.Topology.Category.PointedCGWH.SuspensionLoop
import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.Evaluation

/-!
# Iterated function spectra of the free one-sphere

For every n and m, identifies degree m of the n-fold iterated free-one-sphere function functor
with n-fold loops of degree m + n. These are level comparisons with explicit forward and inverse
naturality in spectrum maps.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed

namespace NativeOmegaRecovery.NativeSymmetricR
private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}
private abbrev J := PointedCGWH.SymmetricOperatorIndex.{u, v}
private abbrev Carrier := EnrichedFunctorCat V.{u, v} J.{u, v}
attribute [local instance] Operad.SmallFinBijGroupoid.instMonoidalCategory
  Operad.SmallFinBijGroupoid.instSymmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

/-- The actual native first free-function index. -/
abbrev firstIndex : I := Operad.SmallFinBijGroupoid.card 1

/-- The actual function spectrum out of the original first free one-sphere. -/
def functor : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  (NativeOmegaPreparation.NativeSymmetricFunction.bifunctor.{u, v}).obj
    (.op (Free.object (PointedCGWH.symmetricOperatorObj.{u, v} firstIndex)
      PointedCGWH.sphereOne.{u, v}))

/-- Both original free maps give the whole native right-shift/cotensor comparison. -/
def comparison : functor.{u, v} ≅
    PointedCGWH.SymmetricShift.functor.{u, v} firstIndex ⋙
      cotensor PointedCGWH.sphereOne.{u, v} :=
  NativeSymmetricFreeFunction.nativeFreeComparison firstIndex PointedCGWH.sphereOne

/-- The original free one-sphere function spectrum is the native loop of its
original first-free-zero-sphere function delooping. -/
def deloopingLoopComparison : functor.{u, v} ≅
    NativeSymmetricDelooping.firstDeloopingLoop.{u, v} :=
  comparison ≪≫ (Functor.isoWhiskerRight
    (NativeSymmetricDelooping.deloopingComparison firstIndex)
    (cotensor PointedCGWH.sphereOne.{u, v})).symm

/-- Evaluation keeps the genuine original finite-bijection operator object. -/
def level (m : ℕ) : Carrier.{u, v} ⥤ V.{u, v} :=
  evaluation (PointedCGWH.symmetricOperatorObj.{u, v} (Operad.SmallFinBijGroupoid.card m))

private def shiftedLoopLevelIso (m : ℕ) :
    (PointedCGWH.SymmetricShift.functor.{u, v} firstIndex ⋙
      cotensor PointedCGWH.sphereOne.{u, v}) ⋙ level m ≅
        level (m + 1) ⋙ ihom PointedCGWH.sphereOne.{u, v} :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    change component
        (cotensorMap PointedCGWH.sphereOne
          ((PointedCGWH.SymmetricShift.functor firstIndex).map f))
          (PointedCGWH.symmetricOperatorObj (Operad.SmallFinBijGroupoid.card m)) ≫ 𝟙 _ =
      𝟙 _ ≫ (ihom PointedCGWH.sphereOne).map
        (component f (PointedCGWH.symmetricOperatorObj
          (Operad.SmallFinBijGroupoid.card (m + 1))))
    rw [Category.comp_id, Category.id_comp, cotensorMap_component,
      PointedCGWH.SymmetricShift.functor_map_component]
    rfl)

/-- Every original first-free function value has the actual successor-level loop. -/
def levelComparison (m : ℕ) : functor.{u, v} ⋙ level m ≅
    level (m + 1) ⋙ ihom PointedCGWH.sphereOne.{u, v} :=
  Functor.isoWhiskerRight comparison (level m) ≪≫ shiftedLoopLevelIso m

/-- Iterate the same actual original native function functor, retaining its actions. -/
def iterate (n : ℕ) : Carrier.{u, v} ⥤ Carrier.{u, v} :=
  Functor.Iteration.iterate functor n

/-- Every evaluated native R iterate is naturally the original ordered loop power.
No identification of the whole spectrum actions is made. -/
def iterationLevelComparison : ∀ n m : ℕ,
    iterate.{u, v} n ⋙ level m ≅
      level (m + n) ⋙ PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower.{u, v} n
  | 0, m => (level m).leftUnitor ≪≫ (level m).rightUnitor.symm
  | n + 1, m =>
    Functor.associator (iterate n) functor (level m) ≪≫
      Functor.isoWhiskerLeft (iterate n) (levelComparison m) ≪≫
      (Functor.associator (iterate n) (level (m + 1))
        (ihom PointedCGWH.sphereOne)).symm ≪≫
      Functor.isoWhiskerRight (iterationLevelComparison n (m + 1))
        (ihom PointedCGWH.sphereOne) ≪≫
      Functor.associator (level (m + 1 + n))
        (PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n)
        (ihom PointedCGWH.sphereOne) ≪≫
      Functor.isoWhiskerRight
        (eqToIso (congrArg (fun k : ℕ => level.{u, v} k)
          (show m + 1 + n = m + (n + 1) by omega)))
        (PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n ⋙ ihom PointedCGWH.sphereOne)

/-- Both directions of the evaluated component retain the original level values. -/
def iterationLevelIso (n m : ℕ) (X : Carrier.{u, v}) :
    ((iterate n).obj X).toEnrichedFunctor.obj
        (PointedCGWH.symmetricOperatorObj.{u, v} (Operad.SmallFinBijGroupoid.card m)) ≅
      (PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).obj
        (X.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v}
          (Operad.SmallFinBijGroupoid.card (m + n)))) :=
  (iterationLevelComparison n m).app X

/-- Every whole input arrow is natural for the actual evaluated R comparison. -/
theorem iterationLevelComparison_naturality (n m : ℕ) {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (level m).map ((iterate n).map f) ≫ (iterationLevelComparison n m).hom.app Y =
      (iterationLevelComparison n m).hom.app X ≫
        (PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).map
          ((level (m + n)).map f) :=
  (iterationLevelComparison n m).hom.naturality f

/-- The inverse comparison is natural on the same entire input arrow. -/
theorem iterationLevelComparison_inv_naturality (n m : ℕ) {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    (PointedCGWH.SequentialSpectrum.OrderedLoop.loopPower n).map
        ((level (m + n)).map f) ≫ (iterationLevelComparison n m).inv.app Y =
      (iterationLevelComparison n m).inv.app X ≫ (level m).map ((iterate n).map f) :=
  (iterationLevelComparison n m).inv.naturality f

end NativeOmegaRecovery.NativeSymmetricR
