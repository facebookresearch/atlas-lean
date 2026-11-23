/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.LocalCoefficient.WeakEquivalence
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift

/-! Direct positive contracts for the exact original twisted weak-chain map. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial

universe u

#check SSet.realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap
#print axioms SSet.realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap
#check ActualOriginalMapCalibration.originalAllCoefficientPullback_quasiIso_of_regular
#print axioms ActualOriginalMapCalibration.originalAllCoefficientPullback_quasiIso_of_regular

namespace LocalCoefficientWeakEquivalenceTests

example {X Y : SSet.{u}} (f : X ⟶ Y) (hf : SSet.realizationWeakEquivalences f)
    (y : Y _⦋0⦌)
    (hconn : ∀ z : SSet.FundamentalGroupoid Y,
      Nonempty (SSet.FundamentalGroupoid.mk y ⟶ z))
    (L : SSet.LocalSystem ℤ Y) :
    QuasiIso (SSet.localCoefficientPullbackChainMap f L) :=
  SSet.realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap f hf y hconn L

example {X Y : SSet.{u}} (f : X ⟶ Y) (hf : SSet.realizationWeakEquivalences f)
    (y : Y _⦋0⦌)
    (hconn : ∀ z : SSet.FundamentalGroupoid Y,
      Nonempty (SSet.FundamentalGroupoid.mk y ⟶ z)) (n : ℕ)
    (L : SSet.LocalSystem ℤ Y) :
    IsIso (HomologicalComplex.homologyMap (SSet.localCoefficientPullbackChainMap f L) n) := by
  let : QuasiIso (SSet.localCoefficientPullbackChainMap f L) :=
    SSet.realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap f hf y hconn L
  exact (_root_.quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

-- Literal nonflat integer-mod-two stalks are covered by the same public theorem.
example {X Y : SSet.{u}} (f : X ⟶ Y) (hf : SSet.realizationWeakEquivalences f)
    (y : Y _⦋0⦌)
    (hconn : ∀ z : SSet.FundamentalGroupoid Y,
      Nonempty (SSet.FundamentalGroupoid.mk y ⟶ z)) :
    QuasiIso (SSet.localCoefficientPullbackChainMap f
      ((Functor.const (SSet.FundamentalGroupoid Y)).obj
        (ModuleCat.of ℤ (ULift.{u} (ZMod 2))))) :=
  SSet.realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap f hf y hconn _

example {X Y : SSet.{u}} (f : X ⟶ Y) (y : Y _⦋0⦌)
    (hconn : ∀ z : SSet.FundamentalGroupoid Y,
      Nonempty (SSet.FundamentalGroupoid.mk y ⟶ z))
    (hreg : QuasiIso (SSet.localCoefficientPullbackChainMap f
      (CategoryTheory.regularPathModuleCoefficientFunctor (SSet.FundamentalGroupoid.mk y))))
    (L : SSet.LocalSystem ℤ Y) :
    QuasiIso (SSet.localCoefficientPullbackChainMap f L) :=
  ActualOriginalMapCalibration.originalAllCoefficientPullback_quasiIso_of_regular
    f y hconn hreg L

example {X Y : SSet.{1}} (f : X ⟶ Y) (hf : SSet.realizationWeakEquivalences f)
    (y : Y _⦋0⦌)
    (hconn : ∀ z : SSet.FundamentalGroupoid Y,
      Nonempty (SSet.FundamentalGroupoid.mk y ⟶ z))
    (L : SSet.LocalSystem ℤ Y) :
    QuasiIso (SSet.localCoefficientPullbackChainMap f L) :=
  SSet.realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap f hf y hconn L

example {X Y : SSet.{2}} (f : X ⟶ Y) (hf : SSet.realizationWeakEquivalences f)
    (y : Y _⦋0⦌)
    (hconn : ∀ z : SSet.FundamentalGroupoid Y,
      Nonempty (SSet.FundamentalGroupoid.mk y ⟶ z))
    (L : SSet.LocalSystem ℤ Y) :
    QuasiIso (SSet.localCoefficientPullbackChainMap f L) :=
  SSet.realizationWeakEquivalences.quasiIso_localCoefficientPullbackChainMap f hf y hconn L

end LocalCoefficientWeakEquivalenceTests

end
