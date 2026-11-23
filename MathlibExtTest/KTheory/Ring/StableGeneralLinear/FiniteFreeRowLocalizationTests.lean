/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowLocalization

noncomputable section

open CategoryTheory Limits
open CategoryTheory.SInverseS AlgebraicKTheory.StableGL

universe u v

variable (R : Type u) [Ring R]

example (A : AddCommGrpCat.{u}) (q : ℕ)
    (z : localizedCoreTranslationHomology (FGProjectiveCat.IdempotentModel R) A q) :
    ∃ (n : ℕ) (x : coreTranslationHomologyModule (FGProjectiveCat.IdempotentModel R) A q),
      z = LocalizedModule.mk x ((finiteFreeRowRegularDenominator R) ^ n) :=
  finiteFreeRowLocalization_exists_regular_fraction R z

example {V : Type v} [AddCommMonoid V]
    [Module (coreTranslationRing (FGProjectiveCat.IdempotentModel R)) V]
    (x y : V) (n m : ℕ) :
    LocalizedModule.mk x ((finiteFreeRowRegularDenominator R) ^ n) =
        LocalizedModule.mk y ((finiteFreeRowRegularDenominator R) ^ m) ↔
      ∃ t : ℕ, n ≤ t ∧ m ≤ t ∧
        ((finiteFreeRowRegularDenominator R) ^ (t - n)) • x =
          ((finiteFreeRowRegularDenominator R) ^ (t - m)) • y :=
  finiteFreeRowLocalization_mk_eq_iff_common_stage R x y n m

example {V : Type v} [AddCommMonoid V]
    [Module (coreTranslationRing (FGProjectiveCat.IdempotentModel R)) V]
    (x y : V) :
    LocalizedModule.mk x (1 : coreTranslationDenominators (FGProjectiveCat.IdempotentModel R)) =
        LocalizedModule.mk y (1 : coreTranslationDenominators (FGProjectiveCat.IdempotentModel R)) ↔
      ∃ k : ℕ,
        ((finiteFreeRowRegularDenominator R) ^ k) • x =
          ((finiteFreeRowRegularDenominator R) ^ k) • y := by
  simpa only [pow_zero, Nat.add_zero] using
    finiteFreeRowLocalization_mk_eq_iff_eventual R x y 0 0

#check AlgebraicKTheory.StableGL.finiteFreeRowDenominator_exists_complement
#check AlgebraicKTheory.StableGL.finiteFreeRowLocalization_exists_regular_fraction
#check AlgebraicKTheory.StableGL.finiteFreeRowLocalization_mk_eq_iff_eventual
#check AlgebraicKTheory.StableGL.finiteFreeRowLocalization_mk_eq_iff_common_stage
