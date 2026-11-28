/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LimitingMultiplierFamilies
public import Batteries.Util.ProofWanted

/-!
# Directed maxima of actual limiting multiplier ideals

Candidate sheaves are fixed by the actual resolved fractional pullbacks
and their affine pushforward images. These requests concern that family;
none assumes an arbitrary maximal ideal or a Q-Gorenstein condition.
Source: de Fernex--Hacon, arXiv:0805.1767v2, Definition 4.3 and Section 4.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LimitingMultiplierFamiliesWanted

open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.NaturalPullbackMultiplierModules
open MathlibExt.AlgebraicGeometry.LimitingMultiplierFamilies

theorem_wanted limitingMultiplierDirected (k : Type) [Field k] [CharZero k] (n : ℕ)
    (V : NormalVariety k n) (C : CanonicalData V)
    [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
    (I : V.X.left.IdealSheafData) (c : ℝ) (_nonnegative : 0 ≤ c)
    (F : LimitingFamily V C I c) (a b : PNat) :
    ∃ m : PNat, (F.image a).ideal ≤ (F.image m).ideal ∧ (F.image b).ideal ≤ (F.image m).ideal

theorem_wanted limitingMultiplierMaximal (k : Type) [Field k] [CharZero k] (n : ℕ)
    (V : NormalVariety k n) (C : CanonicalData V)
    [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
    (I : V.X.left.IdealSheafData) (c : ℝ) (_nonnegative : 0 ≤ c)
    (F : LimitingFamily V C I c) : ∃ m : PNat, limitingIdeal F = (F.image m).ideal

theorem_wanted limitingMultiplierIndependent (k : Type) [Field k] [CharZero k] (n : ℕ)
    (V : NormalVariety k n) (C : CanonicalData V)
    [∀ p : PrimePoint V, IsDiscreteValuationRing (LocalRing V p.val)]
    (I : V.X.left.IdealSheafData) (c : ℝ) (_nonnegative : 0 ≤ c)
    (F G : LimitingFamily V C I c) : limitingIdeal F = limitingIdeal G

end WantedExt.AlgebraicGeometry.LimitingMultiplierFamiliesWanted
