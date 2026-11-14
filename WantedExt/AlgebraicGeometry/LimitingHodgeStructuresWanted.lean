/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.LimitingHodgeStructures

/-!
# Unipotent one-variable limiting Hodge realization

The local system, deck logarithm, geometric period filtration, untwisting
and monodromy weight formula are fixed in the completed core.
Source: Schmid, *Variation of Hodge Structure: The Singularities of the
Period Mapping*, Invent. Math. 22 (1973), Theorems 4.9 and 6.16.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LimitingHodgeStructuresWanted

open CategoryTheory
open MathlibExt.Geometry.RationalHodgeStructures
open MathlibExt.Geometry.LimitingHodgeStructures

/-- The normalized untwisted period filtration extends holomorphically to
zero for a polarized variation with unipotent deck operator. -/
public theorem_wanted unipotent_period_extension
    (V : ModuleCat.{0} ℚ) [FiniteDimensional ℚ V]
    (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ) (hb : 0 < b)
    (hT : (H.rationalDeck.toLinearMap - 1) ^ b = 0) :
    Nonempty (PeriodExtension C e H b)

/-- The actual limiting flag and kernel/image monodromy filtration form a
rational MHS; its actual logarithm lowers F by one. -/
public def_wanted limiting_mixed_hodge_realization
    (V : ModuleCat.{0} ℚ) [FiniteDimensional ℚ V]
    (C : RationalComplexification V) (r : ℕ)
    (e : C.complexSpace ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r)) (w : ℤ)
    (H : PolarizedPeriodVariation C e w) (b : ℕ) (hb : 0 < b)
    (hT : (H.rationalDeck.toLinearMap - 1) ^ b = 0)
    (E : PeriodExtension C e H b) : LimitingHodgeData C e H b E

end WantedExt.AlgebraicGeometry.LimitingHodgeStructuresWanted
