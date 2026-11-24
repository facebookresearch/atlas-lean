/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Weight
public import MathlibExt.Analysis.VonNeumannAlgebra.Ultraweak
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Directed

/-!
# Faithful, normal and semifinite weights on the original concrete algebra

A global scalar weight is an additive, positively homogeneous map from
the original positive cone to extended nonnegative real numbers.
The existing `ScalarWeight.Weight` supplies exactly those values and laws.

Normality below preserves actual least upper bounds of every nonempty,
norm-bounded directed positive set. This expresses the source relation
without choosing a supremum from a theorem. Semifiniteness is totality of
the literal finite-positive set for the proved concrete ultraweak topology:
its complex linear span is ultraweak dense. Faithfulness is the zero-value
condition on every original positive element.

No finite-square domain replaces the finite-positive set. The carrier
contains no modular action, chosen supremum, predual or representation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped NNReal ENNReal

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-- A faithful weight vanishes only at zero in the original positive cone. -/
def IsFaithfulWeight (M : VonNeumannAlgebra H) (φ : CStarAlgebra.ScalarWeight.Weight M) : Prop :=
  ∀ a : CStarAlgebra.ScalarWeight.PositiveElement M, φ.value a = 0 → (a : M) = 0

/-- Normality preserves the actual LUB of every bounded directed positive family.
Directed subsets cover ranges of families indexed in any universe. -/
def IsNormalWeight (M : VonNeumannAlgebra H) (φ : CStarAlgebra.ScalarWeight.Weight M) : Prop :=
  ∀ S : Set (CStarAlgebra.ScalarWeight.PositiveElement M), S.Nonempty →
    DirectedOn (fun a b : CStarAlgebra.ScalarWeight.PositiveElement M => (a : M) ≤ (b : M)) S →
    (∃ C : ℝ, ∀ a ∈ S, ‖(a : M)‖ ≤ C) →
    ∀ s : CStarAlgebra.ScalarWeight.PositiveElement M,
      IsLUB ((fun a : CStarAlgebra.ScalarWeight.PositiveElement M => (a : M)) '' S) (s : M) →
      IsLUB (φ.value '' S) (φ.value s)

/-- Semifiniteness is ultraweak totality of the literal finite-positive set.
The span and the identity into the ultraweak view are the existing actual objects. -/
def IsSemifiniteWeight (M : VonNeumannAlgebra H) (φ : CStarAlgebra.ScalarWeight.Weight M) : Prop :=
  Dense ((φ.finiteIntegrationDomain.map (ultraweakLinearEquiv M).symm.toLinearMap :
    Submodule ℂ (Ultraweak M)) : Set (Ultraweak M))

/-- Faithful normal semifinite weights retain the same original global scalar weight. -/
abbrev NormalSemifiniteFaithfulWeight (M : VonNeumannAlgebra H) : Type u :=
  {φ : CStarAlgebra.ScalarWeight.Weight M //
    IsNormalWeight M φ ∧ IsSemifiniteWeight M φ ∧ IsFaithfulWeight M φ}

end

end VonNeumannAlgebra
