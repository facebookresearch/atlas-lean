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
# Faithful, normal and semifinite extended weights

For a concrete von Neumann algebra `M`, a scalar weight is an additive map `φ : M₊ → [0,∞]`,
homogeneous for finite nonnegative real scalars and zero at zero. Faithfulness means `φ(a)=0`
implies `a=0` on `M₊`.

Normality preserves the least upper bound of every nonempty norm-bounded directed positive set.
Semifiniteness here means that the complex span of finite-weight positive elements is
ultraweakly dense in `M`. A normal semifinite faithful weight satisfies all three properties and
retains these extended positive values.

Infinite values are allowed; no supremum is chosen in the weight bundle, and the finite positive
span is distinct from the finite square domain.
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

/-- **Faithfulness of an extended positive weight.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an extended
positive weight: additive, homogeneous for finite nonnegative real scalars, and zero at
zero. `IsFaithfulWeight M φ` means `φ(a)=0 → a=0` for every positive `a ∈ M`. -/
def IsFaithfulWeight (M : VonNeumannAlgebra H) (φ : CStarAlgebra.ScalarWeight.Weight M) : Prop :=
  ∀ a : CStarAlgebra.ScalarWeight.PositiveElement M, φ.value a = 0 → (a : M) = 0

/-- **Normality by bounded directed positive suprema.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an extended
positive weight: additive, homogeneous for finite nonnegative real scalars, and zero at
zero. `IsNormalWeight M φ` means: if a nonempty directed set `S ⊆ M₊` is bounded in
operator norm and has least upper bound `s ∈ M₊`, then `φ(s)` is the least upper bound of
`φ(S)` in `[0,∞]`. -/
def IsNormalWeight (M : VonNeumannAlgebra H) (φ : CStarAlgebra.ScalarWeight.Weight M) : Prop :=
  ∀ S : Set (CStarAlgebra.ScalarWeight.PositiveElement M), S.Nonempty →
    DirectedOn (fun a b : CStarAlgebra.ScalarWeight.PositiveElement M => (a : M) ≤ (b : M)) S →
    (∃ C : ℝ, ∀ a ∈ S, ‖(a : M)‖ ≤ C) →
    ∀ s : CStarAlgebra.ScalarWeight.PositiveElement M,
      IsLUB ((fun a : CStarAlgebra.ScalarWeight.PositiveElement M => (a : M)) '' S) (s : M) →
      IsLUB (φ.value '' S) (φ.value s)

/-- **Semifiniteness by ultraweak totality of finite positive elements.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊
→ [0,∞]` be an extended positive weight: additive, homogeneous for finite nonnegative real
scalars, and zero at zero. `IsSemifiniteWeight M φ` means `span ℂ {a ∈ M₊ : φ(a)<∞}` is
dense in `M` for the ultraweak topology. This is the finite-positive integration span, not
the finite-square domain. -/
def IsSemifiniteWeight (M : VonNeumannAlgebra H) (φ : CStarAlgebra.ScalarWeight.Weight M) : Prop :=
  Dense ((φ.finiteIntegrationDomain.map (ultraweakLinearEquiv M).symm.toLinearMap :
    Submodule ℂ (Ultraweak M)) : Set (Ultraweak M))

/-- **Normal semifinite faithful weight on a concrete algebra.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `φ : M₊ → [0,∞]` be an
extended positive weight: additive, homogeneous for finite nonnegative real scalars, and
zero at zero. `NormalSemifiniteFaithfulWeight M` is the subtype of weights preserving
bounded directed positive least upper bounds, with ultraweakly dense finite-positive span
and zero value only at zero on the positive cone. -/
abbrev NormalSemifiniteFaithfulWeight (M : VonNeumannAlgebra H) : Type u :=
  {φ : CStarAlgebra.ScalarWeight.Weight M //
    IsNormalWeight M φ ∧ IsSemifiniteWeight M φ ∧ IsFaithfulWeight M φ}

end

end VonNeumannAlgebra
