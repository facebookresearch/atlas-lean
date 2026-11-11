/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.ResidueFieldRoots

@[expose] public section

example (K : Type*) [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) (IsLocalRing.ResidueField ↥A)] :
    Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField ↥A) :=
  ValuationSubring.algebra_isAlgebraic_zmod_residueField_of_isAlgebraic_rat K A p

example (K : Type*) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    (m : ℕ) (hm : (m : IsLocalRing.ResidueField ↥A) ≠ 0) :
    (∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 →
      IsLocalRing.residue ↥A ζ₁ = IsLocalRing.residue ↥A ζ₂ → ζ₁ = ζ₂) ∧
    (∀ u : IsLocalRing.ResidueField ↥A, u ^ m = 1 →
      ∃ ζ : ↥A, ζ ^ m = 1 ∧ IsLocalRing.residue ↥A ζ = u) :=
  ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed K A m hm
