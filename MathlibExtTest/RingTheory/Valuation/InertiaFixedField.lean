/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.InertiaFixedField

@[expose] public section

open IsLocalRing

universe u

/-- Source-shaped consumer with the original binders: the intermediate-field and
discrete-valuation part of the source statement, for `5 ≤ q` and an auxiliary level `M'`
prime to `q`. -/
example (q : ℕ) [Fact q.Prime] (_hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (_hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀)
      (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A),
      IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
        Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))} ∧
      HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) ∧
      IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))) ∧
      (∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧
        ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :=
  ValuationSubring.exists_intermediateField_henselian_dvr_residue_approx A hA

/-- The valuation ring of the inertia fixed field is not a field: `q` is a non-zero non-unit,
so the prime hypothesis on `A` is what makes the ring discrete rather than trivial. -/
example (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) :
    ¬ IsUnit ((q : ℕ) : A.comap (algebraMap
      (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ∧
    ((q : ℕ) : A.comap (algebraMap
      (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) ≠ 0 :=
  ⟨(ValuationSubring.irreducible_natCast_comap_fixedField_inertiaSubgroupIn A hA).not_isUnit,
    (ValuationSubring.irreducible_natCast_comap_fixedField_inertiaSubgroupIn A hA).ne_zero⟩

/-- Every element of `A` is congruent to an element of the inertia fixed field. -/
example (q : ℕ) [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime q) (a : A) :
    ∃ y : A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
        (AlgebraicClosure ℚ)),
      residue A ⟨algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))
        (AlgebraicClosure ℚ) (y : IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)),
          y.2⟩ = residue A a :=
  ValuationSubring.exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq A hA _

/-- The Henselian property holds in an arbitrary universe and over any base field. -/
example {K : Type u} {L : Type (u + 1)} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (A : ValuationSubring L) :
    HenselianLocalRing
      (A.comap (algebraMap (IntermediateField.fixedField (A.inertiaSubgroupIn K)) L)) :=
  ValuationSubring.henselianLocalRing_comap_fixedField_inertiaSubgroupIn A
