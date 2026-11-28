/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MultigradedHilbertSeries
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public noncomputable section

namespace MathlibExtTest.RingTheory.MultigradedHilbertSeries

open MvPolynomial MathlibExt.RingTheory.MultigradedHilbertSeries

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {k : Type*} [Field k]

/-! ### Positivity and finiteness -/

/-- The standard grading of `k[x]` by `ℕ = ℕ^1`: the variable has degree `1`. -/
abbrev w₁ : Fin 1 → (Fin 1 →₀ ℕ) := fun _ ↦ Finsupp.single 0 1

instance : Fact (∀ i, w₁ i ≠ 0) := ⟨fun _ ↦ Finsupp.single_ne_zero.mpr one_ne_zero⟩

-- Positivity makes every quotient piece finite-dimensional, by instance search.
example (I : HomogeneousIdeal (weightedHomogeneousSubmodule k w₁)) (a : Fin 1 →₀ ℕ) :
    Module.Finite k (quotientPiece w₁ I a) :=
  inferInstance

-- The fine `ℕ²`-grading of `k[x, y]`: each bidegree contains finitely many monomials.
example (a : Fin 2 →₀ ℕ) :
    {d : Fin 2 →₀ ℕ | Finsupp.weight (fun i : Fin 2 ↦ Finsupp.single i 1) d = a}.Finite :=
  finite_setOf_weight_eq (fun _ ↦ Finsupp.single_ne_zero.mpr one_ne_zero) a

-- Positivity is necessary: with a variable of degree `0`, the degree-`0` monomials are all of
-- them, so the degree-`0` piece is infinite-dimensional.
example : ¬ {d : Fin 1 →₀ ℕ | Finsupp.weight (fun _ : Fin 1 ↦ (0 : Fin 1 →₀ ℕ)) d = 0}.Finite := by
  have : {d : Fin 1 →₀ ℕ | Finsupp.weight (fun _ : Fin 1 ↦ (0 : Fin 1 →₀ ℕ)) d = 0} =
      Set.univ :=
    Set.eq_univ_of_forall fun d ↦ by simp [Finsupp.weight_apply]
  rw [this]
  exact Set.infinite_univ

/-! ### Hilbert series of the zero ring and of the polynomial ring -/

-- The zero quotient `k[x] ⧸ ⊤` has Hilbert series zero.
example : hilbertSeries (k := k) w₁ ⊤ = 0 := by
  ext a
  have : Subsingleton (MvPolynomial (Fin 1) k ⧸
      (⊤ : HomogeneousIdeal (weightedHomogeneousSubmodule k w₁)).toIdeal) := by
    rw [HomogeneousIdeal.toIdeal_top]
    exact Ideal.Quotient.subsingleton_iff.mpr rfl
  simp [Module.finrank_zero_of_subsingleton]

/-- The coefficients of the Hilbert series of `k[x] ⧸ ⊥ = k[x]` count monomials. -/
theorem coeff_hilbertSeries_bot {n r : ℕ} (w : Fin n → (Fin r →₀ ℕ)) [Fact (∀ i, w i ≠ 0)]
    (a : Fin r →₀ ℕ) :
    MvPowerSeries.coeff a
        (hilbertSeries w (⊥ : HomogeneousIdeal (weightedHomogeneousSubmodule k w))) =
      Nat.card {d : Fin n →₀ ℕ | Finsupp.weight w d = a} := by
  have hinj : Function.Injective
      (Ideal.Quotient.mkₐ k
        (⊥ : HomogeneousIdeal (weightedHomogeneousSubmodule k w)).toIdeal).toLinearMap := by
    intro p q h
    simpa [HomogeneousIdeal.toIdeal_bot, Ideal.Quotient.eq, sub_eq_zero] using h
  rw [coeff_hilbertSeries, quotientPiece,
    ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _),
    weightedHomogeneousSubmodule_eq_finsupp_supported]
  exact congrArg Nat.cast (Module.finrank_eq_nat_card_basis (basisRestrictSupport k _))

-- The degree-`0` piece of `k[x]` is spanned by the constants.
example : MvPowerSeries.coeff 0 (hilbertSeries (k := k) w₁ ⊥) = 1 := by
  rw [coeff_hilbertSeries_bot]
  have : {d : Fin 1 →₀ ℕ | Finsupp.weight w₁ d = 0} = {0} := by
    have := Finsupp.nonTorsionWeight_of (R := ℕ) (w := w₁) Fact.out
    ext d
    simp [Finsupp.weight_eq_zero_iff_eq_zero]
  rw [this]
  simp

/-! ### The denominator -/

-- For `k[x]` with the standard grading the denominator is `1 - t`.
example : MvPowerSeries.coeff 0 (denominator w₁) = 1 := by
  rw [denominator, Fin.prod_univ_one, map_sub, MvPowerSeries.coeff_one,
    MvPowerSeries.coeff_monomial]
  simpa using ((Fact.out : ∀ i, w₁ i ≠ 0) 0).symm

example : MvPowerSeries.coeff (Finsupp.single 0 1) (denominator w₁) = -1 := by
  simp [denominator, MvPowerSeries.coeff_one]

example : MvPowerSeries.coeff (Finsupp.single 0 2) (denominator w₁) = 0 := by
  rw [denominator, Fin.prod_univ_one, map_sub, MvPowerSeries.coeff_one,
    MvPowerSeries.coeff_monomial]
  simp [w₁]

end MathlibExtTest.RingTheory.MultigradedHilbertSeries
