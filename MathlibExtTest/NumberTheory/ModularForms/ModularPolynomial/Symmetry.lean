/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.Symmetry

@[expose] public section

open ModularCurve IntermediateField

/-- Source-shaped consumer, with the original binders. -/
example (p : ℕ) [hp : Fact (Nat.Prime p)] (data : ModularPolynomialData p) :
    EvalSymm data.Φ :=
  ModularCurve.ModularPolynomialData.evalSymm_of_prime p data

/-- Symmetry swaps the roles of `j(q)` and `j(q ^ p)` in the defining relation:
`Φ(j(q ^ p), j(q)) = 0` gives `Φ(j(q), j(q ^ p)) = 0`. -/
example (p : ℕ) [Fact (Nat.Prime p)] (data : ModularPolynomialData p) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (jqN p)).toRingHom jq = 0 := by
  rw [ModularPolynomialData.evalSymm_of_prime p data (jqN p) jq, ← evalAtJ_def]
  exact data.eval_eq_zero

/-- Symmetry is a real constraint: the polynomial `X` (outer variable only) is not
symmetric. -/
example : ¬ EvalSymm (Polynomial.X : Polynomial (Polynomial ℤ)) := by
  intro h
  have h01 := h 0 1
  simp only [Polynomial.eval₂_X] at h01
  exact one_ne_zero h01

/-- The uniqueness and degree statements the proof goes through, at level `2`. -/
example (d d' : ModularPolynomialData 2) : d = d' :=
  ModularPolynomialData.eq_of_prime 2 d d'

example : Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN 2⟯ = 3 :=
  finrank_adjoin_jqN_eq_of_prime 2

/-- Existence at every prime level, with irreducibility over `ℚ(j)`. -/
example (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, PhiIrreducible data ∧ EvalSymm data.Φ :=
  exists_phiIrreducible_evalSymm ℓ

/-- The pole bound holds over any coefficient field: after embedding its coefficients into `ℂ`,
`j` still has at most a simple pole. -/
example : PoleOrderLE (coeffEmb ℂ jq) 1 := fun k hk => by
  rw [coeffEmb_coeff, coeff_jq_of_lt (by exact_mod_cast hk), map_zero]

/-- The bound is sharp: `j` has a pole, so its pole order is not at most `0`. -/
example : ¬ PoleOrderLE jq 0 := fun h => by
  have h1 := h (-1) (by norm_num)
  rw [coeff_jq_neg_one] at h1
  exact one_ne_zero h1

/-- The twist by a unit `u` multiplies the coefficient of `q ^ k` by `u ^ k`, for negative `k`
too. -/
example : (qTwist (Units.mk0 (2 : ℚ) two_ne_zero) jq).coeff (-1) = 1 / 2 := by
  rw [qTwist_coeff, coeff_jq_neg_one, mul_one, zpow_neg_one, Units.val_inv_eq_inv_val,
    Units.val_mk0, one_div]

/-- The coset representatives are `!![ℓ, 0; 0, 1]` (index `0`) and `!![1, b; 0, ℓ]` (index
`b + 1`); here `ℓ = 3` and `b = 1`. -/
example : PhiGen.cosetA 3 0 = 3 ∧ PhiGen.cosetB 3 0 = 0 ∧
    PhiGen.cosetA 3 2 = 1 ∧ PhiGen.cosetB 3 2 = 1 := by
  decide
