/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_exists_phiIrreducible_evalSymm.lean`,
`P2M/Sol/S_ModularCurve_exists_phiIrreducible_evalSymm.lean`,
`Theorems/Thm_ModularCurve_finrank_adjoin_jqN_eq_of_prime.lean`,
`P2M/Sol/S_ModularCurve_finrank_adjoin_jqN_eq_of_prime.lean`,
`Theorems/Thm_ModularCurve_ModularPolynomialData_eq_of_prime.lean`,
`P2M/Sol/S_ModularCurve_ModularPolynomialData_eq_of_prime.lean`,
`Theorems/Thm_ModularCurve_exists_modularPolynomialData_evalSymm.lean`,
`P2M/Sol/S_ModularCurve_exists_modularPolynomialData_evalSymm.lean`,
`Theorems/Thm_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean`,
and
`P2M/Sol/S_ModularCurve_ModularPolynomialData_evalSymm_of_prime.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.SymmetryOfSplits
public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.AnalyticDescent
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.Cyclotomic.Basic

@[expose] public section

noncomputable section

open Polynomial IntermediateField

namespace ModularCurve

/-- For a prime `ℓ`, there is modular polynomial data of level `ℓ` whose polynomial is
irreducible over `ℚ(j)` and symmetric in its two variables. These are parts (ii) and (iii) of
Theorem 11.18 in D. A. Cox, *Primes of the Form x² + ny²* (3rd ed., 2022), for the modular
equation `Φ_ℓ`. -/
theorem exists_phiIrreducible_evalSymm (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, PhiIrreducible data ∧ EvalSymm data.Φ := by
  have : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  have hcyc : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  have : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  have : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]; exact hz
  have hζ1 : hzu.unit ^ ℓ = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  obtain ⟨c, hc⟩ := PhiGen.exists_phiGenDescends ℓ hzu.unit hζ
  have hint : ∀ k, PhiGen.IntCoeffs (c k) := fun k => hc.intCoeffs hζ1 k
  have hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq} :=
    fun k => PhiGen.mem_adjoin_jq_of_phiGenDescends ℓ hzu.unit hζ c hc k
  obtain ⟨data, hcoeff⟩ := PhiGen.exists_modularPolynomialData_coeff_eq hc hint hmem
  exact ⟨data,
    PhiGen.phiIrreducible_of_splits ℓ hzu.unit hζ data
      (PhiGen.splits_of_coeff_evalAtJ_eq hzu.unit hc data hcoeff),
    PhiGen.evalSymm_of_coeff_evalAtJ_eq hζ hc data hcoeff⟩

/-- For a prime `ℓ`, there is symmetric modular polynomial data of level `ℓ`. -/
theorem exists_modularPolynomialData_evalSymm (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    ∃ data : ModularPolynomialData ℓ, EvalSymm data.Φ :=
  let ⟨data, _, h⟩ := exists_phiIrreducible_evalSymm ℓ
  ⟨data, h⟩

variable {N : ℕ} [NeZero N]

private theorem isIntegral_jqN (data : ModularPolynomialData N) : IsIntegral ℚ⟮jq⟯ (jqN N) :=
  ⟨data.toAdjoin, data.toAdjoin_monic, by
    rw [← Polynomial.aeval_def]; exact data.aeval_jqN_toAdjoin⟩

private theorem natDegree_toAdjoin (data : ModularPolynomialData N) :
    data.toAdjoin.natDegree = ArithmeticFunction.dedekindPsi N := by
  rw [ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

/-- For a prime `ℓ`, the field extension `ℚ(j(q), j(q ^ ℓ)) / ℚ(j(q))` has degree `ℓ + 1`. -/
theorem finrank_adjoin_jqN_eq_of_prime (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮jqN ℓ⟯ = ℓ + 1 := by
  obtain ⟨data, hirr, -⟩ := exists_phiIrreducible_evalSymm ℓ
  rw [IntermediateField.adjoin.finrank (isIntegral_jqN data),
    ← (minpoly.eq_of_irreducible_of_monic hirr data.aeval_jqN_toAdjoin
      data.toAdjoin_monic), natDegree_toAdjoin, ArithmeticFunction.dedekindPsi_prime hℓ.out]

private theorem toAdjoin_eq_minpoly (p : ℕ) [hp : Fact p.Prime] (data : ModularPolynomialData p) :
    data.toAdjoin = minpoly ℚ⟮jq⟯ (jqN p) := by
  have hint := isIntegral_jqN data
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN p)).natDegree = p + 1 := by
    rw [← IntermediateField.adjoin.finrank hint]
    exact finrank_adjoin_jqN_eq_of_prime p
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) data.toAdjoin_monic
    (minpoly.dvd _ _ data.aeval_jqN_toAdjoin) ?_
  rw [hdeg, natDegree_toAdjoin, ArithmeticFunction.dedekindPsi_prime hp.out]

/-- For a prime `p`, modular polynomial data of level `p` is unique. -/
theorem ModularPolynomialData.eq_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)]
    (d d' : ModularPolynomialData p) : d = d' := by
  have h : d.Φ = d'.Φ := by
    apply Polynomial.map_injective evalAtJGen evalAtJGen_injective
    change d.toAdjoin = d'.toAdjoin
    rw [toAdjoin_eq_minpoly, toAdjoin_eq_minpoly]
  cases d; cases d'
  cases h
  rfl

/-- For a prime `p`, the polynomial of any modular polynomial data of level `p` is
symmetric: `Φ(x, y) = Φ(y, x)` for all rational Laurent series `x` and `y`. This is the symmetry
`Φ_p(X, Y) = Φ_p(Y, X)` of the modular equation, Theorem 11.18 (iii) in D. A. Cox, *Primes of the
Form x² + ny²* (3rd ed., 2022). -/
theorem ModularPolynomialData.evalSymm_of_prime (p : ℕ) [hp : Fact (Nat.Prime p)]
    (data : ModularPolynomialData p) : EvalSymm data.Φ := by
  obtain ⟨d, hd⟩ := exists_modularPolynomialData_evalSymm p
  rw [ModularPolynomialData.eq_of_prime p data d]
  exact hd

end ModularCurve

end
