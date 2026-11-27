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

`Theorems/Thm_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.lean`
and
`P2M/Sol/S_ModularCurve_PhiGen_evalSymm_of_coeff_evalAtJ_eq.lean`
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

public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.Descends
public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.CosetProduct
public import MathlibExt.NumberTheory.ModularForms.ModularPolynomial.Irreducible
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section

open Polynomial

namespace ModularCurve
namespace PhiGen

section Seam

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}
variable {c : ℕ → LaurentSeries ℚ}

namespace PhiGenDescends

private theorem coeff_phiProd_coeff (hc : PhiGenDescends ℓ ζ c) (k : ℕ)
    (m : ℤ) :
    ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff ((ℓ : ℤ) * m) = algebraMap ℚ K ((c k).coeff m) := by
  rw [hc k, coeffEmb_coeff, qExpand_coeff_mul]

private theorem c_zero_coeff_lead (hc : PhiGenDescends ℓ ζ c)
    (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    (c 0).coeff (-((ℓ + 1 : ℕ) : ℤ)) = 1 := by
  refine (algebraMap ℚ K).injective ?_
  rw [← hc.coeff_phiProd_coeff 0 (-((ℓ + 1 : ℕ) : ℤ)), map_one]
  have hidx : (ℓ : ℤ) * (-((ℓ + 1 : ℕ) : ℤ)) = -((ℓ * ℓ + ℓ : ℕ) : ℤ) := by push_cast; ring
  rw [hidx]
  exact phiProd_conj_coeff_zero_lead ℓ ζ hζ

private theorem c_coeff_eq_zero_of_ne_zero (hc : PhiGenDescends ℓ ζ c)
    (k : ℕ) (hk : k ≠ 0) (m : ℕ) (hm : ℓ + 1 ≤ m) :
    (c k).coeff (-(m : ℤ)) = 0 := by
  refine (algebraMap ℚ K).injective ?_
  rw [← hc.coeff_phiProd_coeff k (-(m : ℤ)), map_zero]
  have hidx : (ℓ : ℤ) * (-(m : ℤ)) = -((ℓ * m : ℕ) : ℤ) := by push_cast; ring
  rw [hidx]
  exact phiProd_conj_coeff_eq_zero_of_le ℓ ζ k hk (ℓ * m) (by nlinarith [hℓ.out.two_le])

private theorem c_zero_coeff_eq_zero_of_lt (hc : PhiGenDescends ℓ ζ c)
    (m : ℕ) (hm : ℓ + 1 < m) :
    (c 0).coeff (-(m : ℤ)) = 0 :=
  hc.poleOrderLE 0 (-(m : ℤ)) (by push_cast; omega)

end PhiGenDescends
end Seam

section Symmetry

variable {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ}
variable {c : ℕ → LaurentSeries ℚ}

theorem evalSymm_of_coeff_evalAtJ_eq (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hc : PhiGenDescends ℓ ζ c) (data : ModularPolynomialData ℓ)
    (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) :
    EvalSymm data.Φ := by
  have hsplit :
      data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) :=
    splits_of_coeff_evalAtJ_eq ζ hc data hcoeff
  have h0top :
      (evalAtJ (data.Φ.coeff 0)).coeff (-((ArithmeticFunction.dedekindPsi ℓ : ℕ) : ℤ)) = 1 := by
    rw [hcoeff 0, ArithmeticFunction.dedekindPsi_prime hℓ.out]
    exact hc.c_zero_coeff_lead hζ
  have h0le : ∀ m : ℕ, ArithmeticFunction.dedekindPsi ℓ < m →
      (evalAtJ (data.Φ.coeff 0)).coeff (-(m : ℤ)) = 0 := by
    intro m hm
    rw [hcoeff 0]
    exact hc.c_zero_coeff_eq_zero_of_lt m
      (by rwa [ArithmeticFunction.dedekindPsi_prime hℓ.out] at hm)
  have hk : ∀ k, k ≠ 0 → ∀ m : ℕ, ArithmeticFunction.dedekindPsi ℓ ≤ m →
      (evalAtJ (data.Φ.coeff k)).coeff (-(m : ℤ)) = 0 := by
    intro k hk0 m hm
    rw [hcoeff k]
    exact hc.c_coeff_eq_zero_of_ne_zero k hk0 m
      (by rwa [ArithmeticFunction.dedekindPsi_prime hℓ.out] at hm)
  obtain ⟨hTmonic, hTdeg⟩ := data.transposeToAdjoin_monic_of_qExpansion h0top h0le hk
  exact evalSymm_of_splits ℓ ζ hζ data hsplit hTmonic hTdeg.le

end Symmetry

end PhiGen
end ModularCurve

end
