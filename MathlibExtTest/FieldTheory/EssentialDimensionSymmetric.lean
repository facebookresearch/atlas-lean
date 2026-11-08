/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.EssentialDimensionSymmetric

/-!
# Essential dimension of symmetric groups: public-API checks

Exact-statement exercises for the general-polynomial model: algebraic
independence of coefficients and roots, transcendence degrees, the
Vieta factorization, the trivial descent, and the proved bounds
`edSn n ≤ n` and `C₇₉ ≤ 1`.
-/

@[expose] public section

namespace EssentialDimensionSymmetricTest

open MathlibExt.FieldTheory.EssentialDimensionSymmetric

/-- The coefficients of the general polynomial are algebraically
independent. -/
example (n : ℕ) : AlgebraicIndependent ℂ (coeff n) :=
  algebraicIndependent_coeff n

/-- The roots are algebraically independent in the function field. -/
example (n : ℕ) : AlgebraicIndependent ℂ (root n) :=
  algebraicIndependent_root n

/-- The roots are pairwise distinct. -/
example (n : ℕ) : Function.Injective (root n) := root_injective n

/-- The function field has transcendence degree `n` over `ℂ`. -/
example (n : ℕ) : transDegNat (rootsField n) = n :=
  transDegNat_rootsField n

/-- The coefficient field has transcendence degree `n` over `ℂ`. -/
example (n : ℕ) : transDegNat (generalBaseField n) = n :=
  transDegNat_generalBaseField n

/-- Vieta: the general polynomial splits over the function field as
the product of the linear factors `X - xᵢ`. -/
example (n : ℕ) :
    (generalPolynomial n).map
        (algebraMap (generalBaseField n) (rootsField n)) =
      ∏ i : Fin n, (Polynomial.X - Polynomial.C (root n i)) :=
  map_generalPolynomial n

/-- Every root satisfies the general polynomial. -/
example (n : ℕ) (i : Fin n) :
    Polynomial.aeval (root n i) (generalPolynomial n) = 0 :=
  root_mem_generalPolynomial_roots n i

/-- The roots generate the function field over `ℂ`. -/
example (n : ℕ) :
    IntermediateField.adjoin ℂ (Set.range (root n)) = ⊤ :=
  adjoin_roots_eq_top n

/-- The coefficient field is a descent parameter field (the trivial
descent). -/
example (n : ℕ) : IsDescent n (generalBaseField n) ⊤ :=
  isDescent_generalBaseField n

/-- Proved elementary bound on the essential dimension. -/
example (n : ℕ) : edSn n ≤ n := edSn_le n

/-- Proved elementary bound on the asymptotic ratio. -/
example : essDimRatio ≤ 1 := essDimRatio_le_one

end EssentialDimensionSymmetricTest
