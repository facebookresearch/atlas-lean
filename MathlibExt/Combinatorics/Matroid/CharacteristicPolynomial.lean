/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# Characteristic polynomial coefficients of a finite matroid

The signed subset expansion defines the coefficients of the characteristic polynomial.
Partial sums of its leading coefficients give the signed coefficients of the reduced
characteristic polynomial, following Adiprasito, Huh and Katz, *Hodge theory for
combinatorial geometries*, Section 9.1.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MatroidCharacteristicPolynomialLogConcaveAMR156Problem0026Wanted

/-- **Rank of a set in a matroid, as a natural number.** For a matroid $M$ and a set $X$, this is
the rank $r(X)$ of $X$ in $M$, the size of a largest independent set of $M$ contained in $X$,
taken as a natural number; it is $0$ when this rank is infinite. -/
noncomputable def finRank {α : Type*} (M : Matroid α) (X : Set α) : ℕ :=
  (M.eRk X).toNat

/-- **Coefficients of the characteristic polynomial of a matroid.** Let $M$ be a finite matroid on
the ground set $E$ with rank function $r$, and let
$\chi_M(\lambda) = \sum_{I \subseteq E} (-1)^{|I|} \lambda^{r(E) - r(I)}$ be its characteristic
polynomial. For a natural number $j$, this is the integer coefficient of $\lambda^j$ in
$\chi_M$, that is, the sum of $(-1)^{|I|}$ over the subsets $I \subseteq E$ with
$r(E) - r(I) = j$. -/
noncomputable def charPolyCoeff {α : Type*} (M : Matroid α) [M.Finite] (j : ℕ) : ℤ :=
  ∑ I ∈ M.ground_finite.toFinset.powerset.filter
      (fun I : Finset α => finRank M M.E - finRank M (I : Set α) = j), (-1) ^ I.card

/-- **Absolute coefficients of the characteristic polynomial of a matroid.** Let $M$ be a finite
matroid on the ground set $E$ with rank function $r$ and characteristic polynomial
$\chi_M(\lambda) = \sum_{I \subseteq E} (-1)^{|I|} \lambda^{r(E) - r(I)}$. For a natural number
$k$, $w_k(M)$ is the absolute value of the coefficient of $\lambda^{r(E) - k}$ in $\chi_M$ when
$k \le r(E)$, and $w_k(M) = 0$ when $k > r(E)$. -/
noncomputable def charPolyAbsCoeff {α : Type*} (M : Matroid α) [M.Finite] (k : ℕ) : ℕ :=
  if k ≤ finRank M M.E then (charPolyCoeff M (finRank M M.E - k)).natAbs else 0

/-- **Log-concavity of the characteristic polynomial of a matroid, statement.** For every finite
matroid $M$ on a ground set $E$ with rank function $r$, let $w_k(M)$ be the absolute value of the
coefficient of $\lambda^{r(E) - k}$ in the characteristic polynomial
$\chi_M(\lambda) = \sum_{I \subseteq E} (-1)^{|I|} \lambda^{r(E) - r(I)}$ when $k \le r(E)$, and
$w_k(M) = 0$ when $k > r(E)$. Then $w_{k-1}(M) \, w_{k+1}(M) \le w_k(M)^2$ for every natural
number $k \ge 1$.

This is part (a) of Stanley's Problem 25 (Read–Hoggar–Rota–Heron–Welsh). -/
def characteristicPolynomialLogConcave : Prop :=
  ∀ (α : Type) (M : Matroid α) [M.Finite] (k : ℕ), 1 ≤ k →
    charPolyAbsCoeff M (k - 1) * charPolyAbsCoeff M (k + 1) ≤ charPolyAbsCoeff M k ^ 2

end MathlibExt.Combinatorics.MatroidCharacteristicPolynomialLogConcaveAMR156Problem0026Wanted

namespace MathlibExt.Combinatorics.MatroidReducedCharacteristicPolynomialWanted

open MathlibExt.Combinatorics.MatroidCharacteristicPolynomialLogConcaveAMR156Problem0026Wanted

/-- **Coefficients `μ_k` of the reduced characteristic polynomial** (Adiprasito, Huh and Katz,
*Hodge theory for combinatorial geometries*, Ann. of Math. 188 (2018), Definition 9.1). For a
finite matroid `M` of rank `r + 1`, `(-1)^k μ_k(M)` is the coefficient of `λ^{r-k}` in
`χ̄_M(λ) = χ_M(λ) / (λ - 1)`, that is, `μ_k(M) = (-1)^k ∑_{i=0}^{k} [λ^{r+1-i}] χ_M(λ)`. -/
noncomputable def reducedCharPolyCoeff {α : Type*} (M : _root_.Matroid α) [M.Finite] (k : ℕ) :
    ℤ :=
  (-1) ^ k * ∑ i ∈ Finset.range (k + 1), charPolyCoeff M (finRank M M.E - i)

end MathlibExt.Combinatorics.MatroidReducedCharacteristicPolynomialWanted
