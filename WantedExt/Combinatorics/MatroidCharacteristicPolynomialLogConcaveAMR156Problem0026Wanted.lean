/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Log-concavity of the characteristic polynomial of a matroid (Stanley, Problem 25(a))

R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics, Problem 25
(Read–Hoggar–Welsh–Mason): are the following sequences unimodal or log-concave for every finite
graph or matroid? (a) The absolute values of the coefficients of the chromatic polynomial of a
graph, or more generally of the characteristic polynomial of a matroid. (b) The numbers of
`i`-element independent sets of a matroid. (c) The Whitney numbers of the second kind of a geometric
lattice.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Matroid.Rank.ENat

@[expose] public section

namespace MathlibExt.Combinatorics.MatroidCharacteristicPolynomialLogConcaveAMR156Problem0026Wanted

/-!
Source: R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999),
Problem 25 (Read–Hoggar–Welsh–Mason conjectures). UnsolvedMath record UM-00801200 (`AMR-156-0026`),
dataset ulamai/UnsolvedMath v1.8.0.

Only part (a) is formalized, for matroids (the chromatic polynomial of a graph is the characteristic
polynomial of its cycle matroid up to a power of `λ`). The characteristic polynomial is Rota's
`χ_M(λ) = ∑_{I ⊆ E} (-1)^{|I|} λ^{r(E) - r(I)}` (the definition used by Adiprasito–Huh–Katz), with
ranks from Mathlib's `Matroid.eRk`; `w_k` is the absolute value of the coefficient of `λ^{r - k}`,
`r = r(E)`, extended by `0` past the degree, and log-concavity is `w_{k-1} w_{k+1} ≤ w_k²` for `k ≥
1`. Part (b) is implied by the existing entry `WantedExt/Combinatorics/StrongMasonWanted.lean`
(`strong_mason_conjecture`, ultra-log-concavity of the independent-set numbers), so it is not
restated; part (c) is still open (only top-heaviness is known) and is not formalized.
-/

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

/-- **Adiprasito–Huh–Katz theorem (Heron–Rota–Welsh conjecture).** For every finite matroid $M$
on a ground set $E$ with rank function $r$, let $w_k(M)$ be the absolute value of the coefficient
of $\lambda^{r(E) - k}$ in the characteristic polynomial
$\chi_M(\lambda) = \sum_{I \subseteq E} (-1)^{|I|} \lambda^{r(E) - r(I)}$ when $k \le r(E)$, and
$w_k(M) = 0$ when $k > r(E)$. Then $w_{k-1}(M) \, w_{k+1}(M) \le w_k(M)^2$ for every natural
number $k \ge 1$.

Huh had proved the case of graphs and realizable matroids in characteristic $0$.

Source:
R. P. Stanley, Positivity Problems and Conjectures in Algebraic Combinatorics (1999), Problem 25
(Read–Hoggar–Welsh–Mason conjectures); resolution: K. Adiprasito, J. Huh and E. Katz, Hodge theory
for combinatorial geometries, Ann. of Math. 188 (2018), 381-452, arXiv:1511.02888; J. Huh, Milnor
numbers of projective hypersurfaces and the chromatic polynomial of graphs, J. Amer. Math. Soc. 25
(2012), 907-927 (graphs), Theorem 9.9(2) (arXiv numbering): for every matroid M the coefficients of
the characteristic polynomial form a log-concave sequence; §1, Conjecture 1.1 defines χ_M and w_k as
above, https://arxiv.org/abs/1511.02888.
-/
public theorem_wanted characteristicPolynomialLogConcave_holds : characteristicPolynomialLogConcave

end MathlibExt.Combinatorics.MatroidCharacteristicPolynomialLogConcaveAMR156Problem0026Wanted
