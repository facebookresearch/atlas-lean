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
public import MathlibExt.Combinatorics.Matroid.CharacteristicPolynomial

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
1`. Part (b) is implied by `strong_mason_conjecture` in
`MathlibExt/Combinatorics/Matroid/StrongMason.lean` (ultra-log-concavity of the independent-set
numbers), so it is not restated; part (c) is still open (only top-heaviness is known) and is not
formalized.
-/

/-- **Adiprasito–Huh–Katz theorem (Heron–Rota–Welsh conjecture).** For every finite matroid $M$
on a ground set $E$ with rank function $r$, let $w_k(M)$ be the absolute value of the coefficient
of $\lambda^{r(E) - k}$ in the characteristic polynomial
$\chi_M(\lambda) = \sum_{I \subseteq E} (-1)^{|I|} \lambda^{r(E) - r(I)}$ when $k \le r(E)$, and
$w_k(M) = 0$ when $k > r(E)$. Then $w_{k-1}(M) \, w_{k+1}(M) \le w_k(M)^2$ for every natural
number $k \ge 1$.

Resolved true: Adiprasito, Huh and Katz proved the Heron–Rota–Welsh conjecture: for every matroid
the absolute values `w_k` of the coefficients of the characteristic polynomial form a log-concave
sequence (K. Adiprasito, J. Huh and E. Katz, Hodge theory for combinatorial geometries, Ann. of
Math. 188 (2018), 381-452, Theorem 9.9(2) (arXiv numbering); §1, Conjecture 1.1 defines χ_M and
`w_k` as above; https://arxiv.org/abs/1511.02888). Earlier cases: matroids representable over a
field of characteristic `0`, which include graphs (J. Huh, Milnor numbers of projective
hypersurfaces and the chromatic polynomial of graphs, J. Amer. Math. Soc. 25 (2012), 907-927,
Theorem 3), and matroids realizable over some field (J. Huh and E. Katz, Log-concavity of
characteristic polynomials and the Bergman fan of matroids, Math. Ann. 354 (2012), 1103-1116,
Theorems 1.1 and 6.2). Source of the problem: R. P. Stanley, Positivity Problems and Conjectures in
Algebraic Combinatorics (1999), Problem 25 (Read–Hoggar–Welsh–Mason conjectures).
-/
public theorem_wanted characteristicPolynomialLogConcave_holds : characteristicPolynomialLogConcave

end MathlibExt.Combinatorics.MatroidCharacteristicPolynomialLogConcaveAMR156Problem0026Wanted
