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

/-- The rank `r(X)` of a set `X` in a finite matroid, as a natural number. -/
noncomputable def finRank {α : Type*} (M : Matroid α) (X : Set α) : ℕ :=
  (M.eRk X).toNat

/-- The coefficient of `λ ^ j` in Rota's characteristic polynomial
`χ_M(λ) = ∑_{I ⊆ E} (-1)^{|I|} λ^{r(E) - r(I)}` of a finite matroid `M` on the ground set `E`. -/
noncomputable def charPolyCoeff {α : Type*} (M : Matroid α) [M.Finite] (j : ℕ) : ℤ :=
  ∑ I ∈ M.ground_finite.toFinset.powerset.filter
      (fun I : Finset α => finRank M M.E - finRank M (I : Set α) = j), (-1) ^ I.card

/-- `w_k(M)`: the absolute value of the coefficient of `λ ^ (r - k)` in `χ_M`, where `r = r(E)` is
the rank of `M`, and `0` for `k > r`. -/
noncomputable def charPolyAbsCoeff {α : Type*} (M : Matroid α) [M.Finite] (k : ℕ) : ℕ :=
  if k ≤ finRank M M.E then (charPolyCoeff M (finRank M M.E - k)).natAbs else 0

/-- Part (a) of Stanley's Problem 25 (Read–Hoggar–Rota–Heron–Welsh), answered: for every finite
matroid the absolute values of the coefficients of the characteristic polynomial form a
log-concave sequence, `w_{k-1} w_{k+1} ≤ w_k²`. -/
def characteristicPolynomialLogConcave : Prop :=
  ∀ (α : Type) (M : Matroid α) [M.Finite] (k : ℕ), 1 ≤ k →
    charPolyAbsCoeff M (k - 1) * charPolyAbsCoeff M (k + 1) ≤ charPolyAbsCoeff M k ^ 2

/--
Resolved true: Adiprasito, Huh and Katz proved the Heron–Rota–Welsh conjecture: for every matroid
the absolute values `w_k` of the coefficients of the characteristic polynomial form a log-concave
sequence (Huh had proved the case of graphs and realizable matroids in characteristic `0`). Source:
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
