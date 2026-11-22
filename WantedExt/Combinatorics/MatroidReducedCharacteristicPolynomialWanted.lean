/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Combinatorics.MatroidCharacteristicPolynomialLogConcaveAMR156Problem0026Wanted

/-!
# The reduced characteristic polynomial of a matroid

Following K. Adiprasito, J. Huh and E. Katz, *Hodge theory for combinatorial geometries*,
Ann. of Math. 188 (2018), 381–452 (arXiv:1511.02888v2), Section 9.1: for a loopless matroid `M`
of rank `r + 1` the characteristic polynomial satisfies `χ_M(1) = 0`, the reduced
characteristic polynomial is `χ̄_M(λ) = χ_M(λ) / (λ - 1) = ∑_{k=0}^{r} (-1)^k μ_k(M) λ^{r-k}`
(Definition 9.1), and Proposition 9.8 shows that `μ_0, …, μ_r` is log-concave. The coefficient
of `λ^{r-k}` in `χ̄_M` is the partial sum `∑_{i=0}^{k} [λ^{r+1-i}] χ_M` of the top coefficients
of `χ_M`, which is how `μ_k` is defined below; for a matroid with a loop `χ_M = 0` and every
`μ_k` is `0`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MatroidReducedCharacteristicPolynomialWanted

open MathlibExt.Combinatorics.MatroidCharacteristicPolynomialLogConcaveAMR156Problem0026Wanted

/-- **Coefficients `μ_k` of the reduced characteristic polynomial** (Adiprasito, Huh and Katz,
*Hodge theory for combinatorial geometries*, Ann. of Math. 188 (2018), Definition 9.1). For a
finite matroid `M` of rank `r + 1`, `(-1)^k μ_k(M)` is the coefficient of `λ^{r-k}` in
`χ̄_M(λ) = χ_M(λ) / (λ - 1)`, that is, `μ_k(M) = (-1)^k ∑_{i=0}^{k} [λ^{r+1-i}] χ_M(λ)`. -/
noncomputable def reducedCharPolyCoeff {α : Type*} (M : _root_.Matroid α) [M.Finite] (k : ℕ) :
    ℤ :=
  (-1) ^ k * ∑ i ∈ Finset.range (k + 1), charPolyCoeff M (finRank M M.E - i)

/-- **Log-concavity of the reduced characteristic polynomial** (Adiprasito, Huh and Katz,
*Hodge theory for combinatorial geometries*, Ann. of Math. 188 (2018), Proposition 9.8 and
Theorem 9.9 (1)). For every finite matroid `M` of rank `r + 1` and every positive integer
`k < r`, `μ_{k-1}(M) μ_{k+1}(M) ≤ μ_k(M)^2`. (AHK state this for loopless matroids; with a loop
every `μ_k` is `0`.) -/
theorem_wanted reducedCharPolyCoeff_logConcave {α : Type*} (M : _root_.Matroid α) [M.Finite]
    (k : ℕ) (hk : 0 < k) (hkr : k + 1 < finRank M M.E) :
    reducedCharPolyCoeff M (k - 1) * reducedCharPolyCoeff M (k + 1) ≤
      reducedCharPolyCoeff M k ^ 2

end MathlibExt.Combinatorics.MatroidReducedCharacteristicPolynomialWanted
