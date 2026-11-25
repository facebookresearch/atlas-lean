/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Matroid.MixedDegrees
public import WantedExt.Combinatorics.MatroidReducedCharacteristicPolynomialWanted
public import Mathlib.Combinatorics.Matroid.Rank.ENat
public import Mathlib.Combinatorics.Matroid.Loop

/-!
# Hodge theory for matroids

The main theorem of K. Adiprasito, J. Huh and E. Katz, *Hodge theory for combinatorial
geometries*, Ann. of Math. 188 (2018), 381–452 (arXiv:1511.02888v2): the Chow ring `A*(M)_ℝ` of
a loopless matroid of rank `r + 1` (defined in `MathlibExt.Combinatorics.Matroid.ChowRing`)
carries a degree map `A^r(M)_ℝ ≅ ℝ` (Definition 5.9, Proposition 5.10) and satisfies the hard
Lefschetz theorem and the Hodge–Riemann relations with respect to the class `ℓ(c)` of any
strictly submodular function `c` (Theorem 1.4). The coefficients of the reduced characteristic
polynomial are the mixed degrees `μ_k(M) = deg(α_M^{r-k} β_M^k)` (Proposition 9.5); together
with the Hodge–Riemann relations in degree at most one this gives the log-concavity of
`μ_k(M)` (Proposition 9.8) and the Heron–Rota–Welsh conjecture (Theorem 9.9).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MatroidHodgeTheoryWanted

open MathlibExt.Combinatorics.Matroid.Chow

/-- **The degree map of a matroid** (Adiprasito, Huh and Katz, *Hodge theory for combinatorial
geometries*, Ann. of Math. 188 (2018), Definition 5.9 and Proposition 5.10). For a finite
loopless matroid `M` of rank `r + 1` there is exactly one linear map `deg : A*(M)_ℝ → ℝ` that
vanishes on the graded pieces `A^q(M)_ℝ` with `q ≠ r` and takes the value `1` on
`x_{F₁} ⋯ x_{F_r}` for every flag `F₁ ⊊ ⋯ ⊊ F_r` of nonempty proper flats; it restricts to an
isomorphism `A^r(M)_ℝ ≅ ℝ`. -/
theorem_wanted existsUnique_isDegreeMap {α : Type*} (M : _root_.Matroid α) [M.Finite]
    [M.Loopless] (r : ℕ) (hr : M.eRank = r + 1) :
    ∃! deg : ChowRing M →ₗ[ℝ] ℝ, IsDegreeMap M r deg

/-- **Hard Lefschetz theorem for matroids** (Adiprasito, Huh and Katz, *Hodge theory for
combinatorial geometries*, Ann. of Math. 188 (2018), Theorem 1.4 (1)). Let `M` be a finite
loopless matroid of rank `r + 1` and `ℓ = ℓ(c)` the class of a strictly submodular function. For
every `q ≤ r / 2`, multiplication by `ℓ^{r-2q}` is a bijection `A^q(M)_ℝ → A^{r-q}(M)_ℝ`: every
`b ∈ A^{r-q}(M)_ℝ` is `ℓ^{r-2q} a` for exactly one `a ∈ A^q(M)_ℝ`. -/
theorem_wanted hardLefschetz {α : Type*} (M : _root_.Matroid α) [M.Finite] [M.Loopless]
    (r : ℕ) (hr : M.eRank = r + 1) (c : Set α → ℝ) (hc : IsStrictlySubmodular M c) (q : ℕ)
    (hq : 2 * q ≤ r) (b : ChowRing M) (hb : b ∈ gradedPiece M (r - q)) :
    ∃! a : ChowRing M, a ∈ gradedPiece M q ∧ ellClass M c ^ (r - 2 * q) * a = b

/-- **Hodge–Riemann relations for matroids** (Adiprasito, Huh and Katz, *Hodge theory for
combinatorial geometries*, Ann. of Math. 188 (2018), Theorem 1.4 (2)). Let `M` be a finite
loopless matroid of rank `r + 1`, `deg` its degree map and `ℓ = ℓ(c)` the class of a strictly
submodular function. For every `q ≤ r / 2`, the symmetric bilinear form
`(a₁, a₂) ↦ (-1)^q deg(a₁ ℓ^{r-2q} a₂)` on `A^q(M)_ℝ` is positive definite on the kernel of
multiplication by `ℓ^{r-2q+1}`: if `a ∈ A^q(M)_ℝ` is nonzero and `ℓ · ℓ^{r-2q} a = 0`, then
`(-1)^q deg(a ℓ^{r-2q} a) > 0`. -/
theorem_wanted hodgeRiemann {α : Type*} (M : _root_.Matroid α) [M.Finite] [M.Loopless]
    (r : ℕ) (hr : M.eRank = r + 1) (deg : ChowRing M →ₗ[ℝ] ℝ) (hdeg : IsDegreeMap M r deg)
    (c : Set α → ℝ) (hc : IsStrictlySubmodular M c) (q : ℕ) (hq : 2 * q ≤ r) (a : ChowRing M)
    (ha : a ∈ gradedPiece M q) (ha0 : a ≠ 0)
    (hker : ellClass M c * (ellClass M c ^ (r - 2 * q) * a) = 0) :
    0 < (-1) ^ q * deg (a * (ellClass M c ^ (r - 2 * q) * a))

end MathlibExt.Combinatorics.MatroidHodgeTheoryWanted
