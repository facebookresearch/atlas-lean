/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The normal covering number of the symmetric groups (Kourovka Notebook Problem 18.23)

Kourovka Notebook, Archive of Solved Problems, Problem 18.23 (D. Bubboloni, C. E. Praeger, P.
Spiga): the normal covering number `γ(Sₙ)` is the least number of proper subgroups of `Sₙ` such that
every element of `Sₙ` is conjugate to an element of one of them. For `n = p₁^α₁ ⋯ p_r^α_r` with
primes `p₁ < ⋯ < p_r` the conjecture gives `γ(Sₙ)` in four cases; the proposers also ask whether it
holds for `n` sufficiently large.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.GroupTheory.NormalCoveringSymmetricKourovka18Problem23Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.23 (D.
Bubboloni, C. E. Praeger, P. Spiga). UnsolvedMath record UM-00701452 (`KOU-18.23`), dataset
ulamai/UnsolvedMath v1.8.0.

The conjectured value is `(n/2)(1 - 1/p₁)` (`r = 1`, `α₁ = 1`), `(n/2)(1 - 1/p₁) + 1` (`r = 1`, `α₁
≥ 2`), `(n/2)(1 - 1/p₁)(1 - 1/p₂) + 1` (`r = 2`, `α₁ + α₂ = 2`) and `(n/2)(1 - 1/p₁)(1 - 1/p₂) + 2`
(`r ≥ 2`, `α₁ + ⋯ + α_r ≥ 3`), computed in `ℚ`. The target is the "for `n` sufficiently large" form;
its refutation also refutes the conjecture for all `n` and avoids small degrees where the formula is
not meant (for `n = 3` it gives `1`, while no finite group is covered by the conjugates of one
proper subgroup).
-/

/-- The normal covering number `γ(Sₙ)`: the least number of proper subgroups `H₁, …, H_γ` of `Sₙ`
such that every element of `Sₙ` is conjugate to an element of some `Hᵢ`. -/
noncomputable def normalCoveringNumber (n : ℕ) : ℕ :=
  sInf {k | ∃ H : Fin k → Subgroup (Equiv.Perm (Fin n)), (∀ i, H i ≠ ⊤) ∧
    ∀ σ : Equiv.Perm (Fin n), ∃ i, ∃ τ ∈ H i, IsConj σ τ}

/-- The value conjectured by Bubboloni, Praeger and Spiga, for `n = p₁^α₁ ⋯ p_r^α_r` with primes
`p₁ < ⋯ < p_r`: `(n/2)(1 - 1/p₁)` if `r = 1, α₁ = 1`; `(n/2)(1 - 1/p₁) + 1` if `r = 1, α₁ ≥ 2`;
`(n/2)(1 - 1/p₁)(1 - 1/p₂) + 1` if `r = 2, α₁ + α₂ = 2`; `(n/2)(1 - 1/p₁)(1 - 1/p₂) + 2` if
`r ≥ 2, α₁ + ⋯ + α_r ≥ 3`. Here `r` is the number of distinct prime factors, `α₁ + ⋯ + α_r` the
number of prime factors with multiplicity, and `p₂` the least prime factor of `n / p₁^α₁`. -/
def conjecturedValue (n : ℕ) : ℚ :=
  let p₁ := n.minFac
  let p₂ := (n / p₁ ^ n.factorization p₁).minFac
  let a : ℚ := n / 2 * (1 - 1 / (p₁ : ℚ))
  let b : ℚ := a * (1 - 1 / (p₂ : ℚ))
  if n.primeFactors.card = 1 then
    (if n.primeFactorsList.length = 1 then a else a + 1)
  else if n.primeFactorsList.length = 2 then b + 1 else b + 2

/-- Kourovka 18.23 (D. Bubboloni, C. E. Praeger, P. Spiga), in the form "for all sufficiently large
`n`" that the proposers single out: `γ(Sₙ)` equals the conjectured value for every large `n`. -/
def normalCoveringNumberEventuallyConjectured : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, (normalCoveringNumber n : ℚ) = conjecturedValue n

/--
Resolved false: the Kourovka Archive records that A. Maróti showed the conjecture incorrect for odd
`n`. In Section 2 of Bubboloni-Praeger-Spiga (2020), Maróti's covering by the subgroups `P_k` (`k ≤
n/3`), `P_k` (`k < n/2` coprime to `n`) and `Sym(p) ≀ Sym(n/p)` gives `γ(Sym(n)) ≤ n/3 + φ(n)/2 +
ω(n)`, which is below the conjectured value for `n` the product of `r` consecutive primes starting
at `p ≥ 43` and every large `r`; the paper notes this contradicts the conjecture for infinitely many
`n`, so it fails for arbitrarily large `n`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 18.23 (D. Bubboloni, C. E. Praeger, P. Spiga); resolution: D. Bubboloni, C.
E. Praeger and P. Spiga, Linear bounds for the normal covering number of the symmetric and
alternating groups, Monatsh. Math. 191 (2020), 229-247, Section 2, A. Maróti's construction: for n =
N(r, p), the product of r consecutive primes starting at p ≥ 43, and r ≥ r*, γ(Sym(n)) < (n/2)(1 -
1/p₁)(1 - 1/p₂) + 2, contradicting the conjecture for infinitely many p and r; Kourovka Archive,
Problem 18.23,
https://api.research-repository.uwa.edu.au/ws/files/49055019/Bubboloni_et_al_2019_Linear_bounds_for_the_normal_covering.pdf.
-/
public theorem_wanted normalCoveringNumberEventuallyConjectured_refuted :
    ¬ normalCoveringNumberEventuallyConjectured

end MathlibExt.GroupTheory.NormalCoveringSymmetricKourovka18Problem23Wanted
