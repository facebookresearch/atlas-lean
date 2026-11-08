/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Fermat
public import Mathlib.NumberTheory.FermatPsp
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import MathlibExt.Data.Set.Density
public import MathlibExt.NumberTheory.StrongPseudoprime

/-!
# Pseudoprime bases and Fermat numbers

Statements from Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24
(2024), Article A23. The paper's `F_n` (pseudoprime bases `1 ≤ b < n`) is written with
Mathlib's `Nat.FermatPsp`, and its `R_n` (strong pseudoprime bases `1 ≤ b < n`) with the
predicate `MetaMathlibExt.IsStrongPseudoprime` (`MathlibExt/NumberTheory/StrongPseudoprime.lean`),
which follows the paper's Congruences (2) and (3). Theorems 1 and 9 (polynomial-time factoring algorithms) are not
stated; see the source audit table.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Monier; Baillie–Wagstaff.** For a composite `n > 1`, the number of pseudoprime bases
`1 ≤ b < n` is `∏_{p ∣ n} gcd(n - 1, p - 1)` over the distinct prime divisors `p` of `n`.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 2 (`integers-2024-A23-thm-2`). -/
public theorem_wanted card_fermatPsp_bases_eq_prod_gcd {n : ℕ} (hn : 1 < n) (hcomp : ¬n.Prime) :
    {b : ℕ | 1 ≤ b ∧ b < n ∧ Nat.FermatPsp n b}.ncard =
      ∏ p ∈ n.primeFactors, Nat.gcd (n - 1) (p - 1)

/-- A product of two distinct primes has a square number of pseudoprime bases `1 ≤ b < pq`.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 1 (`integers-2024-A23-cor-1`). -/
public theorem_wanted isSquare_card_fermatPsp_bases_mul_of_prime {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) :
    IsSquare {b : ℕ | 1 ≤ b ∧ b < p * q ∧ Nat.FermatPsp (p * q) b}.ncard

/-- **Monier's formula.** Let `n` be an odd composite number with `r` distinct prime
factors `p`, write `n - 1 = 2 ^ k * d` and `p - 1 = 2 ^ (k_p) * d_p` with `d`, `d_p` odd,
and let `v = min_p k_p`. Then the number of strong pseudoprime bases `1 ≤ b < n` is
`(1 + (2 ^ (v r) - 1) / (2 ^ r - 1)) * ∏_p gcd(d, d_p)`. Odd parts are written
`ordCompl[2] m`, and the identity is stated in `ℚ`.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 3, Formula (5) (`integers-2024-A23-thm-3`). -/
public theorem_wanted card_strongPseudoprime_bases {n : ℕ} (hn : 1 < n) (hcomp : ¬n.Prime)
    (hodd : Odd n) :
    let r := n.primeFactors.card
    let v := sInf ((fun p => (p - 1).factorization 2) '' (n.primeFactors : Set ℕ))
    ({b : ℕ | 1 ≤ b ∧ b < n ∧ IsStrongPseudoprime n b}.ncard : ℚ) =
      (1 + (2 ^ (v * r) - 1) / (2 ^ r - 1)) *
        ∏ p ∈ n.primeFactors, (Nat.gcd (ordCompl[2] (n - 1)) (ordCompl[2] (p - 1)) : ℚ)

/-- For an odd composite `n`, with `r` and `v` as in Monier's formula, the following are
equivalent: (a) the strong pseudoprime bases form a subgroup of `(ZMod n)ˣ` (equivalently of
the group of pseudoprime bases, which contains them); (b) their number divides the number of
pseudoprime bases; (c) `v = 1` or `r = 1`; (d) some prime `p ≡ 3 (mod 4)` divides `n`, or
`n` is a prime power.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 4 (`integers-2024-A23-thm-4`). -/
public theorem_wanted strongPseudoprime_bases_subgroup_tfae {n : ℕ} (hn : 1 < n)
    (hcomp : ¬n.Prime) (hodd : Odd n) :
    let r := n.primeFactors.card
    let v := sInf ((fun p => (p - 1).factorization 2) '' (n.primeFactors : Set ℕ))
    [∃ H : Subgroup (ZMod n)ˣ, ∀ u : (ZMod n)ˣ, u ∈ H ↔ IsStrongPseudoprime n (u : ZMod n),
      {b : ℕ | 1 ≤ b ∧ b < n ∧ IsStrongPseudoprime n b}.ncard ∣
        {b : ℕ | 1 ≤ b ∧ b < n ∧ Nat.FermatPsp n b}.ncard,
      v = 1 ∨ r = 1,
      (∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3) ∨ IsPrimePow n].TFAE

/-- The odd composite numbers `n` whose strong pseudoprime bases do not form a subgroup of
`(ZMod n)ˣ` have natural density `0`.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 2 (`integers-2024-A23-cor-2`). -/
public theorem_wanted hasDensity_zero_strongPseudoprime_bases_not_subgroup :
    Set.HasDensity {n : ℕ | 1 < n ∧ ¬n.Prime ∧ Odd n ∧
      ¬∃ H : Subgroup (ZMod n)ˣ, ∀ u : (ZMod n)ˣ, u ∈ H ↔ IsStrongPseudoprime n (u : ZMod n)} 0

/-- The four equivalent statements of Theorem 4 hold for almost all odd composite `n`: the
odd composite `n` for which one of them fails have natural density `0`.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 3 (`integers-2024-A23-cor-3`). -/
public theorem_wanted hasDensity_zero_strongPseudoprime_bases_conditions_fail :
    Set.HasDensity {n : ℕ | 1 < n ∧ ¬n.Prime ∧ Odd n ∧
      ¬((∃ H : Subgroup (ZMod n)ˣ, ∀ u : (ZMod n)ˣ, u ∈ H ↔ IsStrongPseudoprime n (u : ZMod n)) ∧
        {b : ℕ | 1 ≤ b ∧ b < n ∧ IsStrongPseudoprime n b}.ncard ∣
          {b : ℕ | 1 ≤ b ∧ b < n ∧ Nat.FermatPsp n b}.ncard ∧
        (sInf ((fun p => (p - 1).factorization 2) '' (n.primeFactors : Set ℕ)) = 1 ∨
          n.primeFactors.card = 1) ∧
        ((∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3) ∨ IsPrimePow n))} 0

/-- Let `b > 1` and `m > 2`. The primitive part of `b ^ m - 1` is `Φ_m(b)` and that of
`b ^ m + 1` is `Φ_{2m}(b)`; removing the intrinsic factor (the prime dividing both the
primitive part and `m`, if any) means dividing by its gcd with `m`. Every composite divisor
of the result is a strong pseudoprime to base `b`.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 5 (`integers-2024-A23-thm-5`). -/
public theorem_wanted isStrongPseudoprime_of_dvd_primitivePart {b m c : ℕ} (hb : 1 < b)
    (hm : 2 < m) (hc : 1 < c) (hcomp : ¬c.Prime) :
    let Φ : ℕ → ℤ := fun j => (Polynomial.cyclotomic j ℤ).eval (b : ℤ)
    ((c : ℤ) ∣ Φ m / (Int.gcd (Φ m) m : ℤ) ∨ (c : ℤ) ∣ Φ (2 * m) / (Int.gcd (Φ (2 * m)) m : ℤ)) →
      IsStrongPseudoprime c b

/-- In the setting of Theorem 5, every composite divisor `c` of the primitive part of
`b ^ m ∓ 1` with the intrinsic factor removed is a strong pseudoprime to every integer power
`b ^ t` (`t < 0` allowed, `b` being a unit modulo `c`).

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 4 (`integers-2024-A23-cor-4`). -/
public theorem_wanted isStrongPseudoprime_zpow_of_dvd_primitivePart {b m c : ℕ} (hb : 1 < b)
    (hm : 2 < m) (hc : 1 < c) (hcomp : ¬c.Prime) :
    let Φ : ℕ → ℤ := fun j => (Polynomial.cyclotomic j ℤ).eval (b : ℤ)
    ((c : ℤ) ∣ Φ m / (Int.gcd (Φ m) m : ℤ) ∨ (c : ℤ) ∣ Φ (2 * m) / (Int.gcd (Φ (2 * m)) m : ℤ)) →
      ∀ u : (ZMod c)ˣ, (u : ZMod c) = b → ∀ t : ℤ,
        IsStrongPseudoprime c ((u ^ t : (ZMod c)ˣ) : ZMod c)

/-- If `n` is a strong pseudoprime to base `b`, then it is a strong pseudoprime to every
integer power `b ^ t` and to `-b`. The base is a unit of `ZMod n` (as it must be, since
`b ^ (n - 1) = 1`), so negative exponents make sense.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 6 (`integers-2024-A23-thm-6`). -/
public theorem_wanted isStrongPseudoprime_zpow_and_neg {n : ℕ} {b : (ZMod n)ˣ}
    (h : IsStrongPseudoprime n (b : ZMod n)) (t : ℤ) :
    IsStrongPseudoprime n ((b ^ t : (ZMod n)ˣ) : ZMod n) ∧
      IsStrongPseudoprime n (-(b : ZMod n))

/-- Every composite Fermat number `F_k = 2 ^ (2 ^ k) + 1` is a strong pseudoprime to every
integer power `2 ^ t` of the unit `2`.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Corollary 5 (`integers-2024-A23-cor-5`). -/
public theorem_wanted fermatNumber_isStrongPseudoprime_two_zpow {k : ℕ}
    (hk : ¬(Nat.fermatNumber k).Prime) (u : (ZMod (Nat.fermatNumber k))ˣ)
    (hu : (u : ZMod (Nat.fermatNumber k)) = 2) (t : ℤ) :
    IsStrongPseudoprime (Nat.fermatNumber k) ((u ^ t : (ZMod (Nat.fermatNumber k))ˣ) : ZMod _)

/-- Every composite Fermat number `F_k` is a strong pseudoprime to the bases
`2 ^ (2 ^ (k - 1) + t) ± 2 ^ t` for every `t ≥ 0`.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 7 (`integers-2024-A23-thm-7`). -/
public theorem_wanted fermatNumber_isStrongPseudoprime_two_pow_add_sub {k : ℕ}
    (hk : ¬(Nat.fermatNumber k).Prime) (t : ℕ) :
    IsStrongPseudoprime (Nat.fermatNumber k) (2 ^ (2 ^ (k - 1) + t) + 2 ^ t) ∧
      IsStrongPseudoprime (Nat.fermatNumber k) (2 ^ (2 ^ (k - 1) + t) - 2 ^ t)

/-- For a composite Fermat number `F_k`, the set `S_k` of the bases of Corollary 5 (the
powers of `2`) and Theorem 7 (`2 ^ (2 ^ (k - 1) + t) ± 2 ^ t`, `t ≥ 0`) is the underlying set
of a subgroup of `(ZMod F_k)ˣ` of order `2 ^ (k + 2)`, and every element of `S_k` is a strong
pseudoprime base for `F_k`. Powers `2 ^ t` with `t ∈ ℤ` and `t ∈ ℕ` give the same residues
since `2` has finite order modulo `F_k`. The paper's further claim that this subgroup is
isomorphic to `C_(2 ^ (k + 1)) × C_2` is omitted because it is false: `x = 2 ^ 16 + 1` has
multiplicative order `128 = 2 ^ (k + 2)` modulo `F_5`, so `S_5` is cyclic.

Source: Samuel S. Wagstaff, Jr., *Pseudoprimes and Fermat Numbers*, INTEGERS 24 (2024),
Article A23, Theorem 8 (`integers-2024-A23-thm-8`). -/
public theorem_wanted fermatNumber_strongPseudoprime_bases_subgroup {k : ℕ}
    (hk : ¬(Nat.fermatNumber k).Prime) :
    let S : Set (ZMod (Nat.fermatNumber k)) :=
      {x | (∃ t : ℕ, x = 2 ^ t) ∨
        ∃ t : ℕ, x = 2 ^ (2 ^ (k - 1) + t) + 2 ^ t ∨ x = 2 ^ (2 ^ (k - 1) + t) - 2 ^ t}
    ∃ H : Subgroup (ZMod (Nat.fermatNumber k))ˣ,
      (∀ u : (ZMod (Nat.fermatNumber k))ˣ, u ∈ H ↔ (u : ZMod (Nat.fermatNumber k)) ∈ S) ∧
      Nat.card H = 2 ^ (k + 2) ∧
      ∀ x ∈ S, IsStrongPseudoprime (Nat.fermatNumber k) x

end

end MetaMathlibExt
