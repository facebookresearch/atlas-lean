/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# On near `F_k`-perfect and deficient `F_k`-perfect numbers

Statements from Flora Jeba S, Anirban Roy, Pankaj Jyoti
Mahanta, and Manjil P. Saikia, "On Near `F_k`-Perfect and
Deficient `F_k`-Perfect Numbers", *INTEGERS* 25 (2025),
Article A86
(<https://math.colgate.edu/~integers/z86/z86.pdf>).

With `σₖ(n) = ∑_{d ∣ n} d^k`, the paper calls `n`
`[k,ℓ]`-deficient-perfect if `σₖ(n) - n^k + d^k = ℓn` for
some proper divisor `d` of `n`, and `[k,ℓ]`-near-perfect if
`σₖ(n) - n^k - d^k = ℓn`; deficient/near `F_k`-perfect is
the case `ℓ = 3` (with `k > 1`), and `F`-perfect variants
are `k = 2`, `ℓ = 3`. Below these are
`IsKLDeficientPerfect`/`IsKLNearPerfect` and the `With`
variants fixing the divisor `d` (written additively to stay
in `ℕ`). The paper's `ℓ` is a positive natural (its
Proposition 2 proof needs `ℓ ≥ 1`: at `ℓ = 0` every prime
would be `[k,0]`-near-perfect with `d = 1`), so
`[k,ℓ]`-statements carry `1 ≤ l` where the printed form
needs it. Two printed statements need corrections found by brute
force: Theorem 3 omits the exception `p^a = 2` (which is
`[2,1]`-deficient-perfect, cf. Corollary 1), and Theorem
4's conclusion `a = k` is false in general (the correct
range is `2 ≤ a ≤ k`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Divisors

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FkPerfectWanted

/-- The paper's deficient equation with a specified proper
divisor `d`: `σₖ(n) + d^k = n^k + ℓn`. -/
def KLDeficientPerfectWith (k l n d : ℕ) : Prop :=
  d ∣ n ∧ d < n ∧
    (∑ e ∈ n.divisors, e ^ k) + d ^ k = n ^ k + l * n

/-- The paper's `[k,ℓ]`-deficient-perfect numbers. -/
def IsKLDeficientPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLDeficientPerfectWith k l n d

/-- The paper's near equation with a specified proper
divisor `d`: `σₖ(n) = n^k + d^k + ℓn`. -/
def KLNearPerfectWith (k l n d : ℕ) : Prop :=
  d ∣ n ∧ d < n ∧
    (∑ e ∈ n.divisors, e ^ k) = n ^ k + d ^ k + l * n

/-- The paper's `[k,ℓ]`-near-perfect numbers. -/
def IsKLNearPerfect (k l n : ℕ) : Prop :=
  ∃ d, KLNearPerfectWith k l n d

/-- The paper's deficient `F_k`-perfect numbers (`ℓ = 3`). -/
def IsDeficientFkPerfect (k n : ℕ) : Prop :=
  IsKLDeficientPerfect k 3 n

/-- The paper's near `F_k`-perfect numbers (`ℓ = 3`). -/
def IsNearFkPerfect (k n : ℕ) : Prop :=
  IsKLNearPerfect k 3 n

/-- The paper's deficient `F`-perfect numbers (`k = 2`,
`ℓ = 3`). -/
def IsDeficientFPerfect (n : ℕ) : Prop :=
  IsKLDeficientPerfect 2 3 n

/-- The paper's near `F`-perfect numbers (`k = 2`,
`ℓ = 3`). -/
def IsNearFPerfect (n : ℕ) : Prop :=
  IsKLNearPerfect 2 3 n

/-- **Proposition 1**: an odd prime is not
`[k,ℓ]`-deficient-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Proposition 1. -/
theorem_wanted not_isKLDeficientPerfect_of_prime_odd
    (k l p : ℕ) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsKLDeficientPerfect k l p

/-- **Corollary 1**: `2` is `[k,1]`-deficient-perfect for
every `k` (with `d = 1`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Corollary 1. -/
theorem_wanted isKLDeficientPerfect_two (k : ℕ) :
    IsKLDeficientPerfect k 1 2

/-- **Corollary 2**: no prime is deficient `F`-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Corollary 2. -/
theorem_wanted not_isDeficientFPerfect_of_prime (p : ℕ)
    (hp : p.Prime) :
    ¬ IsDeficientFPerfect p

/-- **Proposition 2**: a prime is not
`[k,ℓ]`-near-perfect (for `ℓ ≥ 1`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Proposition 2. -/
theorem_wanted not_isKLNearPerfect_of_prime (k l p : ℕ)
    (hl : 1 ≤ l) (hp : p.Prime) :
    ¬ IsKLNearPerfect k l p

/-- **Theorem 1**: no prime power `p^a` is deficient
`F`-perfect or near `F`-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 1. -/
theorem_wanted prime_pow_not_fPerfect (p a : ℕ)
    (hp : p.Prime) :
    ¬ IsDeficientFPerfect (p ^ a) ∧ ¬ IsNearFPerfect (p ^ a)

/-- **Theorem 2**: `p^a` is `[2,ℓ]`-near-perfect with
divisor `d` if and only if `a = 2`, `ℓ = 1`, and `d = 1`
(for `ℓ ≥ 1`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 2. -/
theorem_wanted klNearPerfectWith_prime_pow_two_iff
    (p a l d : ℕ) (hp : p.Prime) (hl : 1 ≤ l) :
    KLNearPerfectWith 2 l (p ^ a) d ↔
      a = 2 ∧ l = 1 ∧ d = 1

/-- **Theorem 3** (corrected): if `p^a` is
`[2,ℓ]`-deficient-perfect then `ℓ = 1` and (`a = 2` or
`p^a = 2`); the printed exception `a = 2`, `ℓ = 1` omits
the solution `p = 2`, `a = 1`, `ℓ = 1`, `d = 1` (the
number `2` of Corollary 1).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 3. -/
theorem_wanted isKLDeficientPerfect_prime_pow_two_imp
    (p a l : ℕ) (hp : p.Prime) :
    IsKLDeficientPerfect 2 l (p ^ a) →
      l = 1 ∧ (a = 2 ∨ (p = 2 ∧ a = 1))

/-- **Theorem 4** (corrected): `p^a` is
`[k,ℓ]`-near-perfect with divisor `d` if and only if
`2 ≤ a ≤ k`, `d = 1`, and
`ℓ = p^{k-a} (1 + p^k + ⋯ + p^{(a-2)k})` (for `k, ℓ ≥ 1`).
The printed conclusion `a = k` is false: at `p = 2`,
`a = 2`, `k = 3`, `ℓ = 2`, `d = 1` one has
`σ₃(4) = 73 = 4³ + 1³ + 2·4` with `a ≠ k`; the printed
form is the case `a = k` of the identity
`∑_{i=1}^{a-1} p^{ik} = ℓ p^a`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 4. -/
theorem_wanted klNearPerfectWith_prime_pow_iff
    (p a k l d : ℕ) (hp : p.Prime) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    KLNearPerfectWith k l (p ^ a) d ↔
      2 ≤ a ∧ a ≤ k ∧ d = 1 ∧
        l = p ^ (k - a) *
          ∑ i ∈ Finset.range (a - 1), p ^ (i * k)

/-- **Theorem 5**, `k ≥ 2` part: if `p^a` is
`[k,ℓ]`-deficient-perfect with `k ≥ 2`, then `p = 2` and
`a = 1`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 5. -/
theorem_wanted isKLDeficientPerfect_prime_pow_imp
    (p a k l : ℕ) (hp : p.Prime) (hk : 2 ≤ k) :
    IsKLDeficientPerfect k l (p ^ a) → p = 2 ∧ a = 1

/-- **Theorem 5**, `k = 1` part: `p^a` is
`[1,ℓ]`-deficient-perfect with divisor `d` if and only if
`p = 2`, `ℓ = 1`, `d = 1` (and `a ≥ 1`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 5. -/
theorem_wanted klDeficientPerfectWith_one_prime_pow_iff
    (p a l d : ℕ) (hp : p.Prime) :
    KLDeficientPerfectWith 1 l (p ^ a) d ↔
      p = 2 ∧ l = 1 ∧ d = 1 ∧ 1 ≤ a

/-- **Theorem 6**: `2p` is not `[k,ℓ]`-near-perfect for an
odd prime `p` (and `ℓ ≥ 1`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 6. -/
theorem_wanted not_isKLNearPerfect_two_mul_prime (k l p : ℕ)
    (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsKLNearPerfect k l (2 * p)

/-- **Theorem 7**: the only deficient `F`-perfect number
of the form `2^a p` has `p = 3` and `a = 1` (the number
`6`, which is deficient `F`-perfect with `d = 2`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 7. -/
theorem_wanted isDeficientFPerfect_two_pow_mul_prime_imp
    (p a : ℕ) (hp : p.Prime) :
    IsDeficientFPerfect (2 ^ a * p) → p = 3 ∧ a = 1

/-- **Theorem 8**: `2^a p` (`p` an odd prime) is not
`[k,ℓ]`-deficient-perfect with divisor `d = 1` or `d = p`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 8. -/
theorem_wanted not_klDeficientPerfectWith_two_pow_mul
    (k l p a : ℕ) (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) :
    ¬ KLDeficientPerfectWith k l (2 ^ a * p) 1 ∧
      ¬ KLDeficientPerfectWith k l (2 ^ a * p) p

/-- **Theorem 9**: there is no near `F`-perfect number of
the form `2^a p`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 9. -/
theorem_wanted not_isNearFPerfect_two_pow_mul_prime
    (p a : ℕ) (hp : p.Prime) :
    ¬ IsNearFPerfect (2 ^ a * p)

/-- **Theorem 10**: `2^a p` (`p` an odd prime) is not
`[2,ℓ]`-near-perfect.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 10. -/
theorem_wanted not_isKLNearPerfect_two_two_pow_mul
    (l p a : ℕ) (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsKLNearPerfect 2 l (2 ^ a * p)

/-- **Theorem 11**: for `a > 1` and an odd prime `p`,
`2^a p` is not `[k,ℓ]`-near-perfect with divisor `d = 1`
or `d = p`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 11. -/
theorem_wanted not_klNearPerfectWith_two_pow_mul
    (k l p a : ℕ) (hl : 1 ≤ l) (hp : p.Prime) (hpo : Odd p)
    (ha : 1 < a) :
    ¬ KLNearPerfectWith k l (2 ^ a * p) 1 ∧
      ¬ KLNearPerfectWith k l (2 ^ a * p) p

/-- **Theorem 12**: the only deficient `F`-perfect number
of the form `2p^a` is `6` (and `6` is one, with `d = 2`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 12. -/
theorem_wanted isDeficientFPerfect_two_mul_prime_pow
    (p a : ℕ) (hp : p.Prime) :
    IsDeficientFPerfect 6 ∧
      (IsDeficientFPerfect (2 * p ^ a) → 2 * p ^ a = 6)

/-- **Theorem 13**: there is no near `F`-perfect number of
the form `2p^a`.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 13. -/
theorem_wanted not_isNearFPerfect_two_mul_prime_pow
    (p a : ℕ) (hp : p.Prime) :
    ¬ IsNearFPerfect (2 * p ^ a)

/-- **Theorem 14**, part 1: the only `[1,ℓ]`-near-perfect
number of the form `2p^a` (any `ℓ ≥ 1`) is `18` (and `18`
is one, for `ℓ = 1` with `d = 3`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 14. -/
theorem_wanted isKLNearPerfect_one_two_mul_prime_pow
    (p a l : ℕ) (hp : p.Prime) (hpo : Odd p) (hl : 1 ≤ l) :
    IsKLNearPerfect 1 1 18 ∧
      (IsKLNearPerfect 1 l (2 * p ^ a) → 2 * p ^ a = 18)

/-- **Theorem 14**, part 2: if `2p^a` (`p` an odd prime)
is `[k,ℓ]`-near-perfect with divisor `d` and `k > 1`, then
`p² ∣ 1 + 2^k`, and `a` is even if and only if `d` is odd.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 14. -/
theorem_wanted klNearPerfectWith_two_mul_prime_pow_imp
    (p a k l d : ℕ) (hp : p.Prime) (hpo : Odd p) (hk : 1 < k)
    (hl : 1 ≤ l) :
    KLNearPerfectWith k l (2 * p ^ a) d →
      p ^ 2 ∣ 1 + 2 ^ k ∧ (Even a ↔ Odd d)

/-- **Theorem 15**: there is no near `F`-perfect number
of the form `2^a p^b` with `b` even.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 15. -/
theorem_wanted not_isNearFPerfect_two_pow_mul_prime_pow
    (p a b : ℕ) (hp : p.Prime) (hb : Even b) :
    ¬ IsNearFPerfect (2 ^ a * p ^ b)

/-- **Theorem 16**: there is no deficient `F_k`-perfect
number of the form `p₁^a p₂` for distinct odd primes
`p₁, p₂` (and `k > 1`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 16. -/
theorem_wanted not_isDeficientFkPerfect_prime_pow_mul
    (k p₁ p₂ a : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) :
    ¬ IsDeficientFkPerfect k (p₁ ^ a * p₂)

/-- **Theorem 17**: there is no near `F_k`-perfect number
of the form `p₁^a p₂` for distinct odd primes `p₁, p₂`
(and `k > 1`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 17. -/
theorem_wanted not_isNearFkPerfect_prime_pow_mul
    (k p₁ p₂ a : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) :
    ¬ IsNearFkPerfect k (p₁ ^ a * p₂)

/-- **Theorem 18**: there is no deficient `F_k`-perfect
number of the form `2p^a` when `k > 2` and `p` is an odd
prime.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 18. -/
theorem_wanted not_isDeficientFkPerfect_two_mul_pow
    (k p a : ℕ) (hk : 2 < k) (hp : p.Prime) (hpo : Odd p) :
    ¬ IsDeficientFkPerfect k (2 * p ^ a)

/-- **Theorem 19**: there is no deficient `F_k`-perfect
number of the form `p₁^a p₂^b` (distinct odd primes,
`k > 1`, `a, b ≥ 1`) when `a + b` is odd or both `a` and
`b` are odd.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 19. -/
theorem_wanted not_isDeficientFkPerfect_pow_mul_pow
    (k p₁ p₂ a b : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpar : Odd (a + b) ∨ (Odd a ∧ Odd b)) :
    ¬ IsDeficientFkPerfect k (p₁ ^ a * p₂ ^ b)

/-- **Theorem 20**: there is no near `F_k`-perfect number
of the form `p₁^a p₂^b` (distinct odd primes, `k > 1`,
`a, b ≥ 1`) when `a + b` is odd or both `a` and `b` are
odd.

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 20. -/
theorem_wanted not_isNearFkPerfect_pow_mul_pow
    (k p₁ p₂ a b : ℕ) (hk : 1 < k) (hp₁ : p₁.Prime)
    (hp₂ : p₂.Prime) (ho₁ : Odd p₁) (ho₂ : Odd p₂)
    (hne : p₁ ≠ p₂) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hpar : Odd (a + b) ∨ (Odd a ∧ Odd b)) :
    ¬ IsNearFkPerfect k (p₁ ^ a * p₂ ^ b)

/-- **Theorem 21**: no product of distinct odd primes is
deficient `F_k`-perfect (for `k > 1`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 21. -/
theorem_wanted not_isDeficientFkPerfect_prod_primes
    (k : ℕ) (hk : 1 < k) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Odd p) :
    ¬ IsDeficientFkPerfect k (∏ p ∈ s, p)

/-- **Theorem 22**: no product of distinct odd primes is
near `F_k`-perfect (for `k > 1`).

Source: Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta,
and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient
`F_k`-Perfect Numbers", Theorem 22. -/
theorem_wanted not_isNearFkPerfect_prod_primes
    (k : ℕ) (hk : 1 < k) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Odd p) :
    ¬ IsNearFkPerfect k (∏ p ∈ s, p)

end MathlibExt.NumberTheory.FkPerfectWanted
