/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Zero-sum constants related to the Jacobi symbol: wishlist

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7
(arXiv:2111.14477).

Definitions follow the paper. For a weight-set `A ⊆ ℤ_n`, a sequence `(x_1, …, x_k)` in
`ℤ_n` is an `A`-weighted zero-sum sequence if `a_1 x_1 + ⋯ + a_k x_k = 0` for some
`a_i ∈ A`. The weighted Davenport constant `D_A(n)` is the least positive integer `k`
such that every sequence of length `k` in `ℤ_n` has an `A`-weighted zero-sum
(nonempty) subsequence; `C_A(n)` is the same with a subsequence of consecutive terms.
Both are stated with `IsLeast` on the corresponding set (local notation below), so no
new definition is introduced. `U(n)` is the unit group, `U(n)²` its squares,
`S(n) = {x ∈ U(n) : (x/n) = 1}` and `L(n;p) = {x ∈ U(n) : (x/n) = (x/p)}` with the
Jacobi symbol `jacobiSym`; `f_{n,m}` is `ZMod.castHom`. The paper assumes `n` odd from
Section 2 on (the Jacobi symbol is defined for odd `n`); this is a hypothesis wherever
`S(n)` or `L(n;p)` appears and is not already implied. `Ω` is
`ArithmeticFunction.cardFactors`.
-/

open scoped ArithmeticFunction.Omega

namespace MetaMathlibExt

@[expose] public section

set_option quotPrecheck false in
/-- The set of positive `k` such that every length-`k` sequence in `ℤ_n` has an
`A`-weighted zero-sum subsequence; `D_A(n)` is its least element. -/
local notation "davenportSet" n:max A:max => {k : ℕ | 0 < k ∧ ∀ x : Fin k → ZMod n,
  ∃ I : Finset (Fin k), I.Nonempty ∧
    ∃ a : Fin k → ZMod n, (∀ i ∈ I, a i ∈ A) ∧ ∑ i ∈ I, a i * x i = 0}

set_option quotPrecheck false in
/-- The set of positive `k` such that every length-`k` sequence in `ℤ_n` has an
`A`-weighted zero-sum subsequence of consecutive terms; `C_A(n)` is its least element. -/
local notation "consecutiveSet" n:max A:max => {k : ℕ | 0 < k ∧ ∀ x : Fin k → ZMod n,
  ∃ s t : Fin k, s ≤ t ∧
    ∃ a : Fin k → ZMod n, (∀ i ∈ Finset.Icc s t, a i ∈ A) ∧
      ∑ i ∈ Finset.Icc s t, a i * x i = 0}

set_option quotPrecheck false in
/-- `x : Fin k → ZMod n` is an `A`-weighted zero-sum sequence. -/
local notation "IsWeightedZeroSum" n:max k:max A:max x:max =>
  ∃ a : Fin k → ZMod n, (∀ i, a i ∈ A) ∧ ∑ i, a i * x i = 0

set_option quotPrecheck false in
/-- `U(n)`, the units of `ℤ_n`. -/
local notation "unitSet" n:max => {x : ZMod n | IsUnit x}

set_option quotPrecheck false in
/-- `U(n)²`, the squares of units of `ℤ_n`. -/
local notation "unitSqSet" n:max => {x : ZMod n | ∃ y : ZMod n, IsUnit y ∧ y ^ 2 = x}

set_option quotPrecheck false in
/-- `S(n) = {x ∈ U(n) : (x/n) = 1}`. -/
local notation "jacobiOneSet" n:max =>
  {x : ZMod n | IsUnit x ∧ jacobiSym ((x.val : ℕ) : ℤ) n = 1}

set_option quotPrecheck false in
/-- `L(n;p) = {x ∈ U(n) : (x/n) = (x/p)}`. -/
local notation "jacobiEqSet" n:max p:max =>
  {x : ZMod n | IsUnit x ∧ jacobiSym ((x.val : ℕ) : ℤ) n = jacobiSym ((x.val : ℕ) : ℤ) p}

/-- For every positive integer `n`, `D_{U(n)}(n) = Ω(n) + 1` and `C_{U(n)}(n) = 2^{Ω(n)}`,
with `Ω(n)` the number of prime factors counted with multiplicity.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 4
(`jis-2024-24.1.7-thm-4`). -/
public theorem_wanted unit_weighted_zero_sum_constants (n : ℕ) (hn : 0 < n) :
    IsLeast (davenportSet n (unitSet n)) (Ω n + 1) ∧
      IsLeast (consecutiveSet n (unitSet n)) (2 ^ Ω n)

/-- For an odd prime `p` and `Q_p = U(p)²`, `C_{Q_p}(p) = D_{Q_p}(p) = 3`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 5
(`jis-2024-24.1.7-thm-5`). -/
public theorem_wanted quadratic_residue_weighted_zero_sum_constants (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    IsLeast (consecutiveSet p (unitSqSet p)) 3 ∧ IsLeast (davenportSet p (unitSqSet p)) 3

/-- If `n = mq`, `f_{n,m}(A) ⊆ B` and `f_{n,q}(A) ⊆ C`, then `C_A(n) ≥ C_B(m) C_C(q)`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 8
(`jis-2024-24.1.7-lem-8`). -/
public theorem_wanted consecutive_constant_mul_le (m q : ℕ) (A : Set (ZMod (m * q)))
    (B : Set (ZMod m)) (C : Set (ZMod q))
    (hB : ZMod.castHom (dvd_mul_right m q) (ZMod m) '' A ⊆ B)
    (hC : ZMod.castHom (dvd_mul_left q m) (ZMod q) '' A ⊆ C) (cA cB cC : ℕ)
    (hA : IsLeast (consecutiveSet (m * q) A) cA) (hBc : IsLeast (consecutiveSet m B) cB)
    (hCc : IsLeast (consecutiveSet q C) cC) :
    cB * cC ≤ cA

/-- If `n = mq`, `f_{n,m}(A) ⊆ B` and `f_{n,q}(A) ⊆ C`, then
`D_A(n) ≥ D_B(m) + D_C(q) - 1`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 9
(`jis-2024-24.1.7-lem-9`). -/
public theorem_wanted davenport_constant_add_le (m q : ℕ) (A : Set (ZMod (m * q)))
    (B : Set (ZMod m)) (C : Set (ZMod q))
    (hB : ZMod.castHom (dvd_mul_right m q) (ZMod m) '' A ⊆ B)
    (hC : ZMod.castHom (dvd_mul_left q m) (ZMod q) '' A ⊆ C) (dA dB dC : ℕ)
    (hA : IsLeast (davenportSet (m * q) A) dA) (hBd : IsLeast (davenportSet m B) dB)
    (hCd : IsLeast (davenportSet q C) dC) :
    dB + dC - 1 ≤ dA

/-- For odd `n`, `S(n)` is a subgroup of index two in `U(n)` when `n` is not a square,
and `S(n) = U(n)` when `n` is a square.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7,
Proposition 11 (`jis-2024-24.1.7-prop-11`). -/
public theorem_wanted jacobi_kernel_index_two (n : ℕ) (hn : Odd n) :
    (¬ IsSquare n → ∃ H : Subgroup (ZMod n)ˣ,
      (∀ u : (ZMod n)ˣ, u ∈ H ↔ jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n = 1) ∧
        H.index = 2) ∧
    (IsSquare n → ∀ u : (ZMod n)ˣ, jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n = 1)

/-- For odd `n = d n'` with `d` not a square and coprime to `n'`,
`U(n') ⊆ f_{n,n'}(S(n))`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 14
(`jis-2024-24.1.7-lem-14`). -/
public theorem_wanted units_subset_image_jacobi_kernel (d n' : ℕ) (hn : Odd (d * n'))
    (hd : ¬ IsSquare d) (hcop : Nat.Coprime d n') (y : ZMod n') (hy : IsUnit y) :
    ∃ x ∈ jacobiOneSet (d * n'), ZMod.castHom (dvd_mul_left n' d) (ZMod n') x = y

/-- Let `n = d n'` with `d` coprime to `n'`, `S` a sequence in `ℤ_n` all of whose terms are
divisible by `d`, and `A' ⊆ f_{n,n'}(A)`. If the image of `S` in `ℤ_{n'}` is an
`A'`-weighted zero-sum sequence, then `S` is an `A`-weighted zero-sum sequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 15
(`jis-2024-24.1.7-lem-15`). -/
public theorem_wanted weighted_zero_sum_of_image (d n' k : ℕ) (hcop : Nat.Coprime d n')
    (x : Fin k → ZMod (d * n')) (hx : ∀ i, (d : ZMod (d * n')) ∣ x i)
    (A : Set (ZMod (d * n'))) (A' : Set (ZMod n'))
    (hA : A' ⊆ ZMod.castHom (dvd_mul_left n' d) (ZMod n') '' A)
    (h : IsWeightedZeroSum n' k A' (fun i => ZMod.castHom (dvd_mul_left n' d) (ZMod n') (x i))) :
    IsWeightedZeroSum (d * n') k A x

/-- For an odd prime `p`, a sequence in `ℤ_{p^r}` with at least two terms coprime to `p`
is a `U(p^r)`-weighted zero-sum sequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 16
(`jis-2024-24.1.7-lem-16`). -/
public theorem_wanted unit_weighted_zero_sum_prime_power (p r k : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (x : Fin k → ZMod (p ^ r))
    (h : 2 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card) :
    IsWeightedZeroSum (p ^ r) k (unitSet (p ^ r)) x

/-- For `n = p^r` with `p ≥ 7` prime, `A = U(n)²` and units `x_1, x_2, x_3`,
`A x_1 + A x_2 + A x_3 = ℤ_n`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 17
(`jis-2024-24.1.7-lem-17`). -/
public theorem_wanted unit_square_three_sumset_eq_univ (p r : ℕ) (hp : p.Prime) (h7 : 7 ≤ p)
    (x : Fin 3 → ZMod (p ^ r)) (hx : ∀ i, IsUnit (x i)) (z : ZMod (p ^ r)) :
    ∃ a : Fin 3 → ZMod (p ^ r), (∀ i, a i ∈ unitSqSet (p ^ r)) ∧ ∑ i, a i * x i = z

/-- For `n = p^r` with `p ≥ 7` prime, `A_1 = U(n)²`, `A_2 = U(n) \ U(n)²`, units
`x_1, x_2, x_3` and any `f : {1,2,3} → {1,2}`, `A_{f(1)} x_1 + A_{f(2)} x_2 + A_{f(3)} x_3 = ℤ_n`.
Here `f i = true` selects `A_1` and `f i = false` selects `A_2`. The exponent is
`r ≥ 1`: for `r = 0`, `ℤ_1 = {0}` has `0 = 0²` as its only unit, so `A_2` is empty.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 18
(`jis-2024-24.1.7-lem-18`). -/
public theorem_wanted unit_square_class_three_sumset_eq_univ (p r : ℕ) (hp : p.Prime)
    (h7 : 7 ≤ p) (hr : 0 < r) (x : Fin 3 → ZMod (p ^ r)) (hx : ∀ i, IsUnit (x i))
    (f : Fin 3 → Bool) (z : ZMod (p ^ r)) :
    ∃ a : Fin 3 → ZMod (p ^ r),
      (∀ i, IsUnit (a i) ∧ (a i ∈ unitSqSet (p ^ r) ↔ f i = true)) ∧ ∑ i, a i * x i = z

open Classical in
/-- For `n = p^r` with `p ≥ 7` prime, a sequence in `ℤ_n` with at least three unit terms is
a `U(n)²`-weighted zero-sum sequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7,
Corollary 19 (`jis-2024-24.1.7-cor-19`). -/
public theorem_wanted unit_square_weighted_zero_sum_prime_power (p r k : ℕ) (hp : p.Prime)
    (h7 : 7 ≤ p) (x : Fin k → ZMod (p ^ r))
    (h : 3 ≤ (Finset.univ.filter fun i => IsUnit (x i)).card) :
    IsWeightedZeroSum (p ^ r) k (unitSqSet (p ^ r)) x

open Classical in
/-- For odd squarefree `n`, a sequence in `ℤ_n` with at least two terms coprime to each
prime divisor of `n` and at most one unit term is an `S(n)`-weighted zero-sum sequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 21
(`jis-2024-24.1.7-lem-21`). -/
public theorem_wanted jacobi_weighted_zero_sum_of_few_units (n k : ℕ) (hn : Odd n)
    (hsf : Squarefree n) (x : Fin k → ZMod n)
    (h2 : ∀ p ∈ n.primeFactors, 2 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card)
    (h1 : (Finset.univ.filter fun i => IsUnit (x i)).card ≤ 1) :
    IsWeightedZeroSum n k (jacobiOneSet n) x

/-- For squarefree `n` with every prime divisor at least seven, a sequence in `ℤ_n` with
at least two terms coprime to each prime divisor, and at least three terms coprime to
some prime divisor, is an `S(n)`-weighted zero-sum sequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 22
(`jis-2024-24.1.7-lem-22`). -/
public theorem_wanted jacobi_weighted_zero_sum_of_three_coprime (n k : ℕ) (hsf : Squarefree n)
    (h7 : ∀ p ∈ n.primeFactors, 7 ≤ p) (x : Fin k → ZMod n)
    (h2 : ∀ p ∈ n.primeFactors, 2 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card)
    (h3 : ∃ p ∈ n.primeFactors, 3 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card) :
    IsWeightedZeroSum n k (jacobiOneSet n) x

/-- For odd squarefree `n`: if `n` is prime then `D_{S(n)}(n) = 3`; if `n` is not prime and
every prime divisor of `n` is at least seven then `D_{S(n)}(n) = Ω(n) + 1`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 23
(`jis-2024-24.1.7-thm-23`). -/
public theorem_wanted jacobi_davenport_constant (n : ℕ) (hn : Odd n) (hsf : Squarefree n) :
    (n.Prime → IsLeast (davenportSet n (jacobiOneSet n)) 3) ∧
    (¬ n.Prime → (∀ p ∈ n.primeFactors, 7 ≤ p) →
      IsLeast (davenportSet n (jacobiOneSet n)) (Ω n + 1))

/-- For odd squarefree `n`: if `n` is prime then `C_{S(n)}(n) = 3`; if `n` is not prime and
every prime divisor of `n` is at least seven then `C_{S(n)}(n) = 2^{Ω(n)}`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 24
(`jis-2024-24.1.7-thm-24`). -/
public theorem_wanted jacobi_consecutive_constant (n : ℕ) (hn : Odd n) (hsf : Squarefree n) :
    (n.Prime → IsLeast (consecutiveSet n (jacobiOneSet n)) 3) ∧
    (¬ n.Prime → (∀ p ∈ n.primeFactors, 7 ≤ p) →
      IsLeast (consecutiveSet n (jacobiOneSet n)) (2 ^ Ω n))

/-- For odd `n` and a prime divisor `p` of `n`, `L(n;p)` is a subgroup of index two in
`U(n)` unless `p` is the unique prime divisor of `n` with odd `p`-adic valuation.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7,
Proposition 26 (`jis-2024-24.1.7-prop-26`). -/
public theorem_wanted jacobi_eq_legendre_index_two (n p : ℕ) (hn : Odd n) (hp : p.Prime)
    (hpn : p ∣ n)
    (hnot : ¬ (Odd (n.factorization p) ∧
      ∀ q ∈ n.primeFactors, Odd (n.factorization q) → q = p)) :
    ∃ H : Subgroup (ZMod n)ˣ,
      (∀ u : (ZMod n)ˣ, u ∈ H ↔
        jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n = jacobiSym (((u : ZMod n).val : ℕ) : ℤ) p) ∧
      H.index = 2

/-- For odd `n`, prime divisors `p`, `p'` of `n` with `p` coprime to `n' = n/p`,
`S(n') ⊆ f_{n,n'}(L(n;p'))`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 28
(`jis-2024-24.1.7-lem-28`). -/
public theorem_wanted jacobi_kernel_subset_image_jacobi_eq_legendre (n p p' : ℕ) (hn : Odd n)
    (hp : p.Prime) (hp' : p'.Prime) (hpn : p ∣ n) (hp'n : p' ∣ n)
    (hcop : Nat.Coprime p (n / p)) (y : ZMod (n / p)) (hy : y ∈ jacobiOneSet (n / p)) :
    ∃ x ∈ jacobiEqSet n p', ZMod.castHom (Nat.div_dvd_of_dvd hpn) (ZMod (n / p)) x = y

/-- For odd `n` and a prime divisor `p'` of `n` coprime to `n/p'`,
`U(p') ⊆ f_{n,p'}(L(n;p'))`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 29
(`jis-2024-24.1.7-lem-29`). -/
public theorem_wanted units_prime_subset_image_jacobi_eq_legendre (n p' : ℕ) (hn : Odd n)
    (hp' : p'.Prime) (hp'n : p' ∣ n) (hcop : Nat.Coprime p' (n / p')) (z : ZMod p')
    (hz : IsUnit z) :
    ∃ x ∈ jacobiEqSet n p', ZMod.castHom hp'n (ZMod p') x = z

/-- For odd squarefree `n`, a prime divisor `p'` and `n' = n/p'`, the Chinese remainder
isomorphism `ψ = (f_{n,n'}, f_{n,p'}) : U(n) → U(n') × U(p')` satisfies
`S(n') × U(p') ⊆ ψ(L(n;p'))`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 31
(`jis-2024-24.1.7-lem-31`). -/
public theorem_wanted jacobi_kernel_prod_units_subset_crt_image (n p' : ℕ) (hn : Odd n)
    (hsf : Squarefree n) (hp' : p'.Prime) (hp'n : p' ∣ n) (y : ZMod (n / p'))
    (hy : y ∈ jacobiOneSet (n / p')) (z : ZMod p') (hz : IsUnit z) :
    ∃ x ∈ jacobiEqSet n p', ZMod.castHom (Nat.div_dvd_of_dvd hp'n) (ZMod (n / p')) x = y ∧
      ZMod.castHom hp'n (ZMod p') x = z

open Classical in
/-- For squarefree `n` with every prime divisor at least seven, a prime divisor `p'`,
`n' = n/p'`, and a sequence `S` in `ℤ_n` with at least two terms coprime to each prime
divisor of `n`: if the image of `S` in `ℤ_{n'}` has at most one unit term, or some prime
divisor of `n'` is coprime to at least three terms of `S`, then `S` is an
`L(n;p')`-weighted zero-sum sequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Lemma 32
(`jis-2024-24.1.7-lem-32`). -/
public theorem_wanted jacobi_eq_legendre_weighted_zero_sum (n p' k : ℕ) (hsf : Squarefree n)
    (h7 : ∀ p ∈ n.primeFactors, 7 ≤ p) (hp' : p' ∈ n.primeFactors) (x : Fin k → ZMod n)
    (h2 : ∀ p ∈ n.primeFactors, 2 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card)
    (hcase : (Finset.univ.filter fun i =>
        IsUnit (ZMod.castHom (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp'))
          (ZMod (n / p')) (x i))).card ≤ 1 ∨
      ∃ p ∈ (n / p').primeFactors,
        3 ≤ (Finset.univ.filter fun i => Nat.Coprime (x i).val p).card) :
    IsWeightedZeroSum n k (jacobiEqSet n p') x

/-- For squarefree `n` with every prime divisor at least seven, `Ω(n) ≠ 2`, and a prime
divisor `p'` of `n`, `D_{L(n;p')}(n) = Ω(n) + 1`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 33
(`jis-2024-24.1.7-thm-33`). -/
public theorem_wanted jacobi_eq_legendre_davenport_constant (n p' : ℕ) (hsf : Squarefree n)
    (h7 : ∀ p ∈ n.primeFactors, 7 ≤ p) (hΩ : Ω n ≠ 2) (hp' : p' ∈ n.primeFactors) :
    IsLeast (davenportSet n (jacobiEqSet n p')) (Ω n + 1)

/-- For distinct primes `p', q ≥ 7` and `n = p'q`, `D_{L(n;p')}(n) = 4`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 34
(`jis-2024-24.1.7-thm-34`). -/
public theorem_wanted jacobi_eq_legendre_davenport_constant_two_primes (p' q : ℕ)
    (hp' : p'.Prime) (hq : q.Prime) (hne : p' ≠ q) (h7p : 7 ≤ p') (h7q : 7 ≤ q) :
    IsLeast (davenportSet (p' * q) (jacobiEqSet (p' * q) p')) 4

/-- For squarefree `n` with every prime divisor at least seven, `Ω(n) ≠ 2`, and a prime
divisor `p'` of `n`, `C_{L(n;p')}(n) = 2^{Ω(n)}`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 35
(`jis-2024-24.1.7-thm-35`). -/
public theorem_wanted jacobi_eq_legendre_consecutive_constant (n p' : ℕ) (hsf : Squarefree n)
    (h7 : ∀ p ∈ n.primeFactors, 7 ≤ p) (hΩ : Ω n ≠ 2) (hp' : p' ∈ n.primeFactors) :
    IsLeast (consecutiveSet n (jacobiEqSet n p')) (2 ^ Ω n)

/-- For distinct primes `p', q ≥ 7` and `n = p'q`, `C_{L(n;p')}(n) = 6`.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to
the Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Theorem 36
(`jis-2024-24.1.7-thm-36`). -/
public theorem_wanted jacobi_eq_legendre_consecutive_constant_two_primes (p' q : ℕ)
    (hp' : p'.Prime) (hq : q.Prime) (hne : p' ≠ q) (h7p : 7 ≤ p') (h7q : 7 ≤ q) :
    IsLeast (consecutiveSet (p' * q) (jacobiEqSet (p' * q) p')) 6

end

end MetaMathlibExt
