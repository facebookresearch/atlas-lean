/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

namespace MetaMathlibExt

@[expose] public section

open Complex Finset

/-- The sum `S_k(n, m) := ∑ a_1 ⋯ a_k` over `k`-tuples `(a_1, …, a_k) ∈ {1, …, n}^k` with every
`a_j` coprime to `n` and `a_1 ⋯ a_k ≡ m (mod n)`. For `k = 2`, `m = 1` this is the sum of the
products `a ā` of the residues coprime to `n` and their modular inverses.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, equation (2). -/
public def modularProductSum (k n m : ℕ) : ℕ :=
  ∑ a ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 n) with
      (∀ j, Nat.Coprime (a j) n) ∧ (∏ j, a j) ≡ m [MOD n],
    ∏ j, a j

/-- Characteristic value: `S_2(3, 1) = 1 · 1 + 2 · 2 = 5`.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, equation (2). -/
public theorem modularProductSum_two_three_one : modularProductSum 2 3 1 = 5 := by
  decide

/-- Characteristic value: `S_1(5, 3) = 3` (the only `a ∈ {1, …, 5}` with `a ≡ 3 (mod 5)`).

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, equation (2). -/
public theorem modularProductSum_one_five_three : modularProductSum 1 5 3 = 3 := by
  decide

/-- The constant `C_q := ∏_{p^α ∥ q} (1 + (2p³ + p² - 1) / ((p² + 1)(p² + p + 1))
- 1 / (p^{3(α-1)} (p² + p + 1)))` of Xu and Zhang.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, equation (4), quoting Z. Xu and W. Zhang, *Fourth
power mean of character sums*, Acta Arith. 135 (2008), Lemma 9. -/
public noncomputable def xuZhangConstant (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors,
    (1 + (2 * (p : ℝ) ^ 3 + (p : ℝ) ^ 2 - 1) / (((p : ℝ) ^ 2 + 1) * ((p : ℝ) ^ 2 + p + 1)) -
      1 / ((p : ℝ) ^ (3 * (q.factorization p - 1)) * ((p : ℝ) ^ 2 + p + 1)))

/-- Characteristic value at a prime `p`:
`C_p = 1 + (2p³ + p² - 1) / ((p² + 1)(p² + p + 1)) - 1 / (p² + p + 1)`.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, equation (4). -/
public theorem xuZhangConstant_prime {p : ℕ} (hp : p.Prime) :
    xuZhangConstant p =
      1 + (2 * (p : ℝ) ^ 3 + (p : ℝ) ^ 2 - 1) / (((p : ℝ) ^ 2 + 1) * ((p : ℝ) ^ 2 + p + 1)) -
        1 / ((p : ℝ) ^ 2 + p + 1) := by
  simp [xuZhangConstant, hp.primeFactors, hp.factorization_self]

/-- Theorem 1: for `k ≥ 3`, `n ≥ 2` and `m` coprime to `n`,
`|S_k(n, m) - 2^{-k} n^k φ(n)^{k-1}| ≤ (2√3)^k n^{3k/2} (log n)^k` (the paper's explicit
`O^*` notation). The paper's `m ≥ 1` follows from `gcd(m, n) = 1` and `n ≥ 2`.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Theorem 1. -/
public theorem_wanted modularProductSum_explicit_estimate {k n m : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n)
    (hmn : Nat.Coprime m n) :
    |(modularProductSum k n m : ℝ) - (n : ℝ) ^ k * (n.totient : ℝ) ^ (k - 1) / 2 ^ k| ≤
      (2 * Real.sqrt 3) ^ k * (n : ℝ) ^ ((3 * k : ℝ) / 2) * Real.log n ^ k

/-- Theorem 2: for fixed `k ≥ 4` there is `C_k` such that for every odd `n ≥ 3` and every `m`
coprime to `n`, `|S_k(n, m) - 2^{-k} n^k φ(n)^{k-1}|
≤ C_k n^{3(k-2)/2} φ(n)³ (log n)^{k-4} (log log n)²`.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Theorem 2. -/
public theorem_wanted modularProductSum_odd_estimate {k : ℕ} (hk : 4 ≤ k) :
    ∃ C : ℝ, ∀ n m : ℕ, 3 ≤ n → Odd n → Nat.Coprime m n →
      |(modularProductSum k n m : ℝ) - (n : ℝ) ^ k * (n.totient : ℝ) ^ (k - 1) / 2 ^ k| ≤
        C * (n : ℝ) ^ ((3 * ((k : ℝ) - 2)) / 2) * (n.totient : ℝ) ^ 3 *
          Real.log n ^ (k - 4) * Real.log (Real.log n) ^ 2

/-- Theorem 3: for `n ≥ 2` and `m` coprime to `n`,
`|S_2(n, m) - n² φ(n) / 4| ≤ n² σ_{1/2}(n) (τ(n) log(e n))² + n φ(n) / 4`, where
`σ_{1/2}(n) = ∑_{d ∣ n} √d` and `τ(n)` is the number of divisors.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Theorem 3. -/
public theorem_wanted modularProductSum_two_explicit_estimate {n m : ℕ} (hn : 2 ≤ n)
    (hmn : Nat.Coprime m n) :
    |(modularProductSum 2 n m : ℝ) - (n : ℝ) ^ 2 * n.totient / 4| ≤
      (n : ℝ) ^ 2 * (∑ d ∈ n.divisors, Real.sqrt d) *
          ((n.divisors.card : ℝ) * Real.log (Real.exp 1 * n)) ^ 2 +
        n * n.totient / 4

/-- Theorem 4, mean square: for every `ε > 0` there is `C` such that for every odd `n ≥ 3`,
`|∑_{1 ≤ m ≤ n, (m, n) = 1} (S_2(n, m) - n² φ(n) / 4)² - (5 C_n / 144) (n φ(n))³|
≤ C n^{5 + ε}`, with `C_n` the Xu-Zhang constant of equation (4).

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Theorem 4. -/
public theorem_wanted modularProductSum_two_mean_square {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → Odd n →
      |(∑ m ∈ Icc 1 n with Nat.Coprime m n,
            ((modularProductSum 2 n m : ℝ) - (n : ℝ) ^ 2 * n.totient / 4) ^ 2) -
          5 * xuZhangConstant n / 144 * ((n : ℝ) * n.totient) ^ 3| ≤
        C * (n : ℝ) ^ (5 + ε)

/-- Theorem 4, consequence: there are `c > 0` and `N` such that every odd `n ≥ N` admits
`m ∈ {1, …, n}` coprime to `n` with `|S_2(n, m) - n² φ(n) / 4| ≥ c n^{3/2} φ(n)`.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Theorem 4. -/
public theorem_wanted modularProductSum_two_error_large :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Odd n →
      ∃ m ∈ Icc 1 n, Nat.Coprime m n ∧
        c * (n : ℝ) ^ ((3 : ℝ) / 2) * n.totient ≤
          |(modularProductSum 2 n m : ℝ) - (n : ℝ) ^ 2 * n.totient / 4|

open Classical in
/-- Lemma 1 (Xu and Zhang): for every `ℓ ≥ 0` and `ε > 0` there is `C` such that for every odd
`q ≥ 3`,
`∑_{χ mod q, χ(-1) = -1} χ̄(2^ℓ) |∑_{a=1}^q a χ(a)|⁴ = C_q (3ℓ + 5) q³ φ(q)⁴ / (72 · 2^{ℓ+1}) + O(q^{6+ε})`,
the error bounded by `C q^{6+ε}` (implied constant depending on `ℓ` and `ε`).

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 1 (`integers-2024-A33-lem-1`, journal PDF
p. 4), quoting Z. Xu and W. Zhang, *Fourth power mean of character sums*, Acta Arith. 135
(2008), Lemma 9. -/
public theorem_wanted odd_character_twisted_weighted_sum_fourth_moment (ℓ : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ q : ℕ, 3 ≤ q → Odd q →
      ‖∑ χ : DirichletCharacter ℂ q with χ.Odd,
          starRingEnd ℂ (χ (2 ^ ℓ)) * (‖∑ a ∈ Icc 1 q, (a : ℂ) * χ a‖ ^ 4 : ℝ) -
        (xuZhangConstant q * (3 * ℓ + 5) * (q : ℝ) ^ 3 * (q.totient : ℝ) ^ 4 /
          (72 * 2 ^ (ℓ + 1)) : ℝ)‖ ≤ C * (q : ℝ) ^ (6 + ε)

open Classical in
/-- Corollary 1: there is `C` such that for every odd `n ≥ 3`,
`∑_{χ mod n, χ(-1) = -1} |∑_{a=1}^n a χ(a)|⁴ ≤ C n³ φ(n)⁴ (log log n)²`.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Corollary 1. -/
public theorem_wanted odd_character_weighted_sum_fourth_moment :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → Odd n →
      ∑ χ : DirichletCharacter ℂ n with χ.Odd, ‖∑ a ∈ Icc 1 n, (a : ℂ) * χ a‖ ^ 4 ≤
        C * (n : ℝ) ^ 3 * (n.totient : ℝ) ^ 4 * Real.log (Real.log n) ^ 2

/-- Lemma 2: for `n, k ≥ 1` and `m` coprime to `n`,
`|∑_{1 ≤ a ≤ n, (a, n) = 1} a e_n(k m ā)| ≤ 2 n^{3/2} τ(n) (n, k)^{1/2} log(e n)`, where
`e_n(x) = exp(2πi x / n)` and `ā` is the inverse of `a` modulo `n` (represented by
`ZMod.val`; `e_n` is `n`-periodic). The paper's `m ≥ 1` follows from coprimality for `n ≥ 2`;
for `n = 1` the claim holds for every `m`.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 2. -/
public theorem_wanted weighted_kloosterman_sum_bound {n k m : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hmn : Nat.Coprime m n) :
    ‖∑ a ∈ Icc 1 n with Nat.Coprime a n,
        (a : ℂ) * exp (2 * Real.pi * I * (k * m * ((a : ZMod n)⁻¹).val : ℕ) / n)‖ ≤
      2 * (n : ℝ) ^ ((3 : ℝ) / 2) * n.divisors.card * Real.sqrt (Nat.gcd n k) *
        Real.log (Real.exp 1 * n)

/-- Lemma 3: for `q ≥ 2` and `q ∤ k`,
`∑_{b=1}^{q-1} b e_q(-k b) = -q / (1 - e_q(-k))`. The paper's `k ≥ 1` follows from `q ∤ k`.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 3. -/
public theorem_wanted sum_mul_additive_character {q k : ℕ} (hq : 2 ≤ q) (hk : ¬ q ∣ k) :
    ∑ b ∈ Icc 1 (q - 1), (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / q) =
      -q / (1 - exp (2 * Real.pi * I * (-(k : ℂ)) / q))

/-- Lemma 4: for `n ≥ 2` and `k ≥ 1`,
`∑_{1 ≤ b ≤ n, (b, n) = 1} b e_n(-k b) = -n ∑_{d ∣ n, (n/d) ∤ k} μ(d) / (1 - e_{n/d}(-k))
+ (n/2) ∑_{d ∣ n, d < n, (n/d) ∣ k} μ(d) (n/d - 1)`.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 4. -/
public theorem_wanted coprime_sum_mul_additive_character {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ∑ b ∈ Icc 1 n with Nat.Coprime b n, (b : ℂ) * exp (2 * Real.pi * I * (-(k * b : ℂ)) / n) =
      -n * ∑ d ∈ n.divisors with ¬ (n / d) ∣ k,
          (ArithmeticFunction.moebius d : ℂ) /
            (1 - exp (2 * Real.pi * I * (-(k : ℂ)) / (n / d : ℕ))) +
        n / 2 * ∑ d ∈ n.divisors with d < n ∧ (n / d) ∣ k,
          (ArithmeticFunction.moebius d : ℂ) * ((n / d : ℕ) - 1)

/-- Lemma 5: for any arithmetic function `f` and `n`,
`∑_{k=1}^n f(k) = ∑_{d ∣ n} ∑_{1 ≤ h ≤ n/d, (n/d, h) = 1} f(h d)`. The paper takes `n ≥ 1`;
for `n = 0` both sides are empty sums.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 5. -/
public theorem_wanted sum_Icc_eq_sum_divisors_coprime (f : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k =
      ∑ d ∈ n.divisors, ∑ h ∈ Icc 1 (n / d) with Nat.Coprime (n / d) h, f (h * d)

/-- Lemma 6: for `q ≥ 2`, `ℓ ≥ 1` and either sign `s = ±1`,
`∑_{a mod q, q ∤ a ℓ} 1 / |1 - e_q(s a ℓ)| ≤ (q/2) log(e q / (2 (ℓ, q))) < (q/2) log(e q)`.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 6. -/
public theorem_wanted sum_inv_norm_one_sub_additive_character {q ℓ : ℕ} (hq : 2 ≤ q)
    (hℓ : 1 ≤ ℓ) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∑ a ∈ range q with ¬ q ∣ a * ℓ,
        1 / ‖1 - exp (2 * Real.pi * I * ((s * (a * ℓ : ℕ) : ℤ) : ℂ) / q)‖ ≤
      q / 2 * Real.log (Real.exp 1 * q / (2 * Nat.gcd ℓ q)) ∧
    q / 2 * Real.log (Real.exp 1 * q / (2 * Nat.gcd ℓ q)) < q / 2 * Real.log (Real.exp 1 * q)

/-- Lemma 7: for `n ≥ 2` and `d ∣ n`,
`∑_{1 ≤ k ≤ n-1, (n/d) ∤ k} (n, k)^{1/2} / |1 - e_{n/d}(-k)| ≤ (1/2) n^{1/2} σ_{1/2}(n) log(e n)`,
where `σ_{1/2}(n) = ∑_{δ ∣ n} √δ`.

Source: O. Bordellès and L. Tóth, *Mean Values of the Product of an Integer and Its Modular
Inverse*, INTEGERS 24 (2024), Article A33, Lemma 7. -/
public theorem_wanted sum_sqrt_gcd_div_norm_one_sub_additive_character {n d : ℕ} (hn : 2 ≤ n)
    (hd : d ∣ n) :
    ∑ k ∈ Icc 1 (n - 1) with ¬ (n / d) ∣ k,
        Real.sqrt (Nat.gcd n k) / ‖1 - exp (2 * Real.pi * I * (-(k : ℂ)) / (n / d : ℕ))‖ ≤
      1 / 2 * Real.sqrt n * (∑ δ ∈ n.divisors, Real.sqrt δ) * Real.log (Real.exp 1 * n)

end

end MetaMathlibExt
