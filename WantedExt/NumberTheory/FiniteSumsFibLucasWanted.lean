/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite sums involving Fibonacci and Lucas numbers

Statements from Fatima Zohra Bensaci, Rachid Boumahdi, and
Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas
Numbers", *Journal of Integer Sequences* 27 (2024), Article
24.7.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Boumahdi/boumahdi12.tex>).

Notation: `α = (1 + √5)/2` and `β = (1 - √5)/2` are
`fibAlpha`/`fibBeta`; `Fₙ` is `Nat.fib`, `Lₙ` is
MathlibExt's `lucasNumber`, `Bₙ` is Mathlib's `bernoulli`,
`Gₙ` is MathlibExt's `genocchiNumber`, and the Euler
(secant) numbers `Eₙ` (exponential generating function
`2/(eᵗ + e⁻ᵗ)`) are `eulerSecNumber`, wrapping MathlibExt's
`chapter5EulerEven`. Several printed statements are false
as printed; each is stated below in a corrected form verified
by exact symbolic evaluation in `ℚ(√5)`, with the correction
documented at the declaration:

* Corollary 2's factor `β⁻ⁿ` gives the sum `2ᵐ`, not `0`;
  the `x = -β` specialization of Theorem 1 has `(-β)^{m-n}`.
* Corollary 4's falling factorial `(m-n+1)(s)` should be
  `(m-n)(s)` (it comes from differentiating `s` times).
* Corollary 6 needs `m ≥ 1` (at `m = 0` the sum is `2`).
* Theorem 11's inner sum omits the contribution of the
  `2/D` term of `(e^{αD} + e^{βD})/D`; the corrected inner
  coefficient (with the extra `2√5^{n+1} G_{n+1}/(n+1)`
  term) is `genLucasCoeff`. Corollaries 12–14 and Theorem 20
  inherit this correction; Corollary 12 also has
  `β^{m-n}` for `(-β)^{m-n}` as printed.
* Theorems 15 and 18 need the full multinomial coefficient
  `n! / (∏ jᵢ! ∏ ℓᵢ!)`; the paper's displayed definition
  omits the `ℓᵢ!` factors.
* Theorem 20's factors `L_{n-jᵢ+1}/(n-jᵢ+1)` are also wrong;
  the corrected form convolves `genLucasCoeff`.
* Theorem 23 is ill-formed as printed (the summation index
  `n` collides with the free `n` of the left side) and is
  not stated; see the source-audit ledger.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.Bernoulli
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.NumberTheory.GenocchiNumber
public import MathlibExt.NumberTheory.LucasSequence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.FiniteSumsFibLucasWanted

open MetaMathlibExt

/-- `√5` as a real number. -/
noncomputable def sqrt5 : ℝ := Real.sqrt 5

/-- The paper's `α = (1 + √5)/2`. -/
noncomputable def fibAlpha : ℝ := (1 + Real.sqrt 5) / 2

/-- The paper's `β = (1 - √5)/2`. -/
noncomputable def fibBeta : ℝ := (1 - Real.sqrt 5) / 2

/-- The paper's Euler (secant) numbers `Eₙ` (exponential
generating function `2/(eᵗ + e⁻ᵗ)`): `0` at odd indices and
MathlibExt's `chapter5EulerEven` at even indices
(`E₀ = 1`, `E₂ = -1`, `E₄ = 5`). -/
noncomputable def eulerSecNumber (n : ℕ) : ℚ :=
  if n % 2 = 1 then 0
  else ((MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry.chapter5EulerEven (n / 2) : ℤ) : ℚ)

/-- The corrected inner coefficient of Theorem 11:
`∑_{k=0}^n √5ᵏ C(n,k) Gₖ L_{n-k+1}/(n-k+1) +
2√5^{n+1} G_{n+1}/(n+1)`, where the last term is the
contribution of the `2/D` term that the printed proof drops
from `(e^{αD} + e^{βD})/D`. -/
noncomputable def genLucasCoeff (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), (Real.sqrt 5) ^ k *
      (Nat.choose n k : ℝ) * (genocchiNumber k : ℝ) *
      ((lucasNumber (n - k + 1) : ℝ) / (n - k + 1 : ℕ))) +
    2 * (Real.sqrt 5) ^ (n + 1) *
      ((genocchiNumber (n + 1) : ℝ) / (n + 1 : ℕ))

/-- **Theorem 1**: `(x + β)ᵐ = ∑_{n=0}^m ∑_{k=0}^n
√5ᵏ C(n,k) C(m,n) Bₖ F_{n-k+1}/(n-k+1) x^{m-n}` for every
real `x`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 1. -/
theorem_wanted add_fibBeta_pow_eq_sum (m : ℕ) (x : ℝ) :
    (x + fibBeta) ^ m =
      ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          x ^ (m - n)

/-- **Corollary 2** (corrected): with the factor
`(-β)^{m-n}` of the `x = -β` specialization of Theorem 1,
the double sum is `0` for `m ≥ 1`; as printed (factor
`β⁻ⁿ`) the sum equals `2ᵐ`, not `0`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 2. -/
theorem_wanted sum_bernoulli_fib_neg_fibBeta (m : ℕ) (hm : 1 ≤ m) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          (-fibBeta) ^ (m - n) = 0

/-- **Corollary 3**: `∑_{n=0}^m ∑_{k=0}^n (-2)ⁿ √5ᵏ
C(n,k) C(m,n) Bₖ F_{n-k+1}/(n-k+1) = √5ᵐ`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 3. -/
theorem_wanted sum_neg_two_pow_bernoulli_fib (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (-2 : ℝ) ^ n * (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) =
      (Real.sqrt 5) ^ m

/-- **Corollary 4** (corrected): differentiating Theorem 1
`s` times gives `(m)↓_s (x + β)^{m-s} = ∑_{n,k} √5ᵏ C(n,k)
C(m,n) Bₖ F_{n-k+1}/(n-k+1) (m-n)↓_s x^{m-n-s}` for `s ≤ m`;
the printed falling factor `(m-n+1)(s)` is off by one and
the identity is written cross-multiplied by `(m)↓_s`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 4. -/
theorem_wanted descFactorial_mul_add_fibBeta_pow (m s : ℕ)
    (hs : s ≤ m) (x : ℝ) :
    (Nat.descFactorial m s : ℝ) * (x + fibBeta) ^ (m - s) =
      ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k * (Nat.choose n k : ℝ) *
          (Nat.choose m n : ℝ) * (bernoulli k : ℝ) *
          ((Nat.fib (n - k + 1) : ℝ) / (n - k + 1 : ℕ)) *
          (Nat.descFactorial (m - n) s : ℝ) * x ^ (m - n - s)

/-- **Theorem 5**: `(x + 1/2)ᵐ = (1/2) ∑_{n=0}^m
∑_{k=0}^n (√5/2)ᵏ C(n,k) C(m,n) x^{m-n} Eₖ L_{n-k}` for
every real `x`, with `Eₖ` the Euler (secant) numbers.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 5. -/
theorem_wanted add_half_pow_eq_sum (m : ℕ) (x : ℝ) :
    (x + 1 / 2) ^ m =
      (1 / 2) * ∑ n ∈ Finset.range (m + 1),
        ∑ k ∈ Finset.range (n + 1),
          ((Real.sqrt 5) / 2) ^ k * (Nat.choose n k : ℝ) *
            (Nat.choose m n : ℝ) * x ^ (m - n) *
            (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ)

/-- **Corollary 6**: `∑_{n=0}^m ∑_{k=0}^n (-1)ⁿ √5ᵏ /
2^{k+m-n} C(n,k) C(m,n) Eₖ L_{n-k} = 0`, stated for
`m ≥ 1` (at `m = 0` the sum is `2`).

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 6. -/
theorem_wanted sum_neg_one_pow_eulerSec_lucas (m : ℕ)
    (hm : 1 ≤ m) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ n * (Real.sqrt 5) ^ k / 2 ^ (k + m - n) *
          (Nat.choose n k : ℝ) * (Nat.choose m n : ℝ) *
          (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) = 0

/-- **Corollary 7**: `∑_{n=0}^m ∑_{k=0}^n √5ᵏ / 2^{k+m-n}
C(n,k) C(m,n) Eₖ L_{n-k} = 2`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 7. -/
theorem_wanted sum_eulerSec_lucas (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (Real.sqrt 5) ^ k / 2 ^ (k + m - n) *
          (Nat.choose n k : ℝ) * (Nat.choose m n : ℝ) *
          (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) = 2

/-- **Corollary 8**: `∑_{n=0}^m ∑_{k=0}^n (√5/2)^{k+m-n}
C(n,k) C(m,n) Eₖ L_{n-k} = 2αᵐ`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 8. -/
theorem_wanted sum_eulerSec_lucas_eq_two_fibAlpha_pow (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        ((Real.sqrt 5) / 2) ^ (k + m - n) *
          (Nat.choose n k : ℝ) * (Nat.choose m n : ℝ) *
          (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) =
      2 * fibAlpha ^ m

/-- **Corollary 9**: `∑_{n=0}^m ∑_{k=0}^n (-1)^{m-n}
(√5/2)^{k+m-n} C(n,k) C(m,n) Eₖ L_{n-k} = 2βᵐ`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 9. -/
theorem_wanted sum_eulerSec_lucas_eq_two_fibBeta_pow (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (m - n) * ((Real.sqrt 5) / 2) ^ (k + m - n) *
          (Nat.choose n k : ℝ) * (Nat.choose m n : ℝ) *
          (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) =
      2 * fibBeta ^ m

/-- **Corollary 10**: `∑_{k=0}^n C(n,k) (√5/2)ᵏ Eₖ
L_{n-k} = 2^{1-n}`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 10. -/
theorem_wanted sum_choose_eulerSec_lucas (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * ((Real.sqrt 5) / 2) ^ k *
          (eulerSecNumber k : ℝ) * (lucasNumber (n - k) : ℝ) =
      2 / 2 ^ n

/-- **Theorem 11** (corrected): `(x + β)ᵐ = (1/(2√5))
∑_{n=0}^m C(m,n) cₙ x^{m-n}` where `cₙ` is
`genLucasCoeff n`, the printed inner sum
`∑_{k=0}^n √5ᵏ C(n,k) Gₖ L_{n-k+1}/(n-k+1)` plus the
dropped term `2√5^{n+1} G_{n+1}/(n+1)` (the printed form
already fails at `m = 0`, giving `0` for `1`).

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 11. -/
theorem_wanted add_fibBeta_pow_eq_sum_genLucasCoeff (m : ℕ)
    (x : ℝ) :
    (x + fibBeta) ^ m =
      (1 / (2 * Real.sqrt 5)) * ∑ n ∈ Finset.range (m + 1),
        (Nat.choose m n : ℝ) * genLucasCoeff n * x ^ (m - n)

/-- **Corollary 12** (corrected): the `x = -β`
specialization of corrected Theorem 11,
`∑_{n=0}^m C(m,n) cₙ (-β)^{m-n} = 0` for `m ≥ 1`; as
printed (with `β^{m-n}` and without the correction term in
`cₙ`) the sum at `m = 2` is `-10 + 4√5`, not `0`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 12. -/
theorem_wanted sum_genLucasCoeff_neg_fibBeta (m : ℕ)
    (hm : 1 ≤ m) :
    ∑ n ∈ Finset.range (m + 1),
        (Nat.choose m n : ℝ) * genLucasCoeff n *
          (-fibBeta) ^ (m - n) = 0

/-- **Corollary 13** (corrected):
`∑_{n=0}^m (2/√5)ⁿ C(m,n) cₙ = 2√5^{1-m}` with
`cₙ = genLucasCoeff n`; expanding `cₙ` gives the printed
double sum `∑ 2ⁿ√5^{k-n} C(n,k) C(m,n) Gₖ L_{n-k+1}/(n-k+1)`
plus the correction `∑ (2/√5)ⁿ C(m,n) 2√5^{n+1}
G_{n+1}/(n+1)`. The printed form holds only for odd `m`
(at `m = 2` it gives `12√5/5` against `2√5/5`).

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 13. -/
theorem_wanted sum_genLucasCoeff_weighted (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1),
        (2 / Real.sqrt 5) ^ n * (Nat.choose m n : ℝ) *
          genLucasCoeff n =
      2 * Real.sqrt 5 / (Real.sqrt 5) ^ m

/-- **Corollary 14** (corrected): `∑_{k=0}^n √5ᵏ C(n,k)
Gₖ L_{n-k+1}/(n-k+1) + 2√5^{n+1} G_{n+1}/(n+1) = 2√5 βⁿ`,
the printed identity `∑ √5^{k-1} ⋯ = 2βⁿ` multiplied
through by `√5` with the correction term restored (the
printed form holds only for even `n ≥ 2`; at `n = 1` it
gives `1` against `2β = 1 - √5`).

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 14. -/
theorem_wanted sum_genocchi_lucas_add (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (Real.sqrt 5) ^ k *
        (Nat.choose n k : ℝ) * (genocchiNumber k : ℝ) *
        ((lucasNumber (n - k + 1) : ℝ) / (n - k + 1 : ℕ))) +
      2 * (Real.sqrt 5) ^ (n + 1) *
        ((genocchiNumber (n + 1) : ℝ) / (n + 1 : ℕ)) =
    2 * Real.sqrt 5 * fibBeta ^ n

/-- **Theorem 15** (corrected multinomial): for `q ≥ 1`
and every real `x`, `(x + qβ)ᵐ` is the sum over `n ≤ m` and
`j₁+⋯+j_q+ℓ₁+⋯+ℓ_q = n` of `√5^{ℓ₁+⋯+ℓ_q} · (n!/(∏jᵢ!∏ℓᵢ!))
· C(m,n) · B_{ℓ₁}⋯B_{ℓ_q} · ∏ F_{jᵢ+1}/(jᵢ+1) · x^{m-n}`,
with the full multinomial coefficient (the paper's displayed
definition omits the `ℓᵢ!` factors, and with them omitted
the identity fails, e.g. at `q = 2`, `x = √5`, `m = 2`).

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 15. -/
theorem_wanted add_mul_fibBeta_pow_eq_sum (q m : ℕ)
    (hq : 1 ≤ q) (x : ℝ) :
    (x + q * fibBeta) ^ m =
      ∑ n ∈ Finset.range (m + 1),
        ∑ jℓ ∈ (Finset.univ :
            Finset ((Fin q → Fin (n + 1)) ×
              (Fin q → Fin (n + 1)))).filter
            (fun jℓ => (∑ i, (jℓ.1 i).val) +
              (∑ i, (jℓ.2 i).val) = n),
          (Real.sqrt 5) ^ (∑ i, (jℓ.2 i).val) *
            ((n.factorial : ℝ) /
              ((∏ i, ((jℓ.1 i).val.factorial : ℝ)) *
                ∏ i, ((jℓ.2 i).val.factorial : ℝ))) *
            (Nat.choose m n : ℝ) *
            (∏ i, (bernoulli (jℓ.2 i).val : ℝ)) *
            (∏ i, ((Nat.fib ((jℓ.1 i).val + 1) : ℝ) /
              ((jℓ.1 i).val + 1 : ℕ))) *
            x ^ (m - n)

/-- **Corollary 17** (corrected multinomial): the `q = 2`,
`x = √5` case of Theorem 15, whose sum is `1` since
`√5 + 2β = 1`; with the paper's displayed multinomial the
sum at `m = 2` is `8/3`, not `1`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Corollary 17. -/
theorem_wanted sum_bernoulli_fib_two_eq_one (m : ℕ) :
    ∑ n ∈ Finset.range (m + 1),
        ∑ jℓ ∈ (Finset.univ :
            Finset ((Fin 2 → Fin (n + 1)) ×
              (Fin 2 → Fin (n + 1)))).filter
            (fun jℓ => (∑ i, (jℓ.1 i).val) +
              (∑ i, (jℓ.2 i).val) = n),
          (Real.sqrt 5) ^ ((∑ i, (jℓ.2 i).val) + m - n) *
            ((n.factorial : ℝ) /
              ((∏ i, ((jℓ.1 i).val.factorial : ℝ)) *
                ∏ i, ((jℓ.2 i).val.factorial : ℝ))) *
            (Nat.choose m n : ℝ) *
            (∏ i, (bernoulli (jℓ.2 i).val : ℝ)) *
            (∏ i, ((Nat.fib ((jℓ.1 i).val + 1) : ℝ) /
              ((jℓ.1 i).val + 1 : ℕ))) = 1

/-- **Theorem 18** (corrected multinomial): for `q ≥ 1`
and every real `x`, `2^q (x + q/2)ᵐ` is the sum over
`n ≤ m` and `j₁+⋯+j_q+ℓ₁+⋯+ℓ_q = n` of
`(√5/2)^{ℓ₁+⋯+ℓ_q} · (n!/(∏jᵢ!∏ℓᵢ!)) · C(m,n) ·
E_{ℓ₁}⋯E_{ℓ_q} · L_{j₁}⋯L_{j_q} · x^{m-n}`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 18. -/
theorem_wanted two_pow_mul_add_half_pow (q m : ℕ)
    (hq : 1 ≤ q) (x : ℝ) :
    (2 : ℝ) ^ q * (x + (q : ℝ) / 2) ^ m =
      ∑ n ∈ Finset.range (m + 1),
        ∑ jℓ ∈ (Finset.univ :
            Finset ((Fin q → Fin (n + 1)) ×
              (Fin q → Fin (n + 1)))).filter
            (fun jℓ => (∑ i, (jℓ.1 i).val) +
              (∑ i, (jℓ.2 i).val) = n),
          ((Real.sqrt 5) / 2) ^ (∑ i, (jℓ.2 i).val) *
            ((n.factorial : ℝ) /
              ((∏ i, ((jℓ.1 i).val.factorial : ℝ)) *
                ∏ i, ((jℓ.2 i).val.factorial : ℝ))) *
            (Nat.choose m n : ℝ) *
            (∏ i, (eulerSecNumber (jℓ.2 i).val : ℝ)) *
            (∏ i, (lucasNumber (jℓ.1 i).val : ℝ)) *
            x ^ (m - n)

/-- **Theorem 20** (corrected): for `q ≥ 1` and every real
`x`, `(2√5)^q (x + qβ)ᵐ = ∑_{n=0}^m C(m,n) x^{m-n}
∑_{j₁+⋯+j_q=n} (n!/∏jᵢ!) c_{j₁}⋯c_{j_q}` with
`c = genLucasCoeff`, the `q`-fold convolution form of
corrected Theorem 11; as printed (factors
`L_{n-jᵢ+1}/(n-jᵢ+1)`, multinomial without `ℓᵢ!`, no
correction terms) the identity fails already at `q = 1`.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 20. -/
theorem_wanted two_sqrt5_pow_mul_add (q m : ℕ) (hq : 1 ≤ q)
    (x : ℝ) :
    (2 * Real.sqrt 5) ^ q * (x + q * fibBeta) ^ m =
      ∑ n ∈ Finset.range (m + 1), (Nat.choose m n : ℝ) *
        x ^ (m - n) *
        ∑ j ∈ (Finset.univ :
            Finset (Fin q → Fin (n + 1))).filter
            (fun j => ∑ i, (j i).val = n),
          ((n.factorial : ℝ) /
              ∏ i, ((j i).val.factorial : ℝ)) *
            ∏ i, genLucasCoeff (j i).val

/-- **Lemma 21**: the `k`-th forward difference with step
`r` of `y ↦ yⁿ` is `∑_{j=0}^k (-1)^{k-j} C(k,j) (x + rj)ⁿ`
(paper: nonzero complex `r`, positive `k`; the identity
holds for all real `r` and all `k`).

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Lemma 21. -/
theorem_wanted iterate_forwardDiff_pow_eq_sum (r x : ℝ)
    (k n : ℕ) :
    ((fun f : ℝ → ℝ => fun y => f (y + r) - f y)^[k]
        (fun y => y ^ n)) x =
      ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ (k - j) *
        (Nat.choose k j : ℝ) * (x + r * j) ^ n

/-- **Theorem 22**: `Gₙ/n = ∑_{j=0}^{n-1} (-1)ʲ j!/2ʲ
S(n-1, j)` for `n ≥ 1`, with `S` the Stirling numbers of
the second kind, as a rational identity.

Source: Fatima Zohra Bensaci, Rachid Boumahdi, and Laala
Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers",
Theorem 22. -/
theorem_wanted genocchiNumber_div_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    genocchiNumber n / (n : ℚ) =
      ∑ j ∈ Finset.range n, (-1 : ℚ) ^ j *
        (j.factorial : ℚ) / 2 ^ j *
        (Nat.stirlingSecond (n - 1) j : ℚ)

end MathlibExt.NumberTheory.FiniteSumsFibLucasWanted
