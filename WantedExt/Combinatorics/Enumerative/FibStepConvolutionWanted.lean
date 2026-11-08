/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# General convolution sums involving Fibonacci `m`-step numbers

Statements from Robert Frontczak and Karol Gryszka,
"General Convolution Sums Involving Fibonacci `m`-Step
Numbers", *Journal of Integer Sequences* 27 (2024),
Article 24.8.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Gryszka/gryszka12.tex>).

The Fibonacci `m`-step numbers `F⁽ᵐ⁾ₙ` (`F₀ = 0`,
`F₁ = 1`, `Fₙ = F_{n-1} + ⋯ + F_{n-m}` for `n ≥ 2`, terms
at negative indices being `0`) are `fibStep m n`, defined
by list recursion; `F⁽²⁾, F⁽³⁾, F⁽⁴⁾, F⁽⁵⁾` are the paper's
`F, T, Q, P`. Jacobsthal numbers are `jacobsthalSeq`, Pell
numbers are MathlibExt's `pellNumber`, sums over
`K(r, n)` (compositions of `n` into `r` nonnegative parts)
are `compProdSum`, and ordinary generating functions are
`fibStepGF m = ∑ₙ F⁽ᵐ⁾ₙ Xⁿ`. Two printed statements are
corrected, each found numerically and checked against the
paper's own derivations: Theorem 8's inner coefficients
are `m-1-k`, not `k` (its proof's penultimate display has
the right coefficients), and Corollary 13's fourth
identity has `Q_{n+2-j}`, not `Q_{n-j}`; Theorem 34's
printed `F^{(m+3)}_{k_3}` is `F^{(m+3)}_{k_4}`. Displayed
fractions `1/2`, `1/5`, `1/(m-1)` are cleared by
multiplication to stay in `ℤ`. Corollary 16 repeats
Corollary 9's first identity and maps to the same
declaration.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.PellNumberSequence

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted

/-- Initial segment `[F⁽ᵐ⁾₀, …, F⁽ᵐ⁾ₙ]` of the Fibonacci
`m`-step sequence, by list recursion. -/
def fibStepSeq (m : ℕ) : ℕ → List ℤ
  | 0 => [0]
  | 1 => [0, 1]
  | n + 2 =>
      let prev := fibStepSeq m (n + 1)
      prev ++ [∑ j ∈ Finset.Icc 1 m, prev.getD (n + 2 - j) 0]

/-- The Fibonacci `m`-step numbers `F⁽ᵐ⁾ₙ`. -/
def fibStep (m n : ℕ) : ℤ := (fibStepSeq m n).getD n 0

/-- The Jacobsthal numbers `J₀ = 0`, `J₁ = 1`,
`J_{n+2} = J_{n+1} + 2Jₙ`. -/
def jacobsthalSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => jacobsthalSeq (n + 1) + 2 * jacobsthalSeq n

/-- Ordinary generating function `F^{(m)}(X)` of the
Fibonacci `m`-step numbers. -/
noncomputable def fibStepGF (m : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (fibStep m n : ℚ)

/-- Sums over compositions `K(r, n)`:
`∑_{(k₁,…,k_r), ∑ k_i = n} ∏_i (seqs i (k_i))`. -/
def compProdSum {r : ℕ} (seqs : Fin r → ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ (Finset.univ : Finset (Fin r → Fin (n + 1))).filter
      (fun k => ∑ i, (k i).val = n), ∏ i, seqs i (k i).val

/-- **Theorem 1**: for `n ≥ m`,
`∑_{j=0}^{n-m} F⁽ᵐ⁾ⱼ F⁽ᵐ⁺¹⁾_{n-m-j} = F⁽ᵐ⁺¹⁾ₙ - F⁽ᵐ⁾ₙ`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 1. -/
theorem_wanted sum_fibStep_mul_succ (m n : ℕ) (hm : 1 ≤ m)
    (hn : m ≤ n) :
    ∑ j ∈ Finset.range (n - m + 1),
        fibStep m j * fibStep (m + 1) (n - m - j) =
      fibStep (m + 1) n - fibStep m n

/-- **Corollary 2**, `F*T` case:
`∑_{j=0}^n F_j T_{n-j} = T_{n+2} - F_{n+2}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 2. -/
theorem_wanted sum_fib_mul_trib (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), fibStep 2 j * fibStep 3 (n - j) =
      fibStep 3 (n + 2) - fibStep 2 (n + 2)

/-- **Corollary 2**, `T*Q` case:
`∑_{j=0}^n T_j Q_{n-j} = Q_{n+3} - T_{n+3}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 2. -/
theorem_wanted sum_trib_mul_tetra (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), fibStep 3 j * fibStep 4 (n - j) =
      fibStep 4 (n + 3) - fibStep 3 (n + 3)

/-- **Corollary 2**, `Q*P` case:
`∑_{j=0}^n Q_j P_{n-j} = P_{n+4} - Q_{n+4}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 2. -/
theorem_wanted sum_tetra_mul_penta (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), fibStep 4 j * fibStep 5 (n - j) =
      fibStep 5 (n + 4) - fibStep 4 (n + 4)

/-- **Theorem 3**: for `n ≥ m`,
`∑_{k=0}^{p-1} ∑_{j=0}^{n-m-k} F⁽ᵐ⁾ⱼ F⁽ᵐ⁺ᵖ⁾_{n-m-k-j}
= F⁽ᵐ⁺ᵖ⁾ₙ - F⁽ᵐ⁾ₙ`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 3. -/
theorem_wanted sum_sum_fibStep_mul (m p n : ℕ) (hm : 1 ≤ m)
    (hn : m ≤ n) :
    ∑ k ∈ Finset.range p, ∑ j ∈ Finset.range (n - m - k + 1),
        fibStep m j * fibStep (m + p) (n - m - k - j) =
      fibStep (m + p) n - fibStep m n

/-- **Corollary 4**: for `n ≥ m`,
`∑_{j=0}^{n-m-1} F⁽ᵐ⁾ⱼ (F⁽ᵐ⁺²⁾_{n-m-j} +
F⁽ᵐ⁺²⁾_{n-m-j-1}) = F⁽ᵐ⁺²⁾ₙ - F⁽ᵐ⁾ₙ`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 4. -/
theorem_wanted sum_fibStep_mul_add (m n : ℕ) (hm : 1 ≤ m)
    (hn : m ≤ n) :
    ∑ j ∈ Finset.range (n - m), fibStep m j *
        (fibStep (m + 2) (n - m - j) +
          fibStep (m + 2) (n - m - j - 1)) =
      fibStep (m + 2) n - fibStep m n

/-- **Corollary 7**: for `n ≥ p ≥ 1`,
`F⁽ᵖ⁺¹⁾ₙ - 1 = ∑_{k=0}^{p-1} ∑_{j=0}^{n-2-k} F⁽ᵖ⁺¹⁾ⱼ`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 7. -/
theorem_wanted fibStep_sub_one_eq_sum_sum (p n : ℕ)
    (hp : 1 ≤ p) (hn : p ≤ n) :
    fibStep (p + 1) n - 1 =
      ∑ k ∈ Finset.range p, ∑ j ∈ Finset.range (n - 1 - k),
        fibStep (p + 1) j

/-- **Theorem 8** (partial sums, corrected): for `m ≥ 2`,
`(m-1) ∑_{k=0}^n F⁽ᵐ⁾ₖ = F⁽ᵐ⁾_{n+m} -
∑_{k=1}^{m-2} (m-1-k) F⁽ᵐ⁾_{n+k} - 1`; the printed
coefficients `k` are a transcription error (the proof's
own display gives `m-1-k`; as printed the formula fails
already at `m = 4`, `n = 1`, giving `2/3` for `1`),
written multiplied through by `m - 1`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 8. -/
theorem_wanted mul_sum_fibStep (m n : ℕ) (hm : 2 ≤ m) :
    ((m : ℤ) - 1) * ∑ k ∈ Finset.range (n + 1), fibStep m k =
      fibStep m (n + m) -
        ∑ k ∈ Finset.Icc 1 (m - 2),
          ((m - 1 - k : ℕ) : ℤ) * fibStep m (n + k) - 1

/-- **Corollary 9** (also Corollary 16), `F*Q` case:
`∑_{j=0}^n F_j Q_{n-j} = Q_{n+1} + Q_{n-1} - F_{n+1}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollaries 9 and 16. -/
theorem_wanted sum_fib_mul_tetra (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), fibStep 2 j * fibStep 4 (n - j) =
      fibStep 4 (n + 1) + fibStep 4 (n - 1) - fibStep 2 (n + 1)

/-- **Corollary 9**, `F*P` case:
`2 ∑_{j=0}^n F_j P_{n-j} = P_{n+2} + P_{n-1} - F_{n+2}`
(printed with a factor `1/2`).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 9. -/
theorem_wanted two_mul_sum_fib_mul_penta (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1),
        fibStep 2 j * fibStep 5 (n - j) =
      fibStep 5 (n + 2) + fibStep 5 (n - 1) - fibStep 2 (n + 2)

/-- **Corollary 9**, `P*T` case:
`2 ∑_{j=0}^n P_j T_{n-j} = P_{n+3} + P_{n+1} + P_{n-1}
- T_{n+3} - T_{n+1}` (printed with a factor `1/2`).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 9. -/
theorem_wanted two_mul_sum_penta_mul_trib (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1),
        fibStep 5 j * fibStep 3 (n - j) =
      fibStep 5 (n + 3) + fibStep 5 (n + 1) + fibStep 5 (n - 1) -
        fibStep 3 (n + 3) - fibStep 3 (n + 1)

/-- **Theorem 10**: for `n ≥ 1`, `m ≥ 3`,
`∑_{j=0}^n F⁽ᵐ⁻²⁾ⱼ (F⁽ᵐ⁾_{n-j} - F⁽ᵐ⁻¹⁾_{n-j}) =
∑_{j=0}^{n-1} F⁽ᵐ⁾ⱼ (F⁽ᵐ⁻¹⁾_{n-1-j} - F⁽ᵐ⁻²⁾_{n-1-j})`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 10. -/
theorem_wanted sum_fibStep_sub_eq (m n : ℕ) (hm : 3 ≤ m)
    (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range (n + 1), fibStep (m - 2) j *
        (fibStep m (n - j) - fibStep (m - 1) (n - j)) =
      ∑ j ∈ Finset.range n, fibStep m j *
        (fibStep (m - 1) (n - 1 - j) - fibStep (m - 2) (n - 1 - j))

/-- **Corollary 11**, first identity:
`T_{n+1} - F_{n+1} = ∑_{j=0}^{n-1} T_j F_{n-1-j}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 11. -/
theorem_wanted trib_sub_fib_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    fibStep 3 (n + 1) - fibStep 2 (n + 1) =
      ∑ j ∈ Finset.range n, fibStep 3 j * fibStep 2 (n - 1 - j)

/-- **Corollary 11**, second identity:
`∑_{j=0}^n F_j (T_{n-j} - Q_{n-j}) =
∑_{j=0}^{n-1} (F_j - T_j) Q_{n-1-j}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 11. -/
theorem_wanted sum_fib_mul_sub_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range (n + 1), fibStep 2 j *
        (fibStep 3 (n - j) - fibStep 4 (n - j)) =
      ∑ j ∈ Finset.range n,
        (fibStep 2 j - fibStep 3 j) * fibStep 4 (n - 1 - j)

/-- **Corollary 11**, third identity:
`∑_{j=0}^n T_j (Q_{n-j} - P_{n-j}) =
∑_{j=0}^{n-1} (T_j - Q_j) P_{n-1-j}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 11. -/
theorem_wanted sum_trib_mul_sub_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range (n + 1), fibStep 3 j *
        (fibStep 4 (n - j) - fibStep 5 (n - j)) =
      ∑ j ∈ Finset.range n,
        (fibStep 3 j - fibStep 4 j) * fibStep 5 (n - 1 - j)

/-- **Theorem 12**: for `m, n ≥ 2`,
`∑_{j=0}^n F⁽ᵐ⁻¹⁾ⱼ F⁽ᵐ⁾_{n-j} =
∑_{j=0}^{n-2} 2^j (F⁽ᵐ⁻¹⁾_{n-1-j} - F⁽ᵐ⁾_{n-2-j})`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 12. -/
theorem_wanted sum_fibStep_pred_mul (m n : ℕ) (hm : 2 ≤ m)
    (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range (n + 1),
        fibStep (m - 1) j * fibStep m (n - j) =
      ∑ j ∈ Finset.range (n - 1), 2 ^ j *
        (fibStep (m - 1) (n - 1 - j) - fibStep m (n - 2 - j))

/-- **Corollary 13**, fourth identity (corrected):
`∑_{j=0}^{n+2} T_j Q_{n+2-j} =
∑_{j=0}^n 2^j (T_{n+1-j} - Q_{n-j})`; the printed
`Q_{n-j}` on the left is a typo (the identity is Theorem
12 at `m = 4` with `n` replaced by `n + 2`; as printed it
fails at `n = 0`, giving `0` for `1`).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 13. -/
theorem_wanted sum_trib_mul_tetra_eq (n : ℕ) :
    ∑ j ∈ Finset.range (n + 3), fibStep 3 j * fibStep 4 (n + 2 - j) =
      ∑ j ∈ Finset.range (n + 1), 2 ^ j *
        (fibStep 3 (n + 1 - j) - fibStep 4 (n - j))

/-- **Theorem 15**: for `m ≥ 2` (so that `F^{(2m-2)}` is
defined) and `n ≥ 2m - 1`,
`∑_{j=0}^{n-1} (-1)^j (F^{(2m)}_j - F^{(2m-2)}_j) =
(-1)^{n+1} ∑_{j=0}^{n-2m+1} F^{(2m)}_j F^{(2m-2)}_{n-2m+1-j}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 15. -/
theorem_wanted sum_neg_one_pow_sub_even (m n : ℕ)
    (hm : 2 ≤ m) (hn : 2 * m - 1 ≤ n) :
    ∑ j ∈ Finset.range n, (-1 : ℤ) ^ j *
        (fibStep (2 * m) j - fibStep (2 * m - 2) j) =
      (-1 : ℤ) ^ (n + 1) *
        ∑ j ∈ Finset.range (n - 2 * m + 2),
          fibStep (2 * m) j * fibStep (2 * m - 2) (n - 2 * m + 1 - j)

/-- **Theorem 17**: for `n ≥ 2m`,
`∑_{j=0}^{n-1} (-1)^{j+1} (F^{(2m+1)}_j - F^{(2m-1)}_j) =
(-1)^n ∑_{j=0}^{n-2m} F^{(2m+1)}_j F^{(2m-1)}_{n-2m-j}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 17. -/
theorem_wanted sum_neg_one_pow_sub_odd (m n : ℕ)
    (hm : 1 ≤ m) (hn : 2 * m ≤ n) :
    ∑ j ∈ Finset.range n, (-1 : ℤ) ^ (j + 1) *
        (fibStep (2 * m + 1) j - fibStep (2 * m - 1) j) =
      (-1 : ℤ) ^ n *
        ∑ j ∈ Finset.range (n - 2 * m + 1),
          fibStep (2 * m + 1) j * fibStep (2 * m - 1) (n - 2 * m - j)

/-- **Corollary 18**, first identity:
`2 ∑_{j=0}^n (-1)^j T_j = (-1)^n (T_{n+1} - T_{n-1}) - 1`
(printed with a factor `1/2`).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 18. -/
theorem_wanted two_mul_sum_neg_one_pow_trib (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ j * fibStep 3 j =
      (-1 : ℤ) ^ n * (fibStep 3 (n + 1) - fibStep 3 (n - 1)) - 1

/-- **Corollary 18**, second identity:
`2 ∑_{j=0}^n P_j T_{n-j} = -P_{n+7} + 2P_{n+6} - P_{n+5}
+ 2P_{n+4} + P_{n+3} - T_{n+4} + T_{n+2}` (printed with a
factor `1/2`).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 18. -/
theorem_wanted two_mul_sum_penta_mul_trib' (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1),
        fibStep 5 j * fibStep 3 (n - j) =
      -fibStep 5 (n + 7) + 2 * fibStep 5 (n + 6) -
        fibStep 5 (n + 5) + 2 * fibStep 5 (n + 4) +
        fibStep 5 (n + 3) - fibStep 3 (n + 4) + fibStep 3 (n + 2)

/-- **Theorem 19**: for `m ≥ 3`, `n ≥ 2`, with `J` the
Jacobsthal numbers, `∑_{j=0}^n F⁽ᵐ⁾ⱼ F⁽ᵐ⁻²⁾_{n-j} =
J_{n-1} + ∑_{j=0}^{n-2} J_j (F⁽ᵐ⁻²⁾_{n-j} - F⁽ᵐ⁾_{n-2-j})`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 19. -/
theorem_wanted sum_fibStep_mul_sub_two (m n : ℕ) (hm : 3 ≤ m)
    (hn : 2 ≤ n) :
    ∑ j ∈ Finset.range (n + 1),
        fibStep m j * fibStep (m - 2) (n - j) =
      jacobsthalSeq (n - 1) +
        ∑ j ∈ Finset.range (n - 1), jacobsthalSeq j *
          (fibStep (m - 2) (n - j) - fibStep m (n - 2 - j))

/-- **Corollary 20**:
`2 ∑_{j=0}^n J_j T_{n-j} = 2J_{n+1} + J_{n+2} - T_{n+3}
- T_{n+1}` (printed with a factor `1/2` on part of the
right side).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 20. -/
theorem_wanted two_mul_sum_jacobsthal_mul_trib (n : ℕ) :
    2 * ∑ j ∈ Finset.range (n + 1),
        jacobsthalSeq j * fibStep 3 (n - j) =
      2 * jacobsthalSeq (n + 1) + jacobsthalSeq (n + 2) -
        fibStep 3 (n + 3) - fibStep 3 (n + 1)

/-- **Theorem 21** (Pell–Fibonacci `m`-step relation):
for `n ≥ 1`, `m ≥ 2`,
`∑_{K(3,n-1)} 𝒫_{k₁} F⁽ᵐ⁻¹⁾_{k₂} F⁽ᵐ⁾_{k₃} =
∑_{j=0}^n F⁽ᵐ⁻¹⁾ⱼ (𝒫_{n-j} - F⁽ᵐ⁾_{n-j}) -
∑_{j=0}^{n-1} 𝒫_j F⁽ᵐ⁾_{n-1-j}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 21. -/
theorem_wanted compProdSum_pell_fibStep (m n : ℕ)
    (hm : 2 ≤ m) (hn : 1 ≤ n) :
    compProdSum
        (fun i k => ![fun t => (MetaMathlibExt.pellNumber t : ℤ),
          fibStep (m - 1), fibStep m] i k) (n - 1) =
      ∑ j ∈ Finset.range (n + 1), fibStep (m - 1) j *
          ((MetaMathlibExt.pellNumber (n - j) : ℤ) -
            fibStep m (n - j)) -
        ∑ j ∈ Finset.range n,
          (MetaMathlibExt.pellNumber j : ℤ) * fibStep m (n - 1 - j)

/-- **Corollary 22**:
`∑_{j=0}^n 𝒫_j F_{n-j} = 𝒫ₙ - Fₙ`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 22. -/
theorem_wanted sum_pell_mul_fib (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1),
        (MetaMathlibExt.pellNumber j : ℤ) * fibStep 2 (n - j) =
      (MetaMathlibExt.pellNumber n : ℤ) - fibStep 2 n

/-- **Corollary 23**, first form:
`∑_{K(3,n)} 𝒫_{k₁} F_{k₂} T_{k₃} = 𝒫_{n+1} + F_{n+2} -
T_{n+3} - ∑_{j=0}^n 𝒫_j T_{n-j}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 23. -/
theorem_wanted compProdSum_pell_fib_trib (n : ℕ) :
    compProdSum
        (fun i k => ![fun t => (MetaMathlibExt.pellNumber t : ℤ),
          fibStep 2, fibStep 3] i k) n =
      (MetaMathlibExt.pellNumber (n + 1) : ℤ) + fibStep 2 (n + 2) -
        fibStep 3 (n + 3) -
        ∑ j ∈ Finset.range (n + 1),
          (MetaMathlibExt.pellNumber j : ℤ) * fibStep 3 (n - j)

/-- **Corollary 23**, second form:
`2 ∑_{K(3,n)} 𝒫_{k₁} F_{k₂} T_{k₃} = 𝒫_{n+1} - T_{n+3}
- T_{n+2} + 2F_{n+2}` (printed with a factor `1/2`).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 23. -/
theorem_wanted two_mul_compProdSum_pell_fib_trib (n : ℕ) :
    2 * compProdSum
        (fun i k => ![fun t => (MetaMathlibExt.pellNumber t : ℤ),
          fibStep 2, fibStep 3] i k) n =
      (MetaMathlibExt.pellNumber (n + 1) : ℤ) - fibStep 3 (n + 3) -
        fibStep 3 (n + 2) + 2 * fibStep 2 (n + 2)

/-- **Theorem 24** (generating functions): for
`m, p, q ≥ 1`,
`X^{2m+p} (1-X^p)(1-X^q) F^{(m)} F^{(m+p)} F^{(m+p+q)} =
X^m (1-X)(1-X^p) F^{(m)} F^{(m+p+q)} -
(1-X)^2 (F^{(m+p)} - F^{(m)})` in `ℚ⟦X⟧`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 24. -/
theorem_wanted fibStepGF_triple_identity (m p q : ℕ)
    (hm : 1 ≤ m) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    PowerSeries.X ^ (2 * m + p) *
        (1 - PowerSeries.X ^ p) * (1 - PowerSeries.X ^ q) *
        fibStepGF m * fibStepGF (m + p) * fibStepGF (m + p + q) =
      PowerSeries.X ^ m * (1 - PowerSeries.X) *
          (1 - PowerSeries.X ^ p) * fibStepGF m *
          fibStepGF (m + p + q) -
        (1 - PowerSeries.X) ^ 2 *
          (fibStepGF (m + p) - fibStepGF m)

/-- **Theorem 24**, particular case (`p = q = 1`):
`X^{2m+1} F^{(m)} F^{(m+1)} F^{(m+2)} =
X^m F^{(m)} F^{(m+2)} - F^{(m+1)} + F^{(m)}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 24. -/
theorem_wanted fibStepGF_triple_consecutive (m : ℕ)
    (hm : 1 ≤ m) :
    PowerSeries.X ^ (2 * m + 1) * fibStepGF m * fibStepGF (m + 1) *
        fibStepGF (m + 2) =
      PowerSeries.X ^ m * fibStepGF m * fibStepGF (m + 2) -
        fibStepGF (m + 1) + fibStepGF m

/-- **Theorem 25** (generating functions):
`X^m F^{(m)} F^{(m+1)} F^{(p)} =
F^{(p)} F^{(m+1)} - F^{(p)} F^{(m)}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 25. -/
theorem_wanted fibStepGF_mixed_triple (m p : ℕ) (hm : 1 ≤ m)
    (hp : 1 ≤ p) :
    PowerSeries.X ^ m * fibStepGF m * fibStepGF (m + 1) *
        fibStepGF p =
      fibStepGF p * fibStepGF (m + 1) - fibStepGF p * fibStepGF m

/-- **Theorem 25**, coefficient form: for `n ≥ m`,
`∑_{K(3,n-m)} F⁽ᵐ⁾_{k₁} F⁽ᵐ⁺¹⁾_{k₂} F⁽ᵖ⁾_{k₃} =
∑_{j=0}^n F⁽ᵖ⁾ⱼ F⁽ᵐ⁺¹⁾_{n-j} -
∑_{j=0}^n F⁽ᵖ⁾ⱼ F⁽ᵐ⁾_{n-j}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 25. -/
theorem_wanted compProdSum_fibStep_triple (m p n : ℕ)
    (hm : 1 ≤ m) (hp : 1 ≤ p) (hn : m ≤ n) :
    compProdSum (fun i k => ![fibStep m, fibStep (m + 1),
        fibStep p] i k) (n - m) =
      ∑ j ∈ Finset.range (n + 1),
          fibStep p j * fibStep (m + 1) (n - j) -
        ∑ j ∈ Finset.range (n + 1),
          fibStep p j * fibStep m (n - j)

/-- **Theorem 26**:
`∑_{K(3,n)} F_{k₁} T_{k₂} Q_{k₃} =
Q_{n+4} + Q_{n+2} - T_{n+5} + F_{n+3}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 26. -/
theorem_wanted compProdSum_fib_trib_tetra (n : ℕ) :
    compProdSum (fun i k => ![fibStep 2, fibStep 3, fibStep 4] i k) n =
      fibStep 4 (n + 4) + fibStep 4 (n + 2) - fibStep 3 (n + 5) +
        fibStep 2 (n + 3)

/-- **Theorem 27**: for `n ≥ 7`,
`2 ∑_{K(3,n-7)} T_{k₁} Q_{k₂} P_{k₃} =
P_n + P_{n-2} + P_{n-4} + T_n - T_{n-2} - 2Q_n` (printed
with a factor `1/2`).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 27. -/
theorem_wanted two_mul_compProdSum_trib_tetra_penta (n : ℕ)
    (hn : 7 ≤ n) :
    2 * compProdSum
        (fun i k => ![fibStep 3, fibStep 4, fibStep 5] i k) (n - 7) =
      fibStep 5 n + fibStep 5 (n - 2) + fibStep 5 (n - 4) +
        fibStep 3 n - fibStep 3 (n - 2) - 2 * fibStep 4 n

/-- **Theorem 28**:
`2 ∑_{K(3,n-5)} F_{k₁} Q_{k₂} P_{k₃} =
-2Q_n - 2Q_{n-2} + P_{n+1} + P_{n-2} - F_{n+1} + 2F_n`
(printed with a factor `1/2` on part of the right side).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 28. -/
theorem_wanted two_mul_compProdSum_fib_tetra_penta (n : ℕ)
    (hn : 5 ≤ n) :
    2 * compProdSum
        (fun i k => ![fibStep 2, fibStep 4, fibStep 5] i k) (n - 5) =
      -2 * fibStep 4 n - 2 * fibStep 4 (n - 2) +
        fibStep 5 (n + 1) + fibStep 5 (n - 2) - fibStep 2 (n + 1) +
        2 * fibStep 2 n

/-- **Theorem 29**:
`2 ∑_{K(3,n-5)} F_{k₁} T_{k₂} P_{k₃} =
P_n - P_{n-1} + P_{n-2} - T_n - T_{n-2} + F_{n-1}`
(printed with a factor `1/2`).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 29. -/
theorem_wanted two_mul_compProdSum_fib_trib_penta (n : ℕ)
    (hn : 5 ≤ n) :
    2 * compProdSum
        (fun i k => ![fibStep 2, fibStep 3, fibStep 5] i k) (n - 5) =
      fibStep 5 n - fibStep 5 (n - 1) + fibStep 5 (n - 2) -
        fibStep 3 n - fibStep 3 (n - 2) + fibStep 2 (n - 1)

/-- **Theorem 31** (generating functions):
`X^{2m+1} F^{(m)} F^{(m+1)} F^{(m+2)} F^{(m+3)} =
X^m F^{(m)} F^{(m+2)} F^{(m+3)} - F^{(m+1)} F^{(m+3)} +
F^{(m)} F^{(m+3)}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 31. -/
theorem_wanted fibStepGF_quadruple_consecutive (m : ℕ)
    (hm : 1 ≤ m) :
    PowerSeries.X ^ (2 * m + 1) * fibStepGF m * fibStepGF (m + 1) *
        fibStepGF (m + 2) * fibStepGF (m + 3) =
      PowerSeries.X ^ m * fibStepGF m * fibStepGF (m + 2) *
          fibStepGF (m + 3) -
        fibStepGF (m + 1) * fibStepGF (m + 3) +
        fibStepGF m * fibStepGF (m + 3)

/-- **Theorem 32**:
`2 ∑_{K(4,n-5)} F_{k₁} T_{k₂} Q_{k₃} P_{k₄} =
P_{n+4} - P_{n+3} + P_{n+2} + T_{n+3} + T_{n+1} - F_n -
2Q_{n+3} - 2Q_{n+1}` (printed with a factor `1/2`).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 32. -/
theorem_wanted two_mul_compProdSum_four (n : ℕ) (hn : 5 ≤ n) :
    2 * compProdSum (fun i k => ![fibStep 2, fibStep 3,
        fibStep 4, fibStep 5] i k) (n - 5) =
      fibStep 5 (n + 4) - fibStep 5 (n + 3) + fibStep 5 (n + 2) +
        fibStep 3 (n + 3) + fibStep 3 (n + 1) - fibStep 2 n -
        2 * fibStep 4 (n + 3) - 2 * fibStep 4 (n + 1)

/-- **Theorem 34** (index typo corrected):
`∑_{K(4,n-2m-2)} F⁽ᵐ⁾_{k₁} F⁽ᵐ⁺¹⁾_{k₂} F⁽ᵐ⁺²⁾_{k₃}
F⁽ᵐ⁺³⁾_{k₄} = ∑_{j=0}^n (F⁽ᵐ⁺³⁾ⱼ - F⁽ᵐ⁺²⁾ⱼ)
(F⁽ᵐ⁺¹⁾_{n-j} - F⁽ᵐ⁾_{n-j})` (printed with `k_3` repeated
for `k_4`).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 34. -/
theorem_wanted compProdSum_four_consecutive (m n : ℕ)
    (hm : 1 ≤ m) (hn : 2 * m + 2 ≤ n) :
    compProdSum (fun i k => ![fibStep m, fibStep (m + 1),
        fibStep (m + 2), fibStep (m + 3)] i k) (n - 2 * m - 2) =
      ∑ j ∈ Finset.range (n + 1),
        (fibStep (m + 3) j - fibStep (m + 2) j) *
          (fibStep (m + 1) (n - j) - fibStep m (n - j))

/-- **Theorem 35**, even case: for `ℓ ≥ 1`,
`∑_{K(2ℓ, n-ℓ(m+ℓ-1))} ∏_{j=0}^{2ℓ-1} F^{(m+j)}_{k_{j+1}}
= ∑_{K(ℓ, n)} ∏_{j=0}^{ℓ-1}
(F^{(m+2j+1)}_{k_{j+1}} - F^{(m+2j)}_{k_{j+1}})`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 35. -/
theorem_wanted compProdSum_even (l m n : ℕ) (hl : 1 ≤ l)
    (hm : 1 ≤ m) (hn : l * (m + l - 1) ≤ n) :
    @compProdSum (2 * l) (fun (j : Fin (2 * l)) k =>
        fibStep (m + j.val) k) (n - l * (m + l - 1)) =
      @compProdSum l (fun (j : Fin l) k =>
        fibStep (m + 2 * j.val + 1) k - fibStep (m + 2 * j.val) k) n

/-- **Theorem 35**, odd case: for `ℓ ≥ 1`,
`∑_{K(2ℓ+1, n-ℓ(m+ℓ-1))} ∏_{j=0}^{2ℓ} F^{(m+j)}_{k_{j+1}}
= ∑_{K(ℓ+1, n)} F^{(m+2ℓ)}_{k_{ℓ+1}}
∏_{j=0}^{ℓ-1} (F^{(m+2j+1)}_{k_{j+1}} -
F^{(m+2j)}_{k_{j+1}})`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 35. -/
theorem_wanted compProdSum_odd (l m n : ℕ) (hl : 1 ≤ l)
    (hm : 1 ≤ m) (hn : l * (m + l - 1) ≤ n) :
    @compProdSum (2 * l + 1) (fun (j : Fin (2 * l + 1)) k =>
        fibStep (m + j.val) k) (n - l * (m + l - 1)) =
      @compProdSum (l + 1) (fun (j : Fin (l + 1)) k =>
        if (j.val : ℕ) = l then fibStep (m + 2 * l) k
        else fibStep (m + 2 * j.val + 1) k -
          fibStep (m + 2 * j.val) k) n

/-- **Corollary 36**:
`∑_{K(3,n-2)} F_{k₁} T_{k₂} Q_{k₃} =
∑_{j=0}^n (T_j - F_j) Q_{n-j} =
∑_{j=0}^{n+1} F_{n+1-j} (Q_j - T_j)`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Corollary 36. -/
theorem_wanted compProdSum_fib_trib_tetra_eq (n : ℕ)
    (hn : 2 ≤ n) :
    compProdSum (fun i k => ![fibStep 2, fibStep 3, fibStep 4] i k)
          (n - 2) =
        ∑ j ∈ Finset.range (n + 1),
          (fibStep 3 j - fibStep 2 j) * fibStep 4 (n - j) ∧
      compProdSum (fun i k => ![fibStep 2, fibStep 3, fibStep 4] i k)
          (n - 2) =
        ∑ j ∈ Finset.range (n + 2),
          fibStep 2 (n + 1 - j) * (fibStep 4 j - fibStep 3 j)

/-- **Lemma 39**: for `m ≥ 2`,
`∑_{k=0}^{2m+1} F⁽ᵐ⁾_{n+k} = 4 F⁽ᵐ⁾_{n+2m}`.

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Lemma 39. -/
theorem_wanted sum_fibStep_window (m n : ℕ) (hm : 2 ≤ m) :
    ∑ k ∈ Finset.range (2 * m + 2), fibStep m (n + k) =
      4 * fibStep m (n + 2 * m)

/-- **Theorem 41**: with `s = F⁽⁶⁾`, for `n ≥ 3`,
`5 ∑_{j=0}^n s_j F_{n-j} =
s_{n+3} + s_{n+1} - s_n + 3s_{n-1} + s_{n-3} - F_{n+3} -
F_{n+1}` (printed with a factor `1/5`).

Source: Robert Frontczak and Karol Gryszka, "General
Convolution Sums Involving Fibonacci `m`-Step Numbers",
Theorem 41. -/
theorem_wanted five_mul_sum_fibStep6_mul_fib (n : ℕ)
    (hn : 3 ≤ n) :
    5 * ∑ j ∈ Finset.range (n + 1),
        fibStep 6 j * fibStep 2 (n - j) =
      fibStep 6 (n + 3) + fibStep 6 (n + 1) - fibStep 6 n +
        3 * fibStep 6 (n - 1) + fibStep 6 (n - 3) -
        fibStep 2 (n + 3) - fibStep 2 (n + 1)

end MathlibExt.Combinatorics.Enumerative.FibStepConvolutionWanted
