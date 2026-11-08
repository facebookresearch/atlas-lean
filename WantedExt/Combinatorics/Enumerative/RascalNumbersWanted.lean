/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Two combinatorial interpretations of Rascal numbers

Statements from Amelia Gibbs and Brian K. Miceli, "Two
Combinatorial Interpretations of Rascal Numbers", *Journal
of Integer Sequences* 27 (2024), Article 24.8.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL27/Miceli/miceli9.html>;
arXiv:2405.11045).

The Rascal numbers `R_{n,k}` are defined in the paper by the
diamond recurrence of Angorro et al. together with the value
`0` outside `0 ≤ k ≤ n`; since Angorro et al. proved
`R_{n,k} = k(n-k) + 1` in range, `rascalZ` below is defined
directly by that closed form on `ℤ`. The paper's `B_k(n)`
(binary words of length `n` with exactly `k` ones and at most
one ascent) and its generalization `B_k^{(j)}(n)` (at most `j`
ascents) are the list subtypes `RascalWord 1 k n` and
`RascalWord j k n`, with counts `rascalGen j k n` (the
generalized Rascal numbers `R_{n,k}^{(j)}`), extended to `ℤ`
by `0` out of range as `rascalGenZ`. The paper's
`\mathcal{A}_{\{001,210\}}(n, k)` (ascent sequences of length
`n` avoiding the patterns `001` and `210`, with exactly `k`
ascents) is `AscentSeqAvoid n k` with count `apkCard`;
pattern containment is order-isomorphic subsequence
(`List.Sublist`) as in the paper.

Corrections to the printed statements, each found by brute
force and verified numerically: Fleron's recurrence
(Theorem 4) holds only for `0 < k < n` (at `k = 0` or `k = n`
the right side is `2`, not `1`); Theorem 6 as printed fails
for `k > n` and needs `k ≤ n`; Theorem 10 as printed has
`2^{n-2}` where the correct exponent is `n - 1` (at `n = 2`
the sum is `6`, the printed right side is `5`), stated below
doubled to avoid negative exponents; Theorem 19's summation
index is `i` (the printed binder is `r`), and it needs
`k ≤ n`; Theorem 23 uses the paper's convention
`\binom{-1}{j} = (-1)^j` at `n = 0`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

/-- The number of ascents of a word: positions `i` with
`w[i] < w[i+1]`. -/
def wordAscents : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a < b then 1 else 0) + wordAscents (b :: t)

/-- The paper's Rascal numbers `R_{n,k}` on `ℤ`, via the
closed form `k(n-k) + 1` in range and `0` outside. -/
def rascalZ (n k : ℤ) : ℤ :=
  if 0 ≤ k ∧ k ≤ n then k * (n - k) + 1 else 0

/-- The paper's `B_k^{(j)}(n)`: binary words of length `n`
with exactly `k` ones and at most `j` ascents. -/
def RascalWord (j k n : ℕ) : Type :=
  { w : List ℕ // w.length = n ∧ (∀ x ∈ w, x = 0 ∨ x = 1) ∧
      w.count 1 = k ∧ wordAscents w ≤ j }

/-- The paper's generalized Rascal numbers `R_{n,k}^{(j)}`. -/
noncomputable def rascalGen (j k n : ℕ) : ℕ :=
  Nat.card (RascalWord j k n)

/-- `R_{n,k}^{(j)}` on `ℤ`, extended by `0` outside
`0 ≤ k ≤ n` as in the paper. -/
noncomputable def rascalGenZ (j : ℕ) (n k : ℤ) : ℤ :=
  if 0 ≤ k ∧ k ≤ n then (rascalGen j k.toNat n.toNat : ℤ) else 0

/-- Ascent sequences: `w₁ = 0` and `wᵢ ≤ asc(w₁ ⋯ w_{i-1}) + 1`. -/
def IsAscentSeq (w : List ℕ) : Prop :=
  (∀ h : 0 < w.length, w[0]'h = 0) ∧
    ∀ (i : ℕ) (h : i < w.length), w[i]'h ≤ wordAscents (w.take i) + 1

/-- Avoiding the patterns `001` and `210`: no subsequence
`x, x, y` with `x < y` and no strictly decreasing subsequence
of length three. -/
def Avoids001210 (w : List ℕ) : Prop :=
  ∀ x y z : ℕ, List.Sublist [x, y, z] w →
    ¬ (x = y ∧ y < z) ∧ ¬ (z < y ∧ y < x)

/-- The paper's `\mathcal{A}_{\{001,210\}}(n, k)`: ascent
sequences of length `n` avoiding `001` and `210` with exactly
`k` ascents. -/
def AscentSeqAvoid (n k : ℕ) : Type :=
  { w : List ℕ // w.length = n ∧ IsAscentSeq w ∧ Avoids001210 w ∧
      wordAscents w = k }

/-- The count `|\mathcal{A}_{\{001,210\}}(n, k)|`. -/
noncomputable def apkCard (n k : ℕ) : ℕ :=
  Nat.card (AscentSeqAvoid n k)

/-- **Theorem 1**: `R_{n,k} = b_k(n)` for all integers
`n, k`, where `b_k(n) = |B_k(n)|` counts the binary words of
length `n` with exactly `k` ones and at most one ascent.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 1. -/
theorem_wanted rascalZ_eq_rascalGenZ_one (n k : ℤ) :
    rascalZ n k = rascalGenZ 1 n k

/-- **Theorem 2** (symmetry): `R_{n,k} = R_{n,n-k}` for
`0 ≤ k ≤ n`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 2. -/
theorem_wanted rascalZ_symm (n k : ℤ) (h0 : 0 ≤ k) (h1 : k ≤ n) :
    rascalZ n k = rascalZ n (n - k)

/-- **Lemma 3**: for `ℓ ≤ k` and `k + u ≤ n`,
`R_{n-u-ℓ,k-ℓ}` counts the words in `B_k(n)` that start with
at least `ℓ` ones and end with at least `u` zeros.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Lemma 3. -/
theorem_wanted card_prefixOnes_suffixZeros (n k ℓ u : ℕ)
    (hℓ : ℓ ≤ k) (hu : k + u ≤ n) :
    (Nat.card { w : RascalWord 1 k n //
        (∀ x ∈ w.1.take ℓ, x = 1) ∧
          (∀ x ∈ w.1.drop (n - u), x = 0) } : ℤ) =
      rascalZ (n - u - ℓ : ℕ) (k - ℓ : ℕ)

/-- **Theorem 4** (Fleron's recursion):
`R_{n,k} = R_{n-1,k} + R_{n-1,k-1} - R_{n-2,k-1} + 1`,
stated for `0 < k < n` since at `k = 0` or `k = n` the right
side equals `2` while `R_{n,k} = 1`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 4. -/
theorem_wanted rascalZ_fleron (n k : ℤ) (hn : 2 ≤ n)
    (hk0 : 0 < k) (hkn : k < n) :
    rascalZ n k = rascalZ (n - 1) k + rascalZ (n - 1) (k - 1) -
      rascalZ (n - 2) (k - 1) + 1

/-- **Theorem 5** (generalization of the diamond recurrence):
`R_{n,k} = (R_{n-u,k} R_{n-ℓ,k-ℓ} + uℓ) / R_{n-u-ℓ,k-ℓ}`,
written cross-multiplied to stay in `ℤ`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 5. -/
theorem_wanted rascalZ_mul_eq (n k ℓ u : ℤ) (hℓ : 0 ≤ ℓ)
    (hu : 0 ≤ u) (h : ℓ ≤ k) (h2 : k ≤ n - u) :
    rascalZ n k * rascalZ (n - u - ℓ) (k - ℓ) =
      rascalZ (n - u) k * rascalZ (n - ℓ) (k - ℓ) + u * ℓ

/-- **Theorem 6**: `R_{n+m,k} = R_{n,k} + R_{m+k,k} - 1`,
with the hypothesis `k ≤ n` that the printed statement
omits (without it, `R_{0+1,2} = 0 ≠ 0 + 3 - 1`).

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 6. -/
theorem_wanted rascalZ_add_eq (n m k : ℤ) (hm : 0 ≤ m)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) :
    rascalZ (n + m) k = rascalZ n k + rascalZ (m + k) k - 1

/-- **Theorem 7**: `k R_{n-1,k-1} - 1 = (k-1) R_{n,k}` for
`0 < k < n`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 7. -/
theorem_wanted mul_rascalZ_sub_one (n k : ℤ) (hk0 : 0 < k)
    (hkn : k < n) :
    k * rascalZ (n - 1) (k - 1) - 1 = (k - 1) * rascalZ n k

/-- **Theorem 8** (row sum):
`∑_{k=0}^n R_{n,k} = \binom{n+1}{3} + n + 1`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 8. -/
theorem_wanted sum_rascalZ_row (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), rascalZ (n : ℤ) (k : ℤ) =
      (Nat.choose (n + 1) 3 : ℤ) + (n : ℤ) + 1

/-- **Theorem 9** (column sum):
`∑_{i=0}^r R_{k+i,k} = k \binom{r+1}{2} + r + 1`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 9. -/
theorem_wanted sum_rascalZ_column (k r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), rascalZ ((k + i : ℕ) : ℤ) (k : ℤ) =
      (k : ℤ) * (Nat.choose (r + 1) 2 : ℤ) + (r : ℤ) + 1

/-- **Theorem 10** (binomial-weighted row sum):
`∑_{k=0}^n \binom{n}{k} R_{n,k} = 2^{n-1} \binom{n}{2} + 2^n`,
with the exponent corrected from the printed `n - 2` (at
`n = 2` the sum is `6`, not `5`), doubled to stay integral
at `n = 0`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 10. -/
theorem_wanted two_mul_sum_choose_mul_rascalZ (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℤ) * rascalZ (n : ℤ) (k : ℤ) =
      2 ^ n * (Nat.choose n 2 : ℤ) + 2 ^ (n + 1)

/-- **Theorem 11**:
`∑_{i=1}^n ∑_{j=1}^{i-1} R_{i,j} = \binom{n+2}{4} + \binom{n}{2}`
for `n ≥ 2`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 11. -/
theorem_wanted sum_sum_rascalZ (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, ∑ j ∈ Finset.Icc 1 (i - 1),
        rascalZ (i : ℤ) (j : ℤ) =
      (Nat.choose (n + 2) 4 : ℤ) + (Nat.choose n 2 : ℤ)

/-- **Theorem 12**:
`∑_{j=0}^r (-1)^{r-j} \binom{r}{j} R_{n+j,k} = 0` for
`0 ≤ k ≤ n` and `r ≥ 2` (the `r`-th finite difference of a
linear function of `n`).

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 12. -/
theorem_wanted sum_negOnePow_choose_rascalZ (n k r : ℕ)
    (hkn : k ≤ n) (hr : 2 ≤ r) :
    ∑ j ∈ Finset.range (r + 1),
        (-1 : ℤ) ^ (r - j) * (Nat.choose r j : ℤ) *
          rascalZ ((n + j : ℕ) : ℤ) (k : ℤ) = 0

/-- **Theorem 13** (alternating row sum, odd case):
`∑_{k=0}^{2m+1} (-1)^k R_{2m+1,k} = 0`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 13. -/
theorem_wanted sum_rascalZ_alternating_odd (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 2),
        (-1 : ℤ) ^ k * rascalZ ((2 * m + 1 : ℕ) : ℤ) (k : ℤ) = 0

/-- **Theorem 13** (alternating row sum, even case):
`∑_{k=0}^{2m} (-1)^k R_{2m,k} = 1 - m`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 13. -/
theorem_wanted sum_rascalZ_alternating_even (m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 1),
        (-1 : ℤ) ^ k * rascalZ ((2 * m : ℕ) : ℤ) (k : ℤ) =
      1 - (m : ℤ)

/-- **Theorem 14**, product as subset sum:
`∏_{k=1}^m (R_{n,k} - 1) = ∑_{S ⊆ [m]} (-1)^{m-|S|}
∏_{i ∈ S} R_{n,i}` for `1 ≤ m ≤ n`, with `[m] = {1, …, m}`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 14. -/
theorem_wanted prod_rascalZ_sub_one_eq_sum (n m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∏ k ∈ Finset.Icc 1 m, (rascalZ (n : ℤ) (k : ℤ) - 1) =
      ∑ S ∈ (Finset.Icc 1 m).powerset,
        (-1 : ℤ) ^ (m - S.card) *
          ∏ i ∈ S, rascalZ (n : ℤ) (i : ℤ)

/-- **Theorem 14**, closed form:
`∏_{k=1}^m (R_{n,k} - 1) = m! (n-1)↓_m` for `1 ≤ m ≤ n`,
where `↓` is the descending factorial.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 14. -/
theorem_wanted prod_rascalZ_sub_one_eq_factorial_mul (n m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    ∏ k ∈ Finset.Icc 1 m, (rascalZ (n : ℤ) (k : ℤ) - 1) =
      (m.factorial : ℤ) * (Nat.descFactorial (n - 1) m : ℤ)

/-- **Corollary 15**:
`(1/(m!)²) ∏_{k=1}^m (R_{n,k} - 1) = \binom{n-1}{m}` for
`1 ≤ m ≤ n`, written cross-multiplied to stay in `ℤ`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Corollary 15. -/
theorem_wanted factorial_sq_mul_choose_eq_prod (n m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    (m.factorial : ℤ) ^ 2 * (Nat.choose (n - 1) m : ℤ) =
      ∏ k ∈ Finset.Icc 1 m, (rascalZ (n : ℤ) (k : ℤ) - 1)

/-- **Lemma 16**: every `w ∈ \mathcal{A}_{\{001,210\}}(n, k)`
has the form `0 1 ⋯ (k-1) k^{n-k}`, or
`0 1 ⋯ (k-1) k^y x^{n-k-y}` with `1 ≤ y < n - k` and `x < k`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Lemma 16. -/
theorem_wanted ascentSeqAvoid_form (n k : ℕ)
    (w : AscentSeqAvoid n k) :
    w.1 = List.range k ++ List.replicate (n - k) k ∨
      ∃ y x : ℕ, 1 ≤ y ∧ y < n - k ∧ x < k ∧
        w.1 = List.range k ++ List.replicate y k ++
          List.replicate (n - k - y) x

/-- **Theorem 17**: `|\mathcal{A}_{\{001,210\}}(n+1, k)| =
R_{n,k}`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 17. -/
theorem_wanted apkCard_succ_eq_rascalZ (n k : ℕ) :
    (apkCard (n + 1) k : ℤ) = rascalZ (n : ℤ) (k : ℤ)

/-- **Theorem 18** (generalized Fleron's recurrence):
`R^{(j)}_{n,k} = R^{(j)}_{n-1,k} + R^{(j)}_{n-1,k-1} -
R^{(j)}_{n-2,k-1} + R^{(j-1)}_{n-2,k-1}` for `2 ≤ n`,
`0 ≤ k ≤ n`, and `1 ≤ j`, with the `ℤ`-extension by `0` out
of range handling the boundary values.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 18. -/
theorem_wanted rascalGenZ_fleron (j : ℕ) (hj : 1 ≤ j)
    (n k : ℤ) (hn : 2 ≤ n) (hk0 : 0 ≤ k) (hkn : k ≤ n) :
    rascalGenZ j n k = rascalGenZ j (n - 1) k +
      rascalGenZ j (n - 1) (k - 1) - rascalGenZ j (n - 2) (k - 1) +
      rascalGenZ (j - 1) (n - 2) (k - 1)

/-- **Theorem 19**: `R^{(j)}_{n,k} = ∑_{i=0}^j \binom{k}{i}
\binom{n-k}{i}` for `k ≤ n` (the printed summation binder is
`r` with summand in `i`; without `k ≤ n` the sum is `1` while
`R^{(j)}_{n,k} = 0`).

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 19. -/
theorem_wanted rascalGen_eq_sum (j n k : ℕ) (hkn : k ≤ n) :
    (rascalGen j k n : ℤ) =
      ∑ i ∈ Finset.range (j + 1),
        (Nat.choose k i : ℤ) * (Nat.choose (n - k) i : ℤ)

/-- **Theorem 20** (generalized row sum):
`∑_{k=0}^n R^{(j)}_{n,k} = ∑_{k=0}^{2j+1} \binom{n}{k}`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 20. -/
theorem_wanted sum_rascalGen_row (j n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (rascalGen j k n : ℤ) =
      ∑ k ∈ Finset.range (2 * j + 2), (Nat.choose n k : ℤ)

/-- **Corollary 21** (Conjecture 7.5 of Gregory et al.):
`∑_{k=0}^{4j+3} R^{(j)}_{4j+3,k} = 2^{4j+2}`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Corollary 21. -/
theorem_wanted sum_rascalGen_four_mul_add_three (j : ℕ) :
    ∑ k ∈ Finset.range (4 * j + 4),
        (rascalGen j k (4 * j + 3) : ℤ) = 2 ^ (4 * j + 2)

/-- **Corollary 22** (Theorem 7.3 of Gregory et al.): the
`(2j+1)`-st forward difference in `n` of the row sum
`∑_{k=0}^n R^{(j)}_{n,k}` is `1`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Corollary 22. -/
theorem_wanted iterate_forwardDiff_sum_rascalGen (j n : ℕ) :
    ((fun a : ℕ → ℤ => fun m => a (m + 1) - a m)^[2 * j + 1]
      (fun m => ∑ k ∈ Finset.range (m + 1),
        rascalGenZ j (m : ℤ) (k : ℤ))) n = 1

/-- **Theorem 23** (generalized alternating row sum, odd
case): `∑_{k=0}^{2m+1} (-1)^k R^{(j)}_{2m+1,k} = 0`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 23. -/
theorem_wanted sum_rascalGen_alternating_odd (j m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 2),
        (-1 : ℤ) ^ k * (rascalGen j k (2 * m + 1) : ℤ) = 0

/-- **Theorem 23** (generalized alternating row sum, even
case): `∑_{k=0}^{2m} (-1)^k R^{(j)}_{2m,k} =
(-1)^j \binom{m-1}{j}`, with the paper's convention
`\binom{-1}{j} = (-1)^j` at `m = 0`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 23. -/
theorem_wanted sum_rascalGen_alternating_even (j m : ℕ) :
    ∑ k ∈ Finset.range (2 * m + 1),
        (-1 : ℤ) ^ k * (rascalGen j k (2 * m) : ℤ) =
      (-1 : ℤ) ^ j *
        (if m = 0 then (-1 : ℤ) ^ j else (Nat.choose (m - 1) j : ℤ))

/-- **Theorem 24**: `R^{(j)}_{n,k}` equals the number of
`k`-element subsets of `{1, …, n}` whose intersection with
`{1, …, n-k}` contains at most `j` elements (the Gregory et
al. interpretation of `\binom{n}{k}_j`), here zero-based as
subsets of `Fin n` with at most `j` elements `< n - k`.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 24. -/
theorem_wanted rascalGen_eq_card_subset (j n k : ℕ) :
    rascalGen j k n =
      Nat.card { S : Finset (Fin n) // S.card = k ∧
        (S.filter (fun i => i.val < n - k)).card ≤ j }

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
