/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Proofs of several conjectures from the OEIS

Statements from Sela Fried, "Proofs of Several
Conjectures From the OEIS", *Journal of Integer
Sequences* 28 (2025), Article 25.4.3
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Fried/fried15.html>).

`avoidZZ1Z k n` counts words of length `n` over a
`k`-letter alphabet with no consecutive pattern
`z, z+1, z`; the recurrence and initial values were
verified by brute force for `k ≤ 4`, `n ≤ 7`. The
bit-length formula was verified for `n ≤ 8`, and the
cube-root floor formula at `n = 3`.

Theorem 1, Corollary 2, Theorem 4, Theorem 8 and
Theorem 9 were added from the journal PDF and checked
by exact brute force (see the source audit table).
Theorem 4's generating function has constant term
`1 = f_k(0)` (the empty word), so it is stated as a
series identity from `n = 0`. Theorem 9 is false as printed (its condition
does not involve `a_n` and omits distinctness) and is
stated in the reading its proof uses. Not stated:
Corollary 5 (a claim about OEIS conjectures that the
paper does not state).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Fintype.Pi
public import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.OeisConjecturesWanted

/-- The number of words of length `n` over the alphabet
`Fin k` avoiding the consecutive pattern `z, z+1, z`:
there is no position `i` with `w (i+2) = w i` and
`w (i+1) = w i + 1` in value. -/
def avoidZZ1Z (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin k)).filter (fun w =>
    ∀ i : Fin n, ∀ h1 : (i : ℕ) + 1 < n,
      ∀ h2 : (i : ℕ) + 2 < n,
        ¬ (w ⟨(i : ℕ) + 2, h2⟩ = w i ∧
          (w ⟨(i : ℕ) + 1, h1⟩ : ℕ) = (w i : ℕ) + 1))).card

/-- **Theorem 3**: the numbers `f_k(n)` of words of
length `n` over a `k`-letter avoiding the pattern
`z, z+1, z` satisfy `f_k(0) = 1`, `f_k(1) = k`,
`f_k(2) = k^2`, and, for `n ≥ 3`,
`f_k(n) = k f_k(n-1) - f_k(n-2) + f_k(n-3)`. The
alphabet is nonempty (`k ≥ 1`); at `k = 0` the recurrence
would read `0 = 1` at `n = 3`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 3. -/
theorem_wanted avoidZZ1Z_spec (k : ℕ) (hk : 1 ≤ k) :
    avoidZZ1Z k 0 = 1 ∧ avoidZZ1Z k 1 = k ∧
      avoidZZ1Z k 2 = k ^ 2 ∧
      ∀ n : ℕ, 3 ≤ n →
        (avoidZZ1Z k n : ℤ) =
          (k : ℤ) * avoidZZ1Z k (n - 1) -
            avoidZZ1Z k (n - 2) + avoidZZ1Z k (n - 3)

/-- **Theorem 6**: the number of binary bits required to
represent `C(2^n, 2^{n-1})` is `2^n - ⌊n / 2⌋`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 6. -/
theorem_wanted size_choose_two_pow (n : ℕ) (hn : 1 ≤ n) :
    Nat.size (Nat.choose (2 ^ n) (2 ^ (n - 1))) =
      2 ^ n - n / 2

/-- **Theorem 7**: for `n` divisible by `3`, writing
`n = 3m`,
`⌊∑_{i=1}^{10^n} i^{1/3}⌋
  = 3 * 10^{4m} / 4 + 5 * 10^{m-1} - 1`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Theorem 7. -/
theorem_wanted floor_sum_cbrt (m : ℕ) (hm : 1 ≤ m) :
    Nat.floor (∑ i ∈ Finset.Icc (1 : ℕ) (10 ^ (3 * m)),
        (i : ℝ) ^ (1 / 3 : ℝ)) =
      3 * 10 ^ (4 * m) / 4 + 5 * 10 ^ (m - 1) - 1

/-- `b_{n,k}^{(m)}`: the number of integer points
`(x_1, …, x_m)` with `max |x_i| ≤ k` and
`∑ |x_i| = n`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Section 2. -/
def latticeCountEq (m k n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin m => Finset.Icc (-(k : ℤ)) k).filter
    (fun x => ∑ i, |x i| = (n : ℤ))).card

/-- `a_{n,k}^{(m)}`: the number of integer points
`(x_1, …, x_m)` with `max |x_i| ≤ k` and
`∑ |x_i| ≤ n`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Section 2. -/
def latticeCountLe (m k n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin m => Finset.Icc (-(k : ℤ)) k).filter
    (fun x => ∑ i, |x i| ≤ (n : ℤ))).card

/-- `b_{1,1}^{(2)} = 4`: the points `(±1, 0)`,
`(0, ±1)`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Section 2. -/
theorem latticeCountEq_two_one_one : latticeCountEq 2 1 1 = 4 := by
  decide +kernel

/-- `a_{1,1}^{(3)} = 7`: the origin and the six unit
vectors `±e_i`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Section 2. -/
theorem latticeCountLe_three_one_one : latticeCountLe 3 1 1 = 7 := by
  decide +kernel

/-- **Theorem 1**: the generating function of
`b_{n,k}^{(m)}` in `n` is
`B_k^{(m)}(x) = (1 + 2x(1 - x^k)/(1 - x))^m`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Theorem 1. -/
theorem_wanted latticeCountEq_genFun (m k : ℕ) :
    PowerSeries.mk (fun n => (latticeCountEq m k n : ℚ)) =
      (1 + 2 * PowerSeries.X * (1 - PowerSeries.X ^ k) *
        (1 - PowerSeries.X : PowerSeries ℚ)⁻¹) ^ m

/-- **Corollary 2**: `3 a_{n,k}^{(3)}` equals
`4n^3 + 6n^2 + 8n + 3` for `0 ≤ n < k`;
`12k^3 - 36k^2n + 36kn^2 - 8n^3 + 6n^2 + 6k + 2n + 3`
for `k ≤ n < 2k`;
`-84k^3 + 108k^2n - 36kn^2 + 4n^3 - 72k^2 + 72nk
  - 12n^2 - 6k + 8n + 3` for `2k ≤ n < 3k`; and
`24k^3 + 36k^2 + 18k + 3` otherwise.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Corollary 2. -/
theorem_wanted latticeCountLe_three (k n : ℕ) :
    3 * (latticeCountLe 3 k n : ℤ) =
      if n < k then 4 * (n : ℤ) ^ 3 + 6 * n ^ 2 + 8 * n + 3
      else if n < 2 * k then
        12 * (k : ℤ) ^ 3 - 36 * k ^ 2 * n + 36 * k * n ^ 2 - 8 * n ^ 3 +
          6 * n ^ 2 + 6 * k + 2 * n + 3
      else if n < 3 * k then
        -84 * (k : ℤ) ^ 3 + 108 * k ^ 2 * n - 36 * k * n ^ 2 + 4 * n ^ 3 -
          72 * k ^ 2 + 72 * n * k - 12 * n ^ 2 - 6 * k + 8 * n + 3
      else 24 * (k : ℤ) ^ 3 + 36 * k ^ 2 + 18 * k + 3

/-- The number `f_k(n)` of words `w` of length `n` over
a `k`-letter alphabet in which no repeating letter
equals the previous repeating letter: whenever
`w_i = w_{i+1} = w_j = w_{j+1}` with `i < j`, some
`i < m < j` has `w_m = w_{m+1} ≠ w_i` (positions
`0`-based).

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Section 3.2. -/
def restrictedRepeatCount (k n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin k)).filter (fun w =>
    ∀ i j : Fin n, ∀ hi : (i : ℕ) + 1 < n, ∀ hj : (j : ℕ) + 1 < n,
      i < j → w i = w ⟨(i : ℕ) + 1, hi⟩ → w j = w i →
        w ⟨(j : ℕ) + 1, hj⟩ = w i →
        ∃ m : Fin n, ∃ hm : (m : ℕ) + 1 < n, i < m ∧ m < j ∧
          w m = w ⟨(m : ℕ) + 1, hm⟩ ∧ w m ≠ w i)).card

/-- Over two letters, `f_2(3) = 6`: of the `8` words,
`111` and `222` are illegal.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Section 3.2. -/
theorem restrictedRepeatCount_two_three : restrictedRepeatCount 2 3 = 6 := by
  decide +kernel

/-- **Theorem 4**: the generating function of `f_k(n)`
is
`F_k(x) = -((k-2)x^3 + 2(k-2)x^2 + (k-3)x - 1) /
  (2(k-1)^2 x^3 + (k-1)(k-4)x^2 + (3-2k)x + 1)`.
The paper indexes the sequence from `n ≥ 1`; the
constant term `1` of `F_k` is `f_k(0)` (the empty word),
so the identity holds from `n = 0`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Theorem 4. -/
theorem_wanted restrictedRepeatCount_genFun (k : ℕ) :
    PowerSeries.mk (fun n => (restrictedRepeatCount k n : ℚ)) =
      -(PowerSeries.C ((k : ℚ) - 2) * PowerSeries.X ^ 3 +
          PowerSeries.C (2 * ((k : ℚ) - 2)) * PowerSeries.X ^ 2 +
          PowerSeries.C ((k : ℚ) - 3) * PowerSeries.X - 1) *
        (PowerSeries.C (2 * ((k : ℚ) - 1) ^ 2) * PowerSeries.X ^ 3 +
          PowerSeries.C (((k : ℚ) - 1) * ((k : ℚ) - 4)) * PowerSeries.X ^ 2 +
          PowerSeries.C (3 - 2 * (k : ℚ)) * PowerSeries.X + 1)⁻¹

/-- Source-local helper for Theorem 8, not a general
median API (it lives in this paper's namespace; the
repository's canonical median is the measure-theoretic
`ProbabilityTheory.IsMedian`): the median of a finite list of
rationals, counted with multiplicity, i.e. the middle
element of the sorted list for odd length and the mean of
the two middle elements for even length (`0` for the
empty list). It depends only on the multiset of entries
(`listMedian_perm`).

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Section 5 (the median used in the
median absolute deviation, Hoaglin, Mosteller and
Tukey, p. 291). -/
def listMedian (l : List ℚ) : ℚ :=
  let s := l.insertionSort (· ≤ ·)
  (s.getD ((s.length - 1) / 2) 0 + s.getD (s.length / 2) 0) / 2

/-- `listMedian` depends only on the multiset of entries.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Section 5 (median of a multiset). -/
theorem listMedian_perm {l l' : List ℚ} (h : l.Perm l') :
    listMedian l = listMedian l' := by
  have : l.insertionSort (· ≤ ·) = l'.insertionSort (· ≤ ·) :=
    List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ => le_antisymm h₁ h₂)
      (List.pairwise_insertionSort _ _) (List.pairwise_insertionSort _ _)
      ((List.perm_insertionSort _ l).trans (h.trans (List.perm_insertionSort _ l').symm))
  simp only [listMedian, this]

/-- The median of a one-element list is its entry.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Section 5. -/
theorem listMedian_singleton (a : ℚ) : listMedian [a] = a := by
  simp [listMedian]

/-- `median {1, 9, 4} = 4`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Section 5. -/
theorem listMedian_odd_example : listMedian [1, 9, 4] = 4 := by
  norm_num [listMedian, List.insertionSort_cons, List.orderedInsert_cons]

/-- `median {16, 1, 9, 4} = 13/2`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Section 5. -/
theorem listMedian_even_example : listMedian [16, 1, 9, 4] = 13 / 2 := by
  norm_num [listMedian, List.insertionSort_cons, List.orderedInsert_cons]

/-- **Theorem 8**: with `A_n = {k^2 : 1 ≤ k ≤ n}` and
`a_n = median(|x - median(A_n)| : x ∈ A_n)` its median
absolute deviation (deviations counted with
multiplicity), `a_n / n^2 → √3 / 8`.

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Theorem 8. -/
theorem_wanted tendsto_medianAbsDev_squares :
    Filter.Tendsto
      (fun n : ℕ =>
        ((listMedian ((List.range n).map fun k =>
            |((k + 1 : ℕ) : ℚ) ^ 2 -
              listMedian ((List.range n).map fun j => ((j + 1 : ℕ) : ℚ) ^ 2)|) : ℚ) : ℝ) /
          (n : ℝ) ^ 2)
      Filter.atTop (nhds (Real.sqrt 3 / 8))

/-- **Theorem 9** (corrected reading): let `a_1 = 1`
and, for `n ≥ 2`, let `a_n` be the least positive
integer distinct from `a_1, …, a_{n-1}` such that the
average of `a_1, …, a_n` is a power of `2`. Then
`a_n = (n + 1) 2^{n/2 - 1}` for even `n` and
`a_n = 2^{(n-1)/2}` for odd `n`. As printed the
condition reads "the average of `a_1, …, a_{n-1}`" and
omits distinctness, which gives `a_2 = 1 ≠ 3`; the
proof uses `s_n = n 2^ℓ` and "the distinctness
condition".

Source: Sela Fried, "Proofs of Several Conjectures From
the OEIS", Journal of Integer Sequences 28 (2025),
Article 25.4.3, Theorem 9. -/
theorem_wanted greedy_powTwo_average (a : ℕ → ℕ) (h1 : a 1 = 1)
    (hgreedy : ∀ n, 2 ≤ n →
      IsLeast {x : ℕ | 0 < x ∧ (∀ i ∈ Finset.Icc 1 (n - 1), a i ≠ x) ∧
        ∃ ℓ : ℕ, (∑ i ∈ Finset.Icc 1 (n - 1), a i) + x = n * 2 ^ ℓ} (a n))
    (n : ℕ) (hn : 1 ≤ n) :
    a n = if Even n then (n + 1) * 2 ^ (n / 2 - 1) else 2 ^ ((n - 1) / 2)

end MathlibExt.NumberTheory.OeisConjecturesWanted
