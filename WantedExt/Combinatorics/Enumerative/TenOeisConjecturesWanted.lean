/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Proofs of ten conjectures from the OEIS

Statements from Sela Fried, "Proofs of Ten Conjectures From the OEIS", *Journal of Integer
Sequences* 29 (2026), Article 26.1.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Fried/fried21.html>).

Stated: Lemma 1 (a binomial identity), Theorem 2 (a diagonal coefficient), Theorem 3
(triangular numbers near squares along `⌊n√2⌋`), Theorem 5 (arithmetic progressions of `[n]`),
Theorem 6 (digit insertion and the digit sum), Theorem 7 (a binomial sum modulo `4`), Theorem 8
(the Bala-Somos parity conjectures from A067567 and A305123), Lemmas 9-11 and Theorem 12 (the
ceiling of `cot (π / (2m))`), Theorem 13 (A285273), Theorem 14 and Corollary 15 (cevians), and
Theorem 16 and Corollaries 17 and 21 (intersections and regions in the two-fan construction).
Theorems 18 and 20 and Corollary 19 stay blocked (see the source audit table).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Nth
public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Topology.Connected.Clopen
public import MathlibExt.Combinatorics.AP.Basic

namespace MetaMathlibExt

open MvPolynomial

@[expose] public section

/-- For `0 ≤ r ≤ n` and `0 ≤ s ≤ 2r`,
`∑_{k=0}^{n} (-1)^k C(n,k) C(2n-2r, n-k) C(n-k, n-2r+s) C(2r-k-s, n-s)
= (-1)^n C(n, 2r-n) C(2n-2r, n-s)`, where `C(a, b)` is the binomial coefficient on integer
arguments, `0` when `a < 0` or `b < 0` (or `b > a`).

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Lemma 1 (`jis-2026-26.1.8-lem-1`). -/
public theorem_wanted fried_alternating_binomial_identity (n r s : ℕ) (hr : r ≤ n)
    (hs : s ≤ 2 * r) :
    let C : ℤ → ℤ → ℤ := fun a b => if 0 ≤ a ∧ 0 ≤ b then (a.toNat.choose b.toNat : ℤ) else 0
    ∑ k ∈ Finset.range (n + 1),
        (-1) ^ k * C n k * C (2 * n - 2 * r) (n - k) * C (n - k) (n - 2 * r + s) *
          C (2 * r - k - s) (n - s) =
      (-1) ^ n * C n (2 * r - n) * C (2 * n - 2 * r) (n - s)

/-- The Bala-Somos conjectures. Let `p(n)` be the number of partitions of `n`, let
`b_m(n) = ∑_{k=1}^{n} k^{2m+1} p(k) p(n-k)`, and let `a(n)` (A305123) have generating function
`(∑_{k ≥ 1} x^{2k-1}/(1 + x^{2k-1})) ∏_{k ≥ 1} 1/(1 - x^k)`, i.e.
`a(n) = ∑_{j=0}^{n} c(j) p(n-j)` with `c(j) = ∑_{d ∣ j, d odd} (-1)^{j/d - 1}` the `x^j`
coefficient of the first factor. Then for `m, n ≥ 1`: (a) if `n` is odd then `n ∣ b_m(n)`;
(b) `n ∣ b_m(2n)`, and `b_m(2n)/n` is odd iff `n` and `p(n)` are odd; (c) `a(n)` is odd iff `n`
and `p(n)` are odd; (d) `2(b_1(n)/n - ⌊b_1(n)/n⌋) = 1` iff `n` is even and `n/2` and
`p(n/2)` are odd (the paper calls the left side `c(n)`, a different sequence from the
coefficient `c(j)` above).

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 8 (`jis-2026-26.1.8-thm-8`). -/
public theorem_wanted bala_somos_partition_parity (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let p : ℕ → ℕ := fun k => Fintype.card (Nat.Partition k)
    let b : ℕ → ℕ → ℕ := fun m n => ∑ k ∈ Finset.Icc 1 n, k ^ (2 * m + 1) * p k * p (n - k)
    let a : ℕ → ℤ := fun n => ∑ j ∈ Finset.range (n + 1),
      (∑ d ∈ j.divisors.filter Odd, (-1 : ℤ) ^ (j / d - 1)) * p (n - j)
    (Odd n → n ∣ b m n) ∧
      (n ∣ b m (2 * n) ∧ (Odd (b m (2 * n) / n) ↔ Odd n ∧ Odd (p n))) ∧
      (Odd (a n) ↔ Odd n ∧ Odd (p n)) ∧
      (2 * Int.fract ((b 1 n : ℚ) / n) = 1 ↔ Even n ∧ Odd (n / 2) ∧ Odd (p (n / 2)))

/-- The diagonal coefficient of `F_n(x, y, z) = (1 + x + y - z)^n (1 + x - y + z)^n (1 - x + y + z)^n`:
`[x^n y^n z^n] F_n = (-1)^n ∑_{k=0}^{n} C(n,k)^3` (A000172), with `x, y, z` the variables
`X 0, X 1, X 2` of `MvPolynomial (Fin 3) ℤ`.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 2 (`jis-2026-26.1.8-thm-2`). -/
public theorem_wanted coeff_diag_trinomial_product_eq_franel (n : ℕ) :
    (((1 + X 0 + X 1 - X 2 : MvPolynomial (Fin 3) ℤ) ^ n * (1 + X 0 - X 1 + X 2) ^ n *
        (1 - X 0 + X 1 + X 2) ^ n).coeff (Finsupp.equivFunOnFinite.symm fun _ => n)) =
      (-1) ^ n * ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℤ)) ^ 3

/-- With `a_n = ⌊n√2⌋` (A001951) and `T_a = a(a+1)/2`, some square `k^2`, `k ∈ ℤ`, satisfies
`|T_{a_n} - k^2| ≤ ⌊a_n / 2⌋`; that is, `min_{k ∈ ℤ} |T_{a_n} - k^2| ≤ ⌊a_n / 2⌋`.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 3 (`jis-2026-26.1.8-thm-3`). -/
public theorem_wanted exists_sq_near_triangular_beatty_sqrt_two (n : ℕ) :
    let a : ℕ := ⌊(n : ℝ) * Real.sqrt 2⌋₊
    ∃ k : ℤ, |((a * (a + 1) / 2 : ℕ) : ℤ) - k ^ 2| ≤ (a / 2 : ℕ)

/-- For `n ≥ 1`, the number of arithmetic progressions in `[n] = {1, …, n}` of length at least `2`
(A078567), counted as subsets `S ⊆ [n]` with `#S ≥ 2` of the form `{a, a + d, …, a + (#S - 1)d}`
with `d ≥ 1` (`Set.IsAPOfLengthWith`), equals `∑_{m=0}^{n-1} D(m)` with
`D(m) = ∑_{k=1}^{m} ⌊m/k⌋` (A006218).

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 5 (`jis-2026-26.1.8-thm-5`). -/
public theorem_wanted ncard_arithProg_eq_sum_divisorSummatory (n : ℕ) (hn : 1 ≤ n) :
    {S : Finset ℕ | S ⊆ Finset.Icc 1 n ∧ 2 ≤ S.card ∧
        ∃ a d : ℕ, 1 ≤ d ∧ (S : Set ℕ).IsAPOfLengthWith S.card a d}.ncard =
      ∑ m ∈ Finset.range n, ∑ k ∈ Finset.Icc 1 m, m / k

/-- For `n ≥ 1`, let `S(n)` be the set of numbers obtained by inserting one decimal digit
`x ∈ {0, …, 9}` at any position of the decimal expansion of `n` (before, between or after its
digits), a leading `0` being prohibited. The position of `10n` in `S(n)` listed increasingly
(1-based), i.e. the number of elements of `S(n)` that are `≤ 10n`, equals the digit sum of `n`
(A007953). Digits are Mathlib's little-endian `Nat.digits 10 n`; inserting `x` at index `i`
gives it weight `10^i`, and index `(Nat.digits 10 n).length` with `x = 0` is the excluded leading
zero.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 6 (`jis-2026-26.1.8-thm-6`). -/
public theorem_wanted card_digitInsertion_le_ten_mul_eq_digitSum (n : ℕ) (hn : 1 ≤ n) :
    let L := Nat.digits 10 n
    let S : Finset ℕ := (((Finset.range (L.length + 1)) ×ˢ Finset.range 10).filter
        fun p => ¬(p.1 = L.length ∧ p.2 = 0)).image fun p => Nat.ofDigits 10 (L.insertIdx p.1 p.2)
    (S.filter (· ≤ 10 * n)).card = L.sum

/-- Let `a(n) = ∑_{k=0}^{n} C(2n+1, n+k+1) (-2)^k`. If `a(n)` is odd then `a(n) ≡ 1 (mod 4)`.
The paper's `a(n)` is A026641 (the number of even-outdegree nodes in all ordered trees with
`n` edges); its proof works with this binomial sum (Bala's formula, display (13)), which is
taken as the definition here.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 7 (`jis-2026-26.1.8-thm-7`). -/
public theorem_wanted bala_binomial_sum_odd_imp_mod_four (n : ℕ)
    (h : Odd (∑ k ∈ Finset.range (n + 1), ((2 * n + 1).choose (n + k + 1) : ℤ) * (-2) ^ k)) :
    (∑ k ∈ Finset.range (n + 1), ((2 * n + 1).choose (n + k + 1) : ℤ) * (-2) ^ k) % 4 = 1

/-- Let `g(m) = ⌈cot (π / (2m))⌉` for `m ≥ 1`. Then `g` is nondecreasing on `m ≥ 1`, each step
`g(m+1) - g(m)` is `0` or `1`, and every `n ≥ 1` is attained `g(m) = n` by one or two `m ≥ 1`.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Lemma 9 (`jis-2026-26.1.8-lem-9`). -/
public theorem_wanted ceil_cot_pi_div_two_mul_steps :
    let g : ℕ → ℤ := fun m => ⌈Real.cot (Real.pi / (2 * m))⌉
    (∀ m, 1 ≤ m → g m ≤ g (m + 1)) ∧ (∀ m, 1 ≤ m → g (m + 1) - g m ∈ ({0, 1} : Set ℤ)) ∧
      ∀ n : ℕ, 1 ≤ n → {m : ℕ | 1 ≤ m ∧ g m = n}.ncard ∈ ({1, 2} : Set ℕ)

/-- With `g(m) = ⌈cot (π / (2m))⌉`, `mult(j) = #{m ≥ 1 : g(m) = j}`, and `s(r)` the number of
`j ∈ [r]` with `mult(j) = 1` (singletons), for `r ≥ 1`: `#{m ≥ 2 : g(m) ≤ r} = 2r - s(r)`.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Lemma 10 (`jis-2026-26.1.8-lem-10`). -/
public theorem_wanted ncard_ceil_cot_le_eq_two_mul_sub_singletons (r : ℕ) (hr : 1 ≤ r) :
    let g : ℕ → ℤ := fun m => ⌈Real.cot (Real.pi / (2 * m))⌉
    let mult : ℕ → ℕ := fun j => {m : ℕ | 1 ≤ m ∧ g m = j}.ncard
    {m : ℕ | 2 ≤ m ∧ g m ≤ r}.ncard = 2 * r - ((Finset.Icc 1 r).filter fun j => mult j = 1).card

/-- With `g(m) = ⌈cot (π / (2m))⌉`, for `r ≥ 1` and `m ≥ 2`: `m` is the only `m' ≥ 1` with
`g(m') = r` (so `r` is a singleton) if and only if `g(m-1) = r-1`, `g(m) = r` and
`g(m+1) = r+1`.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Lemma 11 (`jis-2026-26.1.8-lem-11`). -/
public theorem_wanted ceil_cot_singleton_iff (r m : ℕ) (hr : 1 ≤ r) (hm : 2 ≤ m) :
    let g : ℕ → ℤ := fun m => ⌈Real.cot (Real.pi / (2 * m))⌉
    {m' : ℕ | 1 ≤ m' ∧ g m' = r} = {m} ↔
      g (m - 1) = (r : ℤ) - 1 ∧ g m = r ∧ g (m + 1) = (r : ℤ) + 1

/-- Jeffery's conjecture (A223577, A223578). Let `f(m) = ⌊cot (π / (2m))⌋` for integers `m ≠ 0`,
let `a(n)` list increasingly the `k ≥ 1` for which exactly one `m ≥ 2` has `-k = f(-m)`, and let
`b(n)` list increasingly the `k ≥ 2` with `f(-k-1) < f(-k) < f(-k+1)`. Then for `n ≥ 1`,
`a(n) = (b(n) + n - 1) / 2`, stated as `2 a(n) = b(n) + n - 1`, with `a(n)`, `b(n)` as
`Nat.nth _ (n - 1)`.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 12 (`jis-2026-26.1.8-thm-12`). -/
public theorem_wanted jeffery_floor_cot_singletons (n : ℕ) (hn : 1 ≤ n) :
    let f : ℤ → ℤ := fun m => ⌊Real.cot (Real.pi / (2 * m))⌋
    let A : ℕ → Prop := fun k => 1 ≤ k ∧ ∃! m : ℕ, 2 ≤ m ∧ -(k : ℤ) = f (-(m : ℤ))
    let B : ℕ → Prop := fun k => 2 ≤ k ∧ f (-(k : ℤ) - 1) < f (-(k : ℤ)) ∧ f (-(k : ℤ)) < f (-(k : ℤ) + 1)
    2 * Nat.nth A (n - 1) = Nat.nth B (n - 1) + n - 1

/-- For `n ≥ 1`, the number of `x` with exactly `n + 1` decimal digits for which some natural
`k` satisfies `x ≤ k < 2x` and `k / x = 1 + (x - 10^n) / (10^n - 1)` (A285273) equals
`2^ω(10^n - 1)`, where `ω` counts distinct prime factors.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 13 (`jis-2026-26.1.8-thm-13`). -/
public theorem_wanted ncard_repeating_decimal_ratio_eq_two_pow_omega (n : ℕ) (hn : 1 ≤ n) :
    {x : ℕ | 10 ^ n ≤ x ∧ x < 10 ^ (n + 1) ∧ ∃ k : ℕ, x ≤ k ∧ k < 2 * x ∧
        (k : ℚ) / x = 1 + ((x : ℚ) - 10 ^ n) / (10 ^ n - 1)}.ncard =
      2 ^ ArithmeticFunction.cardDistinctFactors (10 ^ n - 1)

/-- Zakharov's conjecture (A007980). In a nondegenerate triangle `ABC` in `ℝ × ℝ`, a cevian is a
segment from a vertex to a point of the open opposite side; the regions cut out by cevians
`c_1, …, c_n` are the connected components of the interior of the triangle minus their union.
The maximum number of regions over all choices of `n` cevians is `⌈(n + 1)(n + 2) / 3⌉`.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 14 (`jis-2026-26.1.8-thm-14`). -/
public theorem_wanted cevian_max_regions (A B C : ℝ × ℝ) (hT : AffineIndependent ℝ ![A, B, C])
    (n : ℕ) :
    let T := convexHull ℝ {A, B, C}
    let IsCevian : Set (ℝ × ℝ) → Prop := fun c =>
      (∃ P ∈ openSegment ℝ B C, c = segment ℝ A P) ∨ (∃ P ∈ openSegment ℝ C A, c = segment ℝ B P) ∨
        ∃ P ∈ openSegment ℝ A B, c = segment ℝ C P
    IsGreatest {r : ℕ | ∃ c : Fin n → Set (ℝ × ℝ), (∀ i, IsCevian (c i)) ∧
        Nat.card (ConnectedComponents ↥(interior T \ ⋃ i, c i)) = r}
      ⌈((n + 1) * (n + 2) : ℚ) / 3⌉₊

/-- Zakharov's conjecture (A000212). In the setting of `cevian_max_regions`, if `n` cevians cut
the triangle into the maximum number `⌈(n + 1)(n + 2) / 3⌉` of regions, then the number of
interior points of the triangle lying on two of the cevians is `⌊n^2 / 3⌋`.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Corollary 15 (`jis-2026-26.1.8-cor-15`). -/
public theorem_wanted cevian_max_regions_intersection_count (A B C : ℝ × ℝ)
    (hT : AffineIndependent ℝ ![A, B, C]) (n : ℕ) :
    let T := convexHull ℝ {A, B, C}
    let IsCevian : Set (ℝ × ℝ) → Prop := fun c =>
      (∃ P ∈ openSegment ℝ B C, c = segment ℝ A P) ∨ (∃ P ∈ openSegment ℝ C A, c = segment ℝ B P) ∨
        ∃ P ∈ openSegment ℝ A B, c = segment ℝ C P
    ∀ c : Fin n → Set (ℝ × ℝ), (∀ i, IsCevian (c i)) →
      Nat.card (ConnectedComponents ↥(interior T \ ⋃ i, c i)) = ⌈((n + 1) * (n + 2) : ℚ) / 3⌉₊ →
        {X | X ∈ interior T ∧ ∃ i j, i ≠ j ∧ X ∈ c i ∧ X ∈ c j}.ncard = n ^ 2 / 3

/-- Two-fan construction: from `P = (-1, 0)` draw the `m` rays at angles `π - 2πs/m`
(`0 ≤ s < m`) and from `Q = (1, 0)` the `n` rays at angles `2πt/n` (`0 ≤ t < n`). The number of
ray-ray intersection points, counting `P` and `Q`, is
`2 ∑_{s=1}^{⌊(m-1)/2⌋} ⌈ns/m - 1/2⌉ + 2` for odd `n` and
`2 ∑_{s=1}^{⌊(m-1)/2⌋} ⌈ns/m⌉ - 2⌊(m-1)/2⌋ + 2` for even `n`. The intersection points other
than `P` and `Q` are taken off the `x`-axis: on the axis, rays meet only at `P`, `Q` or along
overlapping segments, which the paper does not count.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Theorem 16 (`jis-2026-26.1.8-thm-16`). -/
public theorem_wanted two_fan_ray_intersection_count (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    let rayP : ℕ → Set (ℝ × ℝ) := fun s => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (-1 + r * Real.cos (Real.pi - 2 * Real.pi * s / m), r * Real.sin (Real.pi - 2 * Real.pi * s / m))}
    let rayQ : ℕ → Set (ℝ × ℝ) := fun t => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (1 + r * Real.cos (2 * Real.pi * t / n), r * Real.sin (2 * Real.pi * t / n))}
    let pts : Set (ℝ × ℝ) := {(-1, 0), (1, 0)} ∪
      {X | X.2 ≠ 0 ∧ ∃ s < m, ∃ t < n, X ∈ rayP s ∧ X ∈ rayQ t}
    (pts.ncard : ℤ) =
      if Odd n then 2 * ∑ s ∈ Finset.Icc 1 ((m - 1) / 2), ⌈(n * s : ℚ) / m - 1 / 2⌉ + 2
      else 2 * ∑ s ∈ Finset.Icc 1 ((m - 1) / 2), ⌈(n * s : ℚ) / m⌉ - 2 * ((m - 1) / 2 : ℕ) + 2

/-- Blomberg's conjecture (A338042): in the two-fan construction of
`two_fan_ray_intersection_count` with `m = n`, the number of ray-ray intersection points
(counting `P` and `Q`) is `(n^2 + 7)/4` for odd `n` and `(n^2 - 6n + 16)/4` for even `n`.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Corollary 17 (`jis-2026-26.1.8-cor-17`). -/
public theorem_wanted two_fan_ray_intersection_count_diag (n : ℕ) (hn : 1 ≤ n) :
    let rayP : ℕ → Set (ℝ × ℝ) := fun s => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (-1 + r * Real.cos (Real.pi - 2 * Real.pi * s / n), r * Real.sin (Real.pi - 2 * Real.pi * s / n))}
    let rayQ : ℕ → Set (ℝ × ℝ) := fun t => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (1 + r * Real.cos (2 * Real.pi * t / n), r * Real.sin (2 * Real.pi * t / n))}
    let pts : Set (ℝ × ℝ) := {(-1, 0), (1, 0)} ∪
      {X | X.2 ≠ 0 ∧ ∃ s < n, ∃ t < n, X ∈ rayP s ∧ X ∈ rayQ t}
    (pts.ncard : ℚ) = if Odd n then ((n : ℚ) ^ 2 + 7) / 4 else ((n : ℚ) ^ 2 - 6 * n + 16) / 4

/-- Blomberg's conjecture (A338041) for `n ≥ 3`: in the two-fan construction of
`two_fan_ray_intersection_count` with `m = n`, for every large enough radius `R`, the polygon
spanned by the points where the rays meet the circle `x^2 + y^2 = R^2` (their convex hull; the
points lie on the circle, so this is the paper's polygon joining consecutive points) is cut by the
rays into `(n^2 + 8n - 5)/4` regions for odd `n` and `(n^2 + 2n)/4` for even `n`; regions are the
connected components of the polygon's interior minus the rays.

Source: Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29
(2026), Article 26.1.8, Corollary 21 (`jis-2026-26.1.8-cor-21`). -/
public theorem_wanted two_fan_region_count_diag (n : ℕ) (hn : 3 ≤ n) :
    let rayP : ℕ → Set (ℝ × ℝ) := fun s => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (-1 + r * Real.cos (Real.pi - 2 * Real.pi * s / n), r * Real.sin (Real.pi - 2 * Real.pi * s / n))}
    let rayQ : ℕ → Set (ℝ × ℝ) := fun t => {X | ∃ r : ℝ, 0 ≤ r ∧
      X = (1 + r * Real.cos (2 * Real.pi * t / n), r * Real.sin (2 * Real.pi * t / n))}
    let rays : Set (ℝ × ℝ) := (⋃ s ∈ Finset.range n, rayP s) ∪ ⋃ t ∈ Finset.range n, rayQ t
    ∃ R₀ : ℝ, ∀ R ≥ R₀,
      (Nat.card (ConnectedComponents
          ↥(interior (convexHull ℝ {X | X.1 ^ 2 + X.2 ^ 2 = R ^ 2 ∧ X ∈ rays}) \ rays)) : ℚ) =
        if Odd n then ((n : ℚ) ^ 2 + 8 * n - 5) / 4 else ((n : ℚ) ^ 2 + 2 * n) / 4

end

end MetaMathlibExt
