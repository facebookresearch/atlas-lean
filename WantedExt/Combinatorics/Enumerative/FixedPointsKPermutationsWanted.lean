/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fixed points in permutations with a given number of cycles

Statements from Moussa Benoumhani, *The Distribution of the Number of Fixed Points in
k-Permutations*, INTEGERS 24 (2024), Article A54.

A `k`-permutation of `[n]` is a permutation with exactly `k` cycles, fixed points counted as
one-cycles (the convention of `MetaMathlibExt.card_perm_cycleCount_eq_stirlingFirst`).
`kPermFixedPointCount n k j` is the paper's `a(n, k, j)`, the number of `k`-permutations of `[n]`
with exactly `j` fixed points; the paper's `c(n, k)` is `Nat.stirlingFirst n k`, and its
`d(n, k)` (derangements of `[n]` with `k` cycles) is `kPermFixedPointCount n k 0`, as forced by
Proposition 3 (i) at `j = 0`. The number of cycles is `MetaMathlibExt.cycleQuotientCount`.
"Has only real zeros" for `p : ℝ[X]` is `p.Splits` (equivalently
`Multiset.card p.roots = p.natDegree`, `Polynomial.splits_iff_card_roots`).
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import MathlibExt.Combinatorics.Enumerative.Stirling

namespace MetaMathlibExt

@[expose] public section

open Filter Polynomial Topology

/-- The number `a(n, k, j)` of permutations of `Fin n` with exactly `k` cycles (fixed points
counted as one-cycles) and exactly `j` fixed points.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (definition of `a(n, k, j)`). -/
public noncomputable def kPermFixedPointCount (n k j : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) //
    cycleQuotientCount σ = k ∧ Fintype.card (Function.fixedPoints σ) = j}

/-- A permutation with `k` cycles has at most `k` fixed points, so `a(n, k, j) = 0` for `k < j`.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (range `0 ≤ j ≤ k` of `a(n, k, j)`). -/
public theorem kPermFixedPointCount_eq_zero_of_lt {n k j : ℕ} (h : k < j) :
    kPermFixedPointCount n k j = 0 := by
  unfold kPermFixedPointCount
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨σ, h1, h2⟩ => by rw [cycleQuotientCount_eq] at h1; omega⟩

/-- The empty permutation has no cycles and no fixed points: `a(0, 0, 0) = 1`.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (definition of `a(n, k, j)`, value at
`n = k = j = 0`). -/
public theorem kPermFixedPointCount_zero_zero_zero : kPermFixedPointCount 0 0 0 = 1 := by
  unfold kPermFixedPointCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨1, by rw [cycleQuotientCount_eq]; simp, by simp⟩,
    fun x => Subtype.ext (Subsingleton.elim _ _)⟩

/-- Proposition 3 (i): `a(n, k, j) = C(n, j) d(n - j, k - j)` for `0 ≤ j ≤ k`, with
`d(m, i) = a(m, i, 0)` the number of derangements of `[m]` with `i` cycles.

The paper assumes `n ≥ k ≥ 1`; the identity is stated for all `n` and `k ≥ j`.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (i) (`integers-2024-A54-prop-3`). -/
public theorem_wanted kPermFixedPointCount_eq_choose_mul_derangement {n k j : ℕ} (hjk : j ≤ k) :
    kPermFixedPointCount n k j = n.choose j * kPermFixedPointCount (n - j) (k - j) 0

/-- Proposition 3 (iii): `j a(n, k, j) = n a(n - 1, k - 1, j - 1)` for `1 ≤ j ≤ k`.

The paper assumes `n ≥ k ≥ 1`; the identity is stated for all `n`.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (iii) (`integers-2024-A54-prop-3`). -/
public theorem_wanted mul_kPermFixedPointCount {n k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    j * kPermFixedPointCount n k j = n * kPermFixedPointCount (n - 1) (k - 1) (j - 1)

/-- Proposition 3 (iv): `∑_{j=0}^{k} a(n, k, j) = c(n, k)`, the unsigned Stirling number of the
first kind.

The paper assumes `n ≥ k ≥ 1`; the identity is stated for all `n` and `k`.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (iv) (`integers-2024-A54-prop-3`). -/
public theorem_wanted sum_kPermFixedPointCount (n k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), kPermFixedPointCount n k j = Nat.stirlingFirst n k

/-- Proposition 4 (mean): the mean `μ_{n,k} = n c(n - 1, k - 1) / c(n, k)` of the number of fixed
points of a uniform `k`-permutation of `[n]`, stated with the denominator `c(n, k)` cleared.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 4 (`integers-2024-A54-prop-4`). -/
public theorem_wanted sum_mul_kPermFixedPointCount {n k : ℕ} (hk : 1 ≤ k) :
    ∑ j ∈ Finset.range (k + 1), j * kPermFixedPointCount n k j =
      n * Nat.stirlingFirst (n - 1) (k - 1)

/-- Proposition 4 (variance): with `μ_{n,k} = n c(n - 1, k - 1) / c(n, k)`, the variance of the
number of fixed points of a uniform `k`-permutation of `[n]` is
`σ²_{n,k} = μ_{n,k} (1 + μ_{n-1,k-1} - μ_{n,k})`, for `n ≥ k ≥ 2` (so that `μ_{n-1,k-1}` is
defined).

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 4 (`integers-2024-A54-prop-4`). -/
public theorem_wanted kPermFixedPoint_variance {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    let μ : ℕ → ℕ → ℚ := fun n k =>
      (n : ℚ) * Nat.stirlingFirst (n - 1) (k - 1) / Nat.stirlingFirst n k
    (∑ j ∈ Finset.range (k + 1), (j : ℚ) ^ 2 * kPermFixedPointCount n k j) /
        Nat.stirlingFirst n k - μ n k ^ 2 =
      μ n k * (1 + μ (n - 1) (k - 1) - μ n k)

/-- Newton's inequalities (Theorem 1): if `p = ∑_{j=0}^{n} a_j x^j`, `n ≥ 2`, of degree `n` has
only real zeros, then `a_j² ≥ ((j + 1) / j) ((n - j + 1) / (n - j)) a_{j-1} a_{j+1}` for
`1 ≤ j ≤ n - 1`.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Theorem 1 (`integers-2024-A54-thm-1`). -/
public theorem_wanted newton_inequality_of_real_roots {p : ℝ[X]} {n : ℕ} (hn : 2 ≤ n)
    (hdeg : p.natDegree = n) (hsplit : p.Splits) {j : ℕ} (hj : 1 ≤ j)
    (hjn : j ≤ n - 1) :
    ((j + 1 : ℝ) / j) * (((n : ℝ) - j + 1) / ((n : ℝ) - j)) *
        (p.coeff (j - 1) * p.coeff (j + 1)) ≤ p.coeff j ^ 2

/-- Schur's theorem (Theorem 2): if `f = ∑ a_k x^k` and `g = ∑ c_k x^k` are real polynomials with
only real zeros and all zeros of `g` have the same sign, then `∑_{k=0}^{d} k! a_k c_k x^k`,
`d = min(deg f, deg g)`, has only real zeros. The paper's "one of them" is `g` by symmetry, and
"on the same side" is read as all zeros `≤ 0` or all zeros `≥ 0`.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Theorem 2 (Schur) (`integers-2024-A54-thm-2`). -/
public theorem_wanted schur_factorial_hadamard_real_roots {f g : ℝ[X]}
    (hf : f.Splits) (hg : g.Splits)
    (hsign : (∀ x ∈ g.roots, x ≤ 0) ∨ (∀ x ∈ g.roots, 0 ≤ x)) :
    let h : ℝ[X] := ∑ k ∈ Finset.range (min f.natDegree g.natDegree + 1),
      C ((k.factorial : ℝ) * f.coeff k * g.coeff k) * X ^ k
    h.Splits

/-- Theorem 3: for `n ≥ 2` the polynomial `D_n(x) = ∑_{k=1}^{n} d(n + k, k) x^(k-1)` has only real
zeros, where `d(m, k) = a(m, k, 0)` counts derangements of `[m]` with `k` cycles. The terms with
`k > n` vanish, so the upper summation limit `n` loses nothing.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Theorem 3 (`integers-2024-A54-thm-3`). -/
public theorem_wanted derangementCyclePolynomial_real_roots {n : ℕ} (hn : 2 ≤ n) :
    let D : ℝ[X] := ∑ k ∈ Finset.Icc 1 n,
      C (kPermFixedPointCount (n + k) k 0 : ℝ) * X ^ (k - 1)
    D.Splits

/-- Corollary 1 (unimodality part): a positive sequence `(a_j)_{j=0}^{n}` satisfying Newton's
inequalities has a single maximum or a plateau of two elements: it strictly increases up to some
`m`, then strictly decreases, possibly after one equality `a_m = a_{m+1}`. The paper's "SLC"
conclusion is not stated (the abbreviation is not defined in the extracted statement).

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Corollary 1 (`integers-2024-A54-cor-1`). -/
public theorem_wanted unimodal_of_newton_inequalities {a : ℕ → ℝ} {n : ℕ}
    (hpos : ∀ j ≤ n, 0 < a j)
    (hnewton : ∀ j, 1 ≤ j → j ≤ n - 1 →
      ((j + 1 : ℝ) / j) * (((n : ℝ) - j + 1) / ((n : ℝ) - j)) * (a (j - 1) * a (j + 1)) ≤
        a j ^ 2) :
    ∃ m ≤ n, StrictMonoOn a (Set.Icc 0 m) ∧
      (StrictAntiOn a (Set.Icc m n) ∨
        (m < n ∧ a m = a (m + 1) ∧ StrictAntiOn a (Set.Icc (m + 1) n)))

/-- Corollary 2 (unimodality part): for `k ≤ n` the sequence `(a(n, k, j))_{j=0}^{k}` is unimodal
with a peak or a plateau of two elements: it weakly increases up to its first maximizer `m`,
weakly decreases afterwards, and only `m` and `m + 1` attain the maximum. The paper's "SLC"
conclusion is not stated (the abbreviation is not defined in the extracted statement).

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Corollary 2 (`integers-2024-A54-cor-2`). -/
public theorem_wanted kPermFixedPointCount_unimodal {n k : ℕ} (hkn : k ≤ n) :
    ∃ m ≤ k, MonotoneOn (kPermFixedPointCount n k ·) (Set.Icc 0 m) ∧
      AntitoneOn (kPermFixedPointCount n k ·) (Set.Icc m k) ∧
      ∀ i ≤ k, kPermFixedPointCount n k i = kPermFixedPointCount n k m → i = m ∨ i = m + 1

/-- Theorem 5 (the quoted central limit theorem of Harper and Bender, central limit part):
let `(Q_n)` be real polynomials whose zeros are all real and nonpositive, with
`μ_n = Q_n'(1) / Q_n(1)` and `σ_n² = Q_n'(1) / Q_n(1) + Q_n''(1) / Q_n(1) - (Q_n'(1) / Q_n(1))²`.
If `σ_n² → ∞`, then the coefficient distribution `j ↦ [x^j] Q_n / Q_n(1)` satisfies a central
limit theorem: for every real `x`, the mass of `{j : (j - μ_n) / σ_n ≤ x}` tends to the
standard normal distribution function at `x` (Mathlib `ProbabilityTheory.cdf` of
`gaussianReal 0 1`). "Central limit theorem" is the standard notion (convergence of
distribution functions; uniform and pointwise convergence agree since the normal distribution
function is continuous). No nonvanishing hypothesis is needed: `σ_n² → ∞` forces
`Q_n ≠ 0` eventually (`σ_n² = 0` for `Q_n = 0` under Lean's `x / 0 = 0`). The paper asks for
negative zeros; zeros at `0` are also allowed here, since `Q_n = X^m R_n` only shifts the
coefficient distribution by `m` and leaves `σ_n²` unchanged. The local limit theorem in the
record's second sentence (under no internal zeros) is not stated.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Theorem 5 (`integers-2024-A54-thm-5`). -/
public theorem_wanted coeff_tendsto_gaussian_cdf_of_neg_real_roots (Q : ℕ → ℝ[X])
    (hsplit : ∀ n, (Q n).Splits) (hnonpos : ∀ n, ∀ r ∈ (Q n).roots, r ≤ 0) :
    let μ : ℕ → ℝ := fun n => (Q n).derivative.eval 1 / (Q n).eval 1
    let σ2 : ℕ → ℝ := fun n =>
      (Q n).derivative.eval 1 / (Q n).eval 1 +
        (Q n).derivative.derivative.eval 1 / (Q n).eval 1 - μ n ^ 2
    Tendsto σ2 atTop atTop → ∀ x : ℝ,
      Tendsto (fun n => (∑ j ∈ Finset.range ((Q n).natDegree + 1) with
          (((j : ℕ) : ℝ) - μ n) / Real.sqrt (σ2 n) ≤ x, (Q n).coeff j) / (Q n).eval 1)
        atTop (𝓝 (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x))

/-- Theorem 4: for `n ≥ k ≥ 1`, the polynomial `P(x) = ∑_{j=0}^{k} a(n, k, j) x^j` of the
fixed-point distribution of `k`-permutations of `[n]` has only real zeros.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Theorem 4 (`integers-2024-A54-thm-4`). -/
public theorem_wanted kPermFixedPointPolynomial_real_roots {n k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n) :
    let P : ℝ[X] := ∑ j ∈ Finset.range (k + 1), C (kPermFixedPointCount n k j : ℝ) * X ^ j
    P.Splits

end

end MetaMathlibExt
