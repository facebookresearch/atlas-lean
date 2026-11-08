/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MetaMathlibExt

@[expose] public section

open Real

/-- The generalized hyperharmonic number `H_n^{[r]}(k)`: the elementary symmetric function of
degree `n - k` of `r, r + 1, …, r + n - 1`, divided by `n!`, and `0` when `k > n`.

The source defines `H_n^{[r]}(k)` in (2.4) by `(-1)^k k! H_n^{[r]}(k) = D_x^k binom(n+r-x-1, n)`
at `x = 0`, and derives in Section 2 (proof of (2.10)) that `H_n^{[r]}(k)` equals
`(1/n!) ∑_{0 ≤ j_1 < ⋯ < j_{n-k} ≤ n-1} (r + j_1) ⋯ (r + j_{n-k})` for every `r`; this
explicit form is used here. For `r = 1` it is the depth-`k` multiple harmonic number, and for
`r ∉ {0, -1, …, 1 - n}` it equals `binom(n+r-1, n) H_n(k; r)` (2.10).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Section 2, (2.4) and (2.10) (`integers-2026-A81-cor-1`). -/
noncomputable def generalizedHyperharmonic (n k : ℕ) (r : ℂ) : ℂ :=
  if k ≤ n then
    (∑ s ∈ (Finset.range n).powersetCard (n - k), ∏ j ∈ s, (r + j)) / n.factorial
  else 0

/-- `H_n^{[r]}(k) = 0` for `k > n`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Section 2, (2.4) (`integers-2026-A81-cor-1`). -/
theorem generalizedHyperharmonic_of_lt {n k : ℕ} (h : n < k) (r : ℂ) :
    generalizedHyperharmonic n k r = 0 := by
  simp [generalizedHyperharmonic, Nat.not_le.mpr h]

/-- `H_0^{[r]}(0) = 1`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Section 2, (2.4) (`integers-2026-A81-cor-1`). -/
@[simp]
theorem generalizedHyperharmonic_zero_zero (r : ℂ) : generalizedHyperharmonic 0 0 r = 1 := by
  simp [generalizedHyperharmonic]

/-- `H_1^{[r]}(0) = r`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Section 2, (2.4) (`integers-2026-A81-cor-1`). -/
theorem generalizedHyperharmonic_one_zero (r : ℂ) : generalizedHyperharmonic 1 0 r = r := by
  simp [generalizedHyperharmonic, Finset.range_one, Finset.powersetCard_one]

/-- `H_1^{[r]}(1) = 1`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Section 2, (2.4) (`integers-2026-A81-cor-1`). -/
theorem generalizedHyperharmonic_one_one (r : ℂ) : generalizedHyperharmonic 1 1 r = 1 := by
  simp [generalizedHyperharmonic]

/-- The generalized hyperharmonic Euler sum `S(k, r; p; a) = ∑_{n ≥ k} H_n^{[r]}(k) / (n + a)^p`,
written as a sum over `n + k`; the exponent `p` is an integer.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 1 display (`integers-2026-A81-cor-1`). -/
noncomputable def hyperharmonicEulerSum (k : ℕ) (r : ℂ) (p : ℤ) (a : ℂ) : ℂ :=
  ∑' n : ℕ, generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + a) ^ p

/-- `S(k, r; p; a)` is also the sum over all `n ≥ 0`, since `H_n^{[r]}(k) = 0` for `n < k`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 1 display (`integers-2026-A81-cor-1`). -/
theorem hyperharmonicEulerSum_eq_tsum (k : ℕ) (r : ℂ) (p : ℤ) (a : ℂ) :
    hyperharmonicEulerSum k r p a =
      ∑' n : ℕ, generalizedHyperharmonic n k r / ((n : ℂ) + a) ^ p := by
  unfold hyperharmonicEulerSum
  refine (add_left_injective k).tsum_eq
    (f := fun n : ℕ => generalizedHyperharmonic n k r / ((n : ℂ) + a) ^ p) ?_
  intro n hn
  by_cases h : k ≤ n
  · exact ⟨n - k, by simp only; omega⟩
  · exact absurd (by simp [generalizedHyperharmonic_of_lt (Nat.lt_of_not_le h)]) hn

/-- The depth-`k` odd harmonic number `O_n(k) = H_n(k; 1/2)
= ∑_{1 ≤ i_1 < ⋯ < i_k ≤ n} ∏_j 1 / (i_j - 1/2)`, with `O_n(0) = 1` and `O_n(k) = 0` for
`k > n`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, (1.8) and (2.11) (`integers-2026-A81-cor-1`). -/
noncomputable def oddMultipleHarmonic (k n : ℕ) : ℝ :=
  ∑ s ∈ (Finset.Icc 1 n).powersetCard k, ∏ i ∈ s, ((i : ℝ) - 1 / 2)⁻¹

/-- `O_n(0) = 1`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, (2.11) (`integers-2026-A81-cor-1`). -/
@[simp]
theorem oddMultipleHarmonic_zero (n : ℕ) : oddMultipleHarmonic 0 n = 1 := by
  simp [oddMultipleHarmonic]

/-- `O_n(k) = 0` for `k > n`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, (2.11) (`integers-2026-A81-cor-1`). -/
theorem oddMultipleHarmonic_of_lt {k n : ℕ} (h : n < k) : oddMultipleHarmonic k n = 0 := by
  have hcard : (Finset.Icc 1 n).card < k := by simpa using h
  simp [oddMultipleHarmonic, Finset.powersetCard_eq_empty.mpr hcard]

/-- `O_1(1) = 2`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, (2.11) (`integers-2026-A81-cor-1`). -/
theorem oddMultipleHarmonic_one_one : oddMultipleHarmonic 1 1 = 2 := by
  simp [oddMultipleHarmonic, Finset.powersetCard_one]
  norm_num

/-- The `ℚ`-algebra `ℚ[log 2, π², ζ(3), ζ(5), …] ⊆ ℂ`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 2 (`integers-2026-A81-cor-2`). -/
noncomputable def eulerSumPeriodAlgebra : Subalgebra ℚ ℂ :=
  Algebra.adjoin ℚ
    ({(Real.log 2 : ℂ), (π : ℂ) ^ 2} ∪ Set.range fun j : ℕ => riemannZeta (2 * j + 3))

/-- `log 2`, `π²` and the odd zeta values `ζ(2j + 3)` lie in `ℚ[log 2, π², ζ(2j+1)_{j ≥ 1}]`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 2 (`integers-2026-A81-cor-2`). -/
theorem generators_mem_eulerSumPeriodAlgebra :
    (Real.log 2 : ℂ) ∈ eulerSumPeriodAlgebra ∧ (π : ℂ) ^ 2 ∈ eulerSumPeriodAlgebra ∧
      ∀ j : ℕ, riemannZeta (2 * j + 3) ∈ eulerSumPeriodAlgebra :=
  ⟨Algebra.subset_adjoin (by simp), Algebra.subset_adjoin (by simp),
    fun j => Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)⟩

/-- The `ℚ`-algebra `ℚ[log 2, π, ζ(2j+1)_{j ≥ 1}, β(2j)_{j ≥ 1}] ⊆ ℂ`, where
`β(s) = ∑_{n ≥ 0} (-1)^n / (2n+1)^s` is the Dirichlet beta function.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 6 (`integers-2026-A81-cor-6`). -/
noncomputable def eulerSumBetaPeriodAlgebra : Subalgebra ℚ ℂ :=
  Algebra.adjoin ℚ
    ({(Real.log 2 : ℂ), (π : ℂ)} ∪ Set.range (fun j : ℕ => riemannZeta (2 * j + 3)) ∪
      Set.range fun j : ℕ =>
        ((∑' n : ℕ, (-1 : ℝ) ^ n / (2 * n + 1 : ℝ) ^ (2 * j + 2) : ℝ) : ℂ))

/-- `log 2`, `π`, `ζ(2j + 3)` and `β(2j + 2)` lie in
`ℚ[log 2, π, ζ(2j+1)_{j ≥ 1}, β(2j)_{j ≥ 1}]`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 6 (`integers-2026-A81-cor-6`). -/
theorem generators_mem_eulerSumBetaPeriodAlgebra :
    (Real.log 2 : ℂ) ∈ eulerSumBetaPeriodAlgebra ∧ (π : ℂ) ∈ eulerSumBetaPeriodAlgebra ∧
      (∀ j : ℕ, riemannZeta (2 * j + 3) ∈ eulerSumBetaPeriodAlgebra) ∧
      ∀ j : ℕ, ((∑' n : ℕ, (-1 : ℝ) ^ n / (2 * n + 1 : ℝ) ^ (2 * j + 2) : ℝ) : ℂ) ∈
        eulerSumBetaPeriodAlgebra :=
  ⟨Algebra.subset_adjoin (by simp), Algebra.subset_adjoin (by simp),
    fun j => Algebra.subset_adjoin (Or.inl (Or.inr ⟨j, rfl⟩)),
    fun j => Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)⟩

/-- Beta-function evaluation: for `k, p ≥ 0`, `ℜ(r) < p + 1` and `ℜ(a) > -k`,
`p! k! S(k, r; p + 1; a) = (-1)^p D_a^p D_r^k B(a, 1 - r)`.

`B(a, 1 - r)` is written `Γ(a) Γ(1 - r) / Γ(a + 1 - r)` with `(Γ(a + 1 - r))⁻¹` (Mathlib's value
`0` at the poles of `Γ` is the value of the entire function `1/Γ` there). Deviation: the points
`r ∈ {1, 2, …}` (where the source's statement holds after removing a singularity of
`Γ(1 - r)`) and `a ∈ {0, -1, -2, …}` are excluded. The source's analytic-continuation sentence
is not formalized.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Theorem 1 (`integers-2026-A81-thm-1`). -/
public theorem_wanted hyperharmonicEulerSum_eq_iteratedDeriv_beta (k p : ℕ) (r a : ℂ)
    (hr : r.re < p + 1) (ha : -(k : ℝ) < a.re) (hr' : ∀ m : ℕ, r ≠ m + 1)
    (ha' : ∀ m : ℕ, a ≠ -m) :
    (p.factorial * k.factorial : ℂ) * hyperharmonicEulerSum k r (p + 1) a =
      (-1) ^ p * iteratedDeriv p (fun b => iteratedDeriv k
        (fun s => Complex.Gamma b * Complex.Gamma (1 - s) * (Complex.Gamma (b + 1 - s))⁻¹) r) a

/-- Polygamma structure: for `r = 1, …, p` and `a ∈ ℂ \ ℤ`, `S(k, r; p + 1; a)` converges and
lies in `ℚ(a)[ψ(a) + γ, ψ^{(j)}(a)_{j ≥ 1}, ζ(j)_{j ≥ 2}]`.

`ψ` is `Complex.digamma` and `ψ^{(j)}` its `j`-th derivative. The source's extension to integers
`a > -k` by continuity is not formalized.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Theorem 2 (`integers-2026-A81-thm-2`). -/
public theorem_wanted hyperharmonicEulerSum_mem_adjoin_digamma (k p r : ℕ) (hr : 1 ≤ r)
    (hrp : r ≤ p) (a : ℂ) (ha : ∀ m : ℤ, a ≠ m) :
    Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + a) ^ ((p : ℤ) + 1)) ∧
      hyperharmonicEulerSum k r (p + 1) a ∈
        Algebra.adjoin (IntermediateField.adjoin ℚ {a})
          ({Complex.digamma a + Real.eulerMascheroniConstant} ∪
            Set.range (fun j : ℕ => iteratedDeriv (j + 1) Complex.digamma a) ∪
            Set.range fun j : ℕ => riemannZeta (j + 2))

/-- Rational parameters: if `a, r ∈ ℚ \ ℤ` with `N a ∈ ℤ` (`N ≥ 1`) and `a ≡ r (mod ℤ)`, then for
integers `k ≥ 0` and `p > r`, `S(k, r; p; a)` converges and lies in
`π ℚ(ζ + ζ⁻¹)[ψ(a) + γ, ψ^{(j)}(a)_{j ≥ 1}, π², ζ(2j+1)_{j ≥ 1}]`, `ζ` a primitive root of unity
of order `lcm(2N, 4)`.

`ζ` is taken to be `exp(2πi / lcm(2N, 4))`; `ℚ(ζ + ζ⁻¹)` does not depend on the primitive root.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Theorem 3 (`integers-2026-A81-thm-3`). -/
public theorem_wanted hyperharmonicEulerSum_rat_mem_pi_mul_adjoin (a r : ℚ)
    (ha : ∀ m : ℤ, a ≠ m) (hr : ∀ m : ℤ, r ≠ m) (N : ℕ) (hN : 0 < N)
    (hNa : ∃ m : ℤ, N * a = m) (har : ∃ m : ℤ, a - r = m) (k : ℕ) (p : ℤ) (hp : r < p) :
    let ζ : ℂ := Complex.exp (2 * π * Complex.I / (Nat.lcm (2 * N) 4 : ℂ))
    Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + a) ^ p) ∧
      ∃ x ∈ Algebra.adjoin (IntermediateField.adjoin ℚ {ζ + ζ⁻¹})
          ({Complex.digamma a + Real.eulerMascheroniConstant} ∪
            Set.range (fun j : ℕ => iteratedDeriv (j + 1) Complex.digamma a) ∪
            {(π : ℂ) ^ 2} ∪ Set.range fun j : ℕ => riemannZeta (2 * j + 3)),
        hyperharmonicEulerSum k r p a = π * x

/-- Duality: for `ℜ(r) < p + 1` and `ℜ(t) < k + 1`, both sums converge and
`S(k, r; p + 1; 1 - t) = S(p, t; k + 1; 1 - r)`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 1 (`integers-2026-A81-cor-1`). -/
public theorem_wanted hyperharmonicEulerSum_duality (k p : ℕ) (r t : ℂ) (hr : r.re < p + 1)
    (ht : t.re < k + 1) :
    Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + (1 - t)) ^ ((p : ℤ) + 1)) ∧
      Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + p) p t / (((n + p : ℕ) : ℂ) + (1 - r)) ^ ((k : ℤ) + 1)) ∧
      hyperharmonicEulerSum k r (p + 1) (1 - t) = hyperharmonicEulerSum p t (k + 1) (1 - r)

/-- Half-integer shifts: for `a ∈ 1/2 + ℤ` and integers `k ≥ 0`, `1 ≤ r < p`,
`∑_{n ≥ k} H_n^{[r]}(k) / (n + a)^p` converges and lies in `ℚ[log 2, π², ζ(2j+1)_{j ≥ 1}]`.

Deviation: the source prints `1 ≤ r ≤ p`; at `r = p` the series diverges (for `k = 0`,
`r = p = 1`, `a = 1/2` it is `∑ 1 / (n + 1/2)`), and the source's Theorem 2 has exponent `p + 1`
for `r ≤ p`, so `r < p` is used.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 2, first part (`integers-2026-A81-cor-2`). -/
public theorem_wanted hyperharmonicEulerSum_half_mem_eulerSumPeriodAlgebra (k p r : ℕ)
    (hr : 1 ≤ r) (hrp : r < p) (c : ℤ) :
    Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + (c + 1 / 2)) ^ (p : ℤ)) ∧
      hyperharmonicEulerSum k r p (c + 1 / 2) ∈ eulerSumPeriodAlgebra

/-- For integers `k ≥ 0`, `p > 0` and `a > -k`,
`∑_{n ≥ k} binom(2n, n) O_n(k) / (4^n (n + a)^p)` converges and lies in
`ℚ[log 2, π², ζ(2j+1)_{j ≥ 1}]`. The sum runs over all `n ≥ 0`; the terms with `n < k` vanish.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 2, second part (`integers-2026-A81-cor-2`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_sum_mem_eulerSumPeriodAlgebra
    (k p : ℕ) (hp : 0 < p) (a : ℤ) (ha : -(k : ℤ) < a) :
    Summable (fun n : ℕ =>
        ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n / (4 ^ n * ((n : ℝ) + a) ^ p)) ∧
      ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + a) ^ p) : ℝ) : ℂ) ∈ eulerSumPeriodAlgebra

/-- For every integer `k ≥ 0`,
`∑_{n ≥ k} binom(2n, n) O_n(k) / (4^n (n + 1)^2)
= 2^{k+2} (k + 1 - log 2) - ∑_{j=1}^{k} (2^{k+2} - 2^j) ζ(k + 2 - j)`.

The sum runs over all `n ≥ 0`; the terms with `n < k` vanish.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 3 (`integers-2026-A81-cor-3`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_div_succ_sq_tsum (k : ℕ) :
    ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) =
      2 ^ (k + 2) * (k + 1 - Real.log 2) -
        ∑ j ∈ Finset.Icc 1 k, (2 ^ (k + 2) - 2 ^ j) * riemannZeta ((k + 2 - j : ℕ) : ℂ)

/-- For integers `k ≥ 0`, `p > m ≥ 0` and `a > -k`,
`∑_{n ≥ k} binom(n, m) binom(2n, n) O_n(k) / (4^n (n + a)^p)` converges and lies in
`ℚ[log 2, π², ζ(2j+1)_{j ≥ 1}]`. The sum runs over all `n ≥ 0`; the terms with `n < k` vanish.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 4, first part (`integers-2026-A81-cor-4`). -/
public theorem_wanted choose_centralBinom_oddMultipleHarmonic_sum_mem_eulerSumPeriodAlgebra
    (k p m : ℕ) (hmp : m < p) (a : ℤ) (ha : -(k : ℤ) < a) :
    Summable (fun n : ℕ => (n.choose m : ℝ) * ((2 * n).choose n : ℝ) *
        oddMultipleHarmonic k n / (4 ^ n * ((n : ℝ) + a) ^ p)) ∧
      ((∑' n : ℕ, (n.choose m : ℝ) * ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + a) ^ p) : ℝ) : ℂ) ∈ eulerSumPeriodAlgebra

/-- For integers `k ≥ 0`, `p, m > 0` and `a > -k`,
`∑_{n ≥ k} binom(2n, n) O_n(k) / (4^n binom(n + m, m) (n + a)^p)` converges and lies in
`ℚ[log 2, π², ζ(2j+1)_{j ≥ 1}]`. The sum runs over all `n ≥ 0`; the terms with `n < k` vanish.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 4, second part (`integers-2026-A81-cor-4`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_div_choose_sum_mem_eulerSumPeriodAlgebra
    (k p m : ℕ) (hp : 0 < p) (hm : 0 < m) (a : ℤ) (ha : -(k : ℤ) < a) :
    Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + a) ^ p)) ∧
      ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + a) ^ p) : ℝ) : ℂ) ∈
        eulerSumPeriodAlgebra

/-- For every integer `k > 0`, `∑_{n ≥ k} C_n O_n(k) / (4^n n) = (2^{k+1} - 1) ζ(k + 1) - 2^{k+1}`,
with `C_n` the Catalan number.

The denominator `4^n n` is read from the record's two-row layout (`C_n O_n(k)` over `4^n n`).
The sum runs over all `n ≥ 0`; the terms with `n < k` vanish.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 5 (`integers-2026-A81-cor-5`). -/
public theorem_wanted catalan_oddMultipleHarmonic_div_tsum (k : ℕ) (hk : 0 < k) :
    ((∑' n : ℕ, (catalan n : ℝ) * oddMultipleHarmonic k n / (4 ^ n * n) : ℝ) : ℂ) =
      (2 ^ (k + 1) - 1) * riemannZeta (k + 1) - 2 ^ (k + 1)

/-- Quarter shifts: for `a ∈ 1/4 + ℤ` or `a ∈ 3/4 + ℤ` and integers `k ≥ 0`, `0 ≤ r < p`,
`∑_{n ≥ k} H_n^{[r]}(k) / (n + a)^p` converges and lies in
`ℚ[log 2, π, ζ(2j+1)_{j ≥ 1}, β(2j)_{j ≥ 1}]`, `β` the Dirichlet beta function.

Deviation: the source prints `0 ≤ r ≤ p`; at `r = p ≥ 1` the series diverges (for `k = 0`,
`r = p = 1` it is `∑ 1 / (n + a)`), so `r < p` is used.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 6 (`integers-2026-A81-cor-6`). -/
public theorem_wanted hyperharmonicEulerSum_quarter_mem_eulerSumBetaPeriodAlgebra
    (k p r : ℕ) (hrp : r < p) (a : ℂ) (ha : ∃ c : ℤ, a = c + 1 / 4 ∨ a = c + 3 / 4) :
    Summable (fun n : ℕ =>
        generalizedHyperharmonic (n + k) k r / (((n + k : ℕ) : ℂ) + a) ^ (p : ℤ)) ∧
      hyperharmonicEulerSum k r p a ∈ eulerSumBetaPeriodAlgebra

/-- Half-integer parameters: for `a, r ∈ 1/2 + ℤ` and integers `k ≥ 0`, `p > r`,
`S(k, r; p; a)` converges and lies in `π ℚ[log 2, π², ζ(2j+1)_{j ≥ 1}]`.

Here `r = c + 1/2`, `a = d + 1/2` with `c, d ∈ ℤ`, and `p > r` is `p > c`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 7, first part (`integers-2026-A81-cor-7`). -/
public theorem_wanted hyperharmonicEulerSum_half_half_mem_pi_mul (k : ℕ) (c d p : ℤ)
    (hp : c < p) :
    Summable (fun n : ℕ => generalizedHyperharmonic (n + k) k (c + 1 / 2) /
        (((n + k : ℕ) : ℂ) + (d + 1 / 2)) ^ p) ∧
      ∃ x ∈ eulerSumPeriodAlgebra,
        hyperharmonicEulerSum k (c + 1 / 2) p (d + 1 / 2) = π * x

/-- For `a ∈ 1/2 + ℤ` and integers `k ≥ 0`, `p > m ≥ 0`,
`∑_{n ≥ k} binom(n, m) binom(2n, n) O_n(k) / (4^n (n + a)^p)` converges and lies in
`π ℚ[log 2, π², ζ(2j+1)_{j ≥ 1}]`. Here `a = d + 1/2`, `d ∈ ℤ`; the sum runs over all `n ≥ 0`
(the terms with `n < k` vanish).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 7, second part (`integers-2026-A81-cor-7`). -/
public theorem_wanted choose_centralBinom_oddMultipleHarmonic_half_sum_mem_pi_mul
    (k p m : ℕ) (hmp : m < p) (d : ℤ) :
    Summable (fun n : ℕ => (n.choose m : ℝ) * ((2 * n).choose n : ℝ) *
        oddMultipleHarmonic k n / (4 ^ n * ((n : ℝ) + (d + 1 / 2)) ^ p)) ∧
      ∃ x ∈ eulerSumPeriodAlgebra,
        ((∑' n : ℕ, (n.choose m : ℝ) * ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + (d + 1 / 2)) ^ p) : ℝ) : ℂ) = π * x

/-- For `a ∈ 1/2 + ℤ` and integers `k ≥ 0`, `p, m > 0`,
`∑_{n ≥ k} binom(2n, n) O_n(k) / (4^n binom(n + m, m) (n + a)^p)` converges and lies in
`ℚ + π ℚ[log 2, π², ζ(2j+1)_{j ≥ 1}]`. Here `a = d + 1/2`, `d ∈ ℤ`; the sum runs over all
`n ≥ 0` (the terms with `n < k` vanish).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 7, third part (`integers-2026-A81-cor-7`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_div_choose_half_sum_mem
    (k p m : ℕ) (hp : 0 < p) (hm : 0 < m) (d : ℤ) :
    Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + (d + 1 / 2)) ^ p)) ∧
      ∃ q : ℚ, ∃ x ∈ eulerSumPeriodAlgebra,
        ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + (d + 1 / 2)) ^ p) : ℝ) : ℂ) =
          q + π * x

/-- For integers `k ≥ 0`, `p > 0`,
`∑_{n ≥ k} C_n O_n(k) / (4^n (n + 1/2)^p) - (-2)^p 2^{k+1}` lies in
`π ℚ[log 2, π², ζ(2j+1)_{j ≥ 1}]`, and the series converges. The sum runs over all `n ≥ 0`
(the terms with `n < k` vanish).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 8 (`integers-2026-A81-cor-8`). -/
public theorem_wanted catalan_oddMultipleHarmonic_half_sum_sub_mem_pi_mul (k p : ℕ)
    (hp : 0 < p) :
    Summable (fun n : ℕ => (catalan n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n : ℝ) + 1 / 2) ^ p)) ∧
      ∃ x ∈ eulerSumPeriodAlgebra,
        ((∑' n : ℕ, (catalan n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + 1 / 2) ^ p) : ℝ) : ℂ) - (-2) ^ p * 2 ^ (k + 1) = π * x

/-- For every integer `m ≥ 1`,
`∑_{n ≥ 0} binom(2n, n) / (4^n binom(n + m, m) (n + 1/2)^2)
= (4^m π / binom(2m, m)) (2 log 2 - O_m)
  - ∑_{q=1}^{m} (-4)^q binom(m, q) / (binom(2q, q) (q - 1/2)^2)`,
where `O_m = O_m(1)` (the source writes `O_m` for the depth-one odd harmonic number).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 9, first identity (`integers-2026-A81-cor-9`). -/
public theorem_wanted centralBinom_div_choose_half_sq_tsum (m : ℕ) (hm : 0 < m) :
    ∑' n : ℕ, ((2 * n).choose n : ℝ) / (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 1 / 2) ^ 2) =
      4 ^ m * π / ((2 * m).choose m : ℝ) * (2 * Real.log 2 - oddMultipleHarmonic 1 m) -
        ∑ q ∈ Finset.Icc 1 m,
          (-4 : ℝ) ^ q * (m.choose q : ℝ) / (((2 * q).choose q : ℝ) * ((q : ℝ) - 1 / 2) ^ 2)

/-- For every integer `m ≥ 1`,
`∑_{n ≥ 0} binom(2n, n) (O_n - O_m) / (4^n binom(n + m, m) (n + 1/2)^2)
= (4^m π / binom(2m, m)) ((O_m - 2 log 2)^2 - ζ(2))
  + ∑_{q=1}^{m} (-4)^q binom(m, q) (O_m - O_q) / (binom(2q, q) (q - 1/2)^2)`,
where `O_j = O_j(1)` and `ζ(2)` is written `π² / 6`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 9, second identity (`integers-2026-A81-cor-9`). -/
public theorem_wanted centralBinom_oddHarmonic_sub_div_choose_half_sq_tsum (m : ℕ)
    (hm : 0 < m) :
    ∑' n : ℕ, ((2 * n).choose n : ℝ) * (oddMultipleHarmonic 1 n - oddMultipleHarmonic 1 m) /
        (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 1 / 2) ^ 2) =
      4 ^ m * π / ((2 * m).choose m : ℝ) *
          ((oddMultipleHarmonic 1 m - 2 * Real.log 2) ^ 2 - π ^ 2 / 6) +
        ∑ q ∈ Finset.Icc 1 m,
          (-4 : ℝ) ^ q * (m.choose q : ℝ) * (oddMultipleHarmonic 1 m - oddMultipleHarmonic 1 q) /
            (((2 * q).choose q : ℝ) * ((q : ℝ) - 1 / 2) ^ 2)

/-- Products of quarter-shift sums: for `r_1, r_2 ∈ 1/2 + ℤ`, `a ∈ 1/4 + ℤ`, `b ∈ 3/4 + ℤ` and
integers `k_1, k_2 ≥ 0`, `p_1 > r_1`, `p_2 > r_2`, both sums converge and
`S(k_1, r_1; p_1, a) S(k_2, r_2; p_2, b) ∈ π ℚ[log 2, π, ζ(2j+1)_{j ≥ 1}, β(2j)_{j ≥ 1}]`.

Here `r_i = c_i + 1/2`, `a = d + 1/4`, `b = e + 3/4` with `c_i, d, e ∈ ℤ`, and `p_i > r_i` is
`p_i > c_i`.

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 11, first part (`integers-2026-A81-cor-11`). -/
public theorem_wanted hyperharmonicEulerSum_quarter_mul_mem_pi_mul (k₁ k₂ : ℕ)
    (c₁ c₂ d e p₁ p₂ : ℤ) (h₁ : c₁ < p₁) (h₂ : c₂ < p₂) :
    Summable (fun n : ℕ => generalizedHyperharmonic (n + k₁) k₁ (c₁ + 1 / 2) /
        (((n + k₁ : ℕ) : ℂ) + (d + 1 / 4)) ^ p₁) ∧
      Summable (fun n : ℕ => generalizedHyperharmonic (n + k₂) k₂ (c₂ + 1 / 2) /
        (((n + k₂ : ℕ) : ℂ) + (e + 3 / 4)) ^ p₂) ∧
      ∃ x ∈ eulerSumBetaPeriodAlgebra,
        hyperharmonicEulerSum k₁ (c₁ + 1 / 2) p₁ (d + 1 / 4) *
          hyperharmonicEulerSum k₂ (c₂ + 1 / 2) p₂ (e + 3 / 4) = π * x

/-- For integers `k_1, k_2 ≥ 0` and `p_1, p_2 > 0`, both series converge and
`(∑_{n ≥ k_1} binom(2n, n) O_n(k_1) / (4^n (n + 1/4)^{p_1}))
 (∑_{n ≥ k_2} binom(2n, n) O_n(k_2) / (4^n (n + 3/4)^{p_2}))`
lies in `π ℚ[log 2, π, ζ(2j+1)_{j ≥ 1}, β(2j)_{j ≥ 1}]`. The sums run over all `n ≥ 0`
(the terms with `n < k_i` vanish).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 11, second part (`integers-2026-A81-cor-11`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_quarter_mul_mem_pi_mul
    (k₁ k₂ p₁ p₂ : ℕ) (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) :
    Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k₁ n /
        (4 ^ n * ((n : ℝ) + 1 / 4) ^ p₁)) ∧
      Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k₂ n /
        (4 ^ n * ((n : ℝ) + 3 / 4) ^ p₂)) ∧
      ∃ x ∈ eulerSumBetaPeriodAlgebra,
        ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k₁ n /
            (4 ^ n * ((n : ℝ) + 1 / 4) ^ p₁) : ℝ) : ℂ) *
          ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k₂ n /
            (4 ^ n * ((n : ℝ) + 3 / 4) ^ p₂) : ℝ) : ℂ) = π * x

/-- Quarter shift `1/4`: for integers `k ≥ 0`, `p > m ≥ 0`,
`∑_{n ≥ k} binom(n, m) binom(2n, n) O_n(k) / (4^n (n + 1/4)^p)` converges and lies in
`ϖ ℚ[log 2, π, ζ(2j+1)_{j ≥ 1}, β(2j)_{j ≥ 1}]`, where `ϖ` is the lemniscate constant
`ϖ = 2 ∫_0^1 dt / √(1 - t⁴)`. The sum runs over all
`n ≥ 0` (the terms with `n < k` vanish).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 10, first statement (`integers-2026-A81-cor-10`). -/
public theorem_wanted choose_centralBinom_oddMultipleHarmonic_quarter_sum_mem
    (k p m : ℕ) (hmp : m < p) :
    Summable (fun n : ℕ => (n.choose m : ℝ) * ((2 * n).choose n : ℝ) *
        oddMultipleHarmonic k n / (4 ^ n * ((n : ℝ) + 1 / 4) ^ p)) ∧
      ∃ x ∈ eulerSumBetaPeriodAlgebra,
        ((∑' n : ℕ, (n.choose m : ℝ) * ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + 1 / 4) ^ p) : ℝ) : ℂ) =
          (((2 * ∫ t in (0 : ℝ)..1, (Real.sqrt (1 - t ^ 4))⁻¹) : ℝ) : ℂ) * x

/-- Quarter shift `3/4`: for integers `k ≥ 0`, `p > m ≥ 0`,
`∑_{n ≥ k} binom(n, m) binom(2n, n) O_n(k) / (4^n (n + 3/4)^p)` converges and lies in
`(π/ϖ) ℚ[log 2, π, ζ(2j+1)_{j ≥ 1}, β(2j)_{j ≥ 1}]`, where `ϖ` is the lemniscate constant
`ϖ = 2 ∫_0^1 dt / √(1 - t⁴)`. The sum runs over
all `n ≥ 0` (the terms with `n < k` vanish).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 10, second statement (`integers-2026-A81-cor-10`). -/
public theorem_wanted choose_centralBinom_oddMultipleHarmonic_three_quarter_sum_mem
    (k p m : ℕ) (hmp : m < p) :
    Summable (fun n : ℕ => (n.choose m : ℝ) * ((2 * n).choose n : ℝ) *
        oddMultipleHarmonic k n / (4 ^ n * ((n : ℝ) + 3 / 4) ^ p)) ∧
      ∃ x ∈ eulerSumBetaPeriodAlgebra,
        ((∑' n : ℕ, (n.choose m : ℝ) * ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n : ℝ) + 3 / 4) ^ p) : ℝ) : ℂ) =
          ((π / (2 * ∫ t in (0 : ℝ)..1, (Real.sqrt (1 - t ^ 4))⁻¹) : ℝ) : ℂ) * x

/-- Quarter shift `1/4` with `binom(n + m, m)` in the denominator: for integers `k ≥ 0`,
`p, m > 0`, `∑_{n ≥ k} binom(2n, n) O_n(k) / (4^n binom(n + m, m) (n + 1/4)^p)` converges and
lies in `ℚ + ϖ ℚ[log 2, π, ζ(2j+1)_{j ≥ 1}, β(2j)_{j ≥ 1}]`, where `ϖ` is the lemniscate constant
`ϖ = 2 ∫_0^1 dt / √(1 - t⁴)`. The sum runs
over all `n ≥ 0` (the terms with `n < k` vanish).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 10, third statement (`integers-2026-A81-cor-10`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_div_choose_quarter_sum_mem
    (k p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 1 / 4) ^ p)) ∧
      ∃ q : ℚ, ∃ x ∈ eulerSumBetaPeriodAlgebra,
        ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 1 / 4) ^ p) : ℝ) : ℂ) =
          q + (((2 * ∫ t in (0 : ℝ)..1, (Real.sqrt (1 - t ^ 4))⁻¹) : ℝ) : ℂ) * x

/-- Quarter shift `3/4` with `binom(n + m, m)` in the denominator: for integers `k ≥ 0`,
`p, m > 0`, `∑_{n ≥ k} binom(2n, n) O_n(k) / (4^n binom(n + m, m) (n + 3/4)^p)` converges and
lies in `ℚ + (π/ϖ) ℚ[log 2, π, ζ(2j+1)_{j ≥ 1}, β(2j)_{j ≥ 1}]`, where `ϖ` is the lemniscate
constant `ϖ = 2 ∫_0^1 dt / √(1 - t⁴)`. The sum runs over all `n ≥ 0` (the terms with `n < k`
vanish).

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 10, fourth statement (`integers-2026-A81-cor-10`). -/
public theorem_wanted centralBinom_oddMultipleHarmonic_div_choose_three_quarter_sum_mem
    (k p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    Summable (fun n : ℕ => ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
        (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 3 / 4) ^ p)) ∧
      ∃ q : ℚ, ∃ x ∈ eulerSumBetaPeriodAlgebra,
        ((∑' n : ℕ, ((2 * n).choose n : ℝ) * oddMultipleHarmonic k n /
          (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 3 / 4) ^ p) : ℝ) : ℂ) =
          q + ((π / (2 * ∫ t in (0 : ℝ)..1, (Real.sqrt (1 - t ^ 4))⁻¹) : ℝ) : ℂ) * x

end

end MetaMathlibExt
