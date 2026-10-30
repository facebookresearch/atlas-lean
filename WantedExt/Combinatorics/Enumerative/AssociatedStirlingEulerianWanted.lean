/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.Combinatorics.AssociatedStirlingEulerian

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- Theorem 5: for `n ≥ 2` and `1 ≤ m ≤ n`, `C_{n,m} = A_{n-1,m-1}` (with
`C_{1,0} = 1`), and `C_n(x) = x A_{n-1}(x)` for the excedance polynomials, where
`A_{n,m}` is the Eulerian number by excedances (all cycle lengths exceed `0`).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 5 (`jis-2025-25.5.7-thm-5`). -/
public theorem_wanted circularEulerian_eq_eulerian :
    circularEulerian 1 0 = 1 ∧
    (∀ n m : ℕ, 2 ≤ n → 1 ≤ m → m ≤ n →
      circularEulerian n m = rAssociatedStirlingEulerian 0 (n - 1) (m - 1)) ∧
    ∀ n : ℕ, 2 ≤ n →
      (∑ m ∈ Finset.range (n + 1), (circularEulerian n m : ℤ[X]) * X ^ m) =
        X * ∑ m ∈ Finset.range n,
          (rAssociatedStirlingEulerian 0 (n - 1) m : ℤ[X]) * X ^ m

/-- Theorem 10: for `r ≥ 2` and `0 ≤ m ≤ n`,
`A^{r-}_{n+1,m} = ∑_{j=1}^{r-1} C(n,j) ∑_{i ≥ 0} C_{j+1,i} A^{r-}_{n-j,m-i} +
A^{r-}_{n,m}`, where `A^{r-}` counts permutations with all cycle lengths at most
`r` by excedances. The inner sum runs over `i ≤ m` (terms with `m - i < 0`
vanish); terms with `j > n` vanish through `C(n,j) = 0`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 10 (`jis-2025-25.5.7-thm-10`). -/
public theorem_wanted rMinusAssociatedStirlingEulerian_succ (r n m : ℕ)
    (hr : 2 ≤ r) (hm : m ≤ n) :
    rMinusAssociatedStirlingEulerian r (n + 1) m =
      ∑ j ∈ Finset.Icc 1 (r - 1), n.choose j *
          ∑ i ∈ Finset.range (m + 1),
            circularEulerian (j + 1) i * rMinusAssociatedStirlingEulerian r (n - j) (m - i) +
        rMinusAssociatedStirlingEulerian r n m

/-- Theorem 30: for `0 ≤ m ≤ n` and `n ≥ r + 1`,
`A^r_{n,m} = m A^r_{n-1,m} + (n-m) A^r_{n-1,m-1} +
C(n-1,r) ∑_s C_{r+1,s} A^r_{n-r-1,m-s}`, where `A^r` counts permutations with
all cycle lengths greater than `r` by excedances. The term `(n-m) A^r_{n-1,m-1}`
is `0` at `m = 0` (index `-1`), and the sum runs over `s ≤ m`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 30 (`jis-2025-25.5.7-thm-30`). -/
public theorem_wanted rAssociatedStirlingEulerian_recurrence (r n m : ℕ)
    (hm : m ≤ n) (hn : r + 1 ≤ n) :
    rAssociatedStirlingEulerian r n m =
      m * rAssociatedStirlingEulerian r (n - 1) m +
        (if m = 0 then 0 else (n - m) * rAssociatedStirlingEulerian r (n - 1) (m - 1)) +
        (n - 1).choose r *
          ∑ s ∈ Finset.range (m + 1),
            circularEulerian (r + 1) s * rAssociatedStirlingEulerian r (n - r - 1) (m - s)

/-- Theorem 31: for `r ≥ 1`, `0 ≤ m ≤ n` and `n ≥ r + 1`,
`A^r_{n+1,m} = ∑_{j=r}^{n} C(n,j) ∑_{i=1}^{m} C_{j+1,i} A^r_{n-j,m-i}`.
Restricted to `r ≥ 1`: at `r = 0` the printed formula fails (`n = 1`, `m = 0`:
`A^0_{2,0} = 1`, the identity, while the right side is the empty sum `0`,
because the `j = 0` term needs `i = 0`).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 31 (`jis-2025-25.5.7-thm-31`). -/
public theorem_wanted rAssociatedStirlingEulerian_succ (r n m : ℕ) (hr : 1 ≤ r)
    (hm : m ≤ n) (hn : r + 1 ≤ n) :
    rAssociatedStirlingEulerian r (n + 1) m =
      ∑ j ∈ Finset.Icc r n, n.choose j *
        ∑ i ∈ Finset.Icc 1 m,
          circularEulerian (j + 1) i * rAssociatedStirlingEulerian r (n - j) (m - i)

/-- Corollary 55: for `n ≥ 1`, summing over derangements `σ` of `n` objects,
`∑ x^{e(σ)} (-2)^{c(σ)} = -2x(-2^{n-1}x - 2^{n-1}x^{n-1} + (x+1)^n)/(x-1)^2`, with
`e` the excedance count and `c` the number of cycles (for a derangement, the
number of entries of `cycleType`). Stated in `ℤ[X]` with the denominator
`(x - 1)^2` cleared.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 55 (`jis-2025-25.5.7-cor-55`). -/
public theorem_wanted derangement_excedance_cycle_sum_neg_two (n : ℕ) (hn : 1 ≤ n) :
    (X - 1) ^ 2 *
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i, σ i ≠ i),
          (X ^ excedanceCount n σ * (-2) ^ σ.cycleType.card : ℤ[X]) =
      -2 * X * (-(2 ^ (n - 1)) * X - 2 ^ (n - 1) * X ^ (n - 1) + (X + 1) ^ n)


/-! ### Exponential generating functions (Theorems 6-35, Corollaries 12-44)

Throughout, `R` is a commutative `ℚ`-algebra and `x q : R` (take `R = ℚ[x, q]` for the
paper's indeterminates). `permExcedanceCycleEGF P x q` is the paper's
`∑_n ∑_{σ ∈ P_n} x^{e(σ)} q^{c(σ)} u^n/n!` (at `q = 1` the series `P(x,u)`),
`A_j(x) = ∑_{σ ∈ S_j} x^{e(σ)}` is written out as a sum over `Equiv.Perm (Fin j)`, and
`exp F` for `F` with zero constant term is `PowerSeries.subst F (PowerSeries.exp R)`.
A statement `L = ln F` is rendered as `exp L = F` with `L(0) = 0`, and `F^q` as
`exp (q ln F)`: for every `L` with zero constant term and `exp L = F`, the claim holds
with `ln F := L` (over a `ℚ`-algebra such `L` exists and is unique). -/

/-- Theorem 6: `C(x,u) = ln A(x,u)`, i.e. `exp C(x,u) = A(x,u)`, where `C` is the
excedance generating function over circular permutations and `A` over all
permutations.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 6 (`jis-2025-25.5.7-thm-6`). -/
public theorem_wanted exp_circularPermEGF_eq_permEGF {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) :
    PowerSeries.subst
        (permExcedanceCycleEGF (fun n σ => 0 < n ∧ ∀ i j, σ.SameCycle i j) x 1)
        (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1

/-- Theorem 7: for `r ≥ 1`, the excedance generating function over circular
permutations of at most `r` objects is
`C^{r-}(x,u) = ∑_{n=1}^{r} C_n(x) u^n/n! = u + x ∑_{n=1}^{r-1} A_n(x) u^{n+1}/(n+1)!`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 7 (`jis-2025-25.5.7-thm-7`). -/
public theorem_wanted circularRMinusPermEGF_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 1 ≤ r) :
    permExcedanceCycleEGF (fun n σ => (0 < n ∧ ∀ i j, σ.SameCycle i j) ∧ n ≤ r) x 1 =
      PowerSeries.X + ∑ j ∈ Finset.Icc 1 (r - 1),
        PowerSeries.C ((((j + 1).factorial : ℚ)⁻¹) •
          (x * ∑ σ : Equiv.Perm (Fin j), x ^ excedanceCount j σ)) * PowerSeries.X ^ (j + 1)

/-- Theorem 8: for `r ≥ 2`, the excedance generating function over circular
permutations of exactly `r` objects (circular `r`-cycle permutations) is
`C^{(r)}(x,u) = x A_{r-1}(x) u^r/r!`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 8 (`jis-2025-25.5.7-thm-8`). -/
public theorem_wanted circularRCyclePermEGF_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (fun n σ => (0 < n ∧ ∀ i j, σ.SameCycle i j) ∧ n = r) x 1 =
      PowerSeries.C (((r.factorial : ℚ)⁻¹) •
        (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
        PowerSeries.X ^ r

/-- Theorem 9: for `r ≥ 2`, with `C^{r+}(x,u) = ∑_{n ≥ r+1} C_n(x) u^n/n!` the
excedance generating function over circular permutations of more than `r` objects,
`C^{r+}(x,u) = ln (A(x,u) exp(-u - x ∑_{i=1}^{r-1} A_i(x) u^{i+1}/(i+1)!))`, stated as
`exp C^{r+}(x,u) = A(x,u) exp(-u - x ∑ …)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 9 (`jis-2025-25.5.7-thm-9`). -/
public theorem_wanted exp_circularRPlusPermEGF_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 2 ≤ r) :
    PowerSeries.subst
        (permExcedanceCycleEGF (fun n σ => (0 < n ∧ ∀ i j, σ.SameCycle i j) ∧ r + 1 ≤ n) x 1)
        (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1 *
        PowerSeries.subst
          (-(PowerSeries.X + ∑ i ∈ Finset.Icc 1 (r - 1),
            PowerSeries.C ((((i + 1).factorial : ℚ)⁻¹) •
              (x * ∑ σ : Equiv.Perm (Fin i), x ^ excedanceCount i σ)) *
              PowerSeries.X ^ (i + 1)))
          (PowerSeries.exp R)

/-- Theorem 11: for `r ≥ 2`, the exponential generating function of the
`r^-`-associated Stirling Eulerian numbers (permutations with all cycle lengths at most
`r`, by excedances) is
`A^{r-}(x,u) = exp(u + x ∑_{j=1}^{r-1} A_j(x) u^{j+1}/(j+1)!)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 11 (`jis-2025-25.5.7-thm-11`). -/
public theorem_wanted rMinusAssociatedPermEGF_eq_exp {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1 =
      PowerSeries.subst
        (PowerSeries.X + ∑ j ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C ((((j + 1).factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin j), x ^ excedanceCount j σ)) *
            PowerSeries.X ^ (j + 1))
        (PowerSeries.exp R)

/-- Corollary 12: for `r ≥ 2`, `C^{r-}(x,u) = ln A^{r-}(x,u)`, stated as
`exp C^{r-}(x,u) = A^{r-}(x,u)`, with `C^{r-}` the excedance generating function over
circular permutations of at most `r` objects (Theorem 7).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 12 (`jis-2025-25.5.7-cor-12`). -/
public theorem_wanted exp_circularRMinusPermEGF_eq_rMinusAssociatedPermEGF {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (r : ℕ) (hr : 2 ≤ r) :
    PowerSeries.subst
        (permExcedanceCycleEGF (fun n σ => (0 < n ∧ ∀ i j, σ.SameCycle i j) ∧ n ≤ r) x 1)
        (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1

/-- Corollary 13: the primitive `P(x,u)` in `u` of the Eulerian exponential generating
function `A(x,u)` (the one vanishing at `u = 0`) satisfies
`P(x,u) = (ln A(x,u) + u(x-1))/x`. Stated with the division by `x` cleared and the
logarithm exponentiated: `exp(x P(x,u) - (x-1)u) = A(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 13 (`jis-2025-25.5.7-cor-13`). -/
public theorem_wanted exp_eulerianEGF_primitive {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (P : PowerSeries R) (hP0 : PowerSeries.constantCoeff P = 0)
    (hP : PowerSeries.derivative (R := R) P = permExcedanceCycleEGF (fun _ _ => True) x 1) :
    PowerSeries.subst (PowerSeries.C x * P - PowerSeries.C (x - 1) * PowerSeries.X)
        (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1

/-- Theorem 14: for `r ≥ 2` and `k ≥ 0`, the excedance generating function over
permutations with all cycle lengths at most `r` and exactly `k` cycles is
`A^{r-}_k(x,u) = (ln A^{r-}(x,u))^k/k! = (u + x ∑_{n=1}^{r-1} A_n(x) u^{n+1}/(n+1)!)^k/k!`.
Both equalities are stated; the logarithm as any `L` with `L(0) = 0` and
`exp L = A^{r-}(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 14 (`jis-2025-25.5.7-thm-14`). -/
public theorem_wanted rMinusAssociatedPermEGF_cycleCount_eq {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (r k : ℕ) (hr : 2 ≤ r) :
    (∀ L : PowerSeries R, PowerSeries.constantCoeff L = 0 →
      PowerSeries.subst L (PowerSeries.exp R) =
        permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1 →
      permExcedanceCycleEGF
          (fun n σ => IsRMinusAssociatedCyclePerm r n σ ∧ cycleQuotientCount σ = k) x 1 =
        ((k.factorial : ℚ)⁻¹) • L ^ k) ∧
    permExcedanceCycleEGF
        (fun n σ => IsRMinusAssociatedCyclePerm r n σ ∧ cycleQuotientCount σ = k) x 1 =
      ((k.factorial : ℚ)⁻¹) •
        (PowerSeries.X + ∑ j ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C ((((j + 1).factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin j), x ^ excedanceCount j σ)) *
            PowerSeries.X ^ (j + 1)) ^ k

/-- Theorem 15: for `r ≥ 2`, the `q`-analogue (`q` marking cycles) of the exponential
generating function of the `r^-`-associated Stirling Eulerian numbers is
`A^{r-}(q,x,u) = exp(q(u + x ∑_{j=1}^{r-1} A_j(x) u^{j+1}/(j+1)!))`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 15 (`jis-2025-25.5.7-thm-15`). -/
public theorem_wanted rMinusAssociatedPermEGF_q_eq_exp {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (r : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x q =
      PowerSeries.subst
        (PowerSeries.C q * (PowerSeries.X + ∑ j ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C ((((j + 1).factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin j), x ^ excedanceCount j σ)) *
            PowerSeries.X ^ (j + 1)))
        (PowerSeries.exp R)

/-- Corollary 16: for `r ≥ 2`, `A^{r-}(q,x,u) = (A^{r-}(x,u))^q`, with the power read
as `exp(q ln A^{r-}(x,u))`: for every `L` with `L(0) = 0` and `exp L = A^{r-}(x,u)`,
`A^{r-}(q,x,u) = exp(q L)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 16 (`jis-2025-25.5.7-cor-16`). -/
public theorem_wanted rMinusAssociatedPermEGF_q_eq_pow {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (r : ℕ) (hr : 2 ≤ r) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1) :
    permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x q =
      PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- Theorem 20: for `r ≥ 2` and `0 ≤ m ≤ n`, the numbers `A^{(r)}_{n,m}` of permutations
with all cycle lengths equal to `r` and `m` excedances satisfy
`A^{(r)}_{n+1,m} = C(n, r-1) ∑_{k ≥ 1} C_{r,k} A^{(r)}_{n-(r-1),m-k}`. The sum runs over
`1 ≤ k ≤ m` (terms with `m - k < 0` vanish); for `n < r - 1` the index `n - (r-1)` is
truncated to `0` in `ℕ`, harmless because then `C(n, r-1) = 0`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 20 (`jis-2025-25.5.7-thm-20`). -/
public theorem_wanted rCycleStirlingEulerian_succ (r n m : ℕ) (hr : 2 ≤ r) (hm : m ≤ n) :
    rCycleStirlingEulerian r (n + 1) m =
      n.choose (r - 1) * ∑ k ∈ Finset.Icc 1 m,
        circularEulerian r k * rCycleStirlingEulerian r (n - (r - 1)) (m - k)

/-- Theorem 21: for `r ≥ 2`, the exponential generating function of the numbers
`A^{(r)}_{n,m}` (all cycle lengths equal to `r`, by excedances) is
`A^{(r)}(x,u) = exp(x A_{r-1}(x) u^r/r!)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 21 (`jis-2025-25.5.7-thm-21`). -/
public theorem_wanted rCyclePermEGF_eq_exp {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (IsRCyclePerm r) x 1 =
      PowerSeries.subst
        (PowerSeries.C (((r.factorial : ℚ)⁻¹) •
          (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
          PowerSeries.X ^ r)
        (PowerSeries.exp R)

/-- Theorem 22: for `r ≥ 2` and `k ≥ 0`, the excedance generating function over
permutations with all cycle lengths equal to `r` and exactly `k` cycles is
`A^{(r)}_k(x,u) = (x A_{r-1}(x) u^r/r!)^k/k! = (ln A^{(r)}(x,u))^k/k!`. Both equalities
are stated; the logarithm as any `L` with `L(0) = 0` and `exp L = A^{(r)}(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 22 (`jis-2025-25.5.7-thm-22`). -/
public theorem_wanted rCyclePermEGF_cycleCount_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r k : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (fun n σ => IsRCyclePerm r n σ ∧ cycleQuotientCount σ = k) x 1 =
        ((k.factorial : ℚ)⁻¹) •
          (PowerSeries.C (((r.factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
            PowerSeries.X ^ r) ^ k ∧
    ∀ L : PowerSeries R, PowerSeries.constantCoeff L = 0 →
      PowerSeries.subst L (PowerSeries.exp R) = permExcedanceCycleEGF (IsRCyclePerm r) x 1 →
      permExcedanceCycleEGF (fun n σ => IsRCyclePerm r n σ ∧ cycleQuotientCount σ = k) x 1 =
        ((k.factorial : ℚ)⁻¹) • L ^ k

/-- Theorem 23: for `r ≥ 2`, the `q`-analogue (`q` marking cycles) of the exponential
generating function of the numbers `A^{(r)}_{n,m,k}` (all cycle lengths equal to `r`,
`m` excedances, `k` cycles) is `A^{(r)}(q,x,u) = exp(q x A_{r-1}(x) u^r/r!)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 23 (`jis-2025-25.5.7-thm-23`). -/
public theorem_wanted rCyclePermEGF_q_eq_exp {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) (r : ℕ) (hr : 2 ≤ r) :
    permExcedanceCycleEGF (IsRCyclePerm r) x q =
      PowerSeries.subst
        (PowerSeries.C q * (PowerSeries.C (((r.factorial : ℚ)⁻¹) •
          (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
          PowerSeries.X ^ r))
        (PowerSeries.exp R)

/-- Corollary 24: for `r ≥ 2`, `n` and `k`, summing over the permutations `π` of `n`
objects with all cycle lengths equal to `r` and exactly `k` cycles,
`∑ x^{e(π)} q^{c(π)} = (rk)!/((r!)^k k!) x^k q^k A_{r-1}(x)^k` if `n = kr`, and `0`
otherwise. The quotient `(rk)!/((r!)^k k!)` is an exact natural-number division.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 24 (`jis-2025-25.5.7-cor-24`). -/
public theorem_wanted sum_rCyclePerm_cycleCount_eq {R : Type*} [CommRing R] (x q : R)
    (r n k : ℕ) (hr : 2 ≤ r) :
    ∑ σ ∈ Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => IsRCyclePerm r n σ ∧ cycleQuotientCount σ = k),
      x ^ excedanceCount n σ * q ^ cycleQuotientCount σ =
    if n = k * r then
      (((r * k).factorial / (r.factorial ^ k * k.factorial) : ℕ) : R) * x ^ k * q ^ k *
        (∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ) ^ k
    else 0

/-- Corollary 25: for `r ≥ 2`, the number of permutations of `n` objects with all cycle
lengths equal to `r` is `n!/(r^{n/r} (n/r)!)` if `r ∣ n` and `0` otherwise (exact
natural-number division).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 25 (`jis-2025-25.5.7-cor-25`). -/
public theorem_wanted card_rCyclePerm (r n : ℕ) (hr : 2 ≤ r) :
    (Finset.univ.filter (IsRCyclePerm r n)).card =
      if r ∣ n then n.factorial / (r ^ (n / r) * (n / r).factorial) else 0

/-- Corollary 26: for `r ≥ 2`, `∑_{n ≥ 0} |S_n^r| u^n/n! = exp(u^r/r)`, with `S_n^r`
the permutations of `n` objects with all cycle lengths equal to `r`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 26 (`jis-2025-25.5.7-cor-26`). -/
public theorem_wanted rCyclePermCountEGF_eq_exp (r : ℕ) (hr : 2 ≤ r) :
    PowerSeries.mk (fun n => ((Finset.univ.filter (IsRCyclePerm r n)).card : ℚ) /
        n.factorial) =
      PowerSeries.subst (PowerSeries.C ((r : ℚ)⁻¹) * PowerSeries.X ^ r) (PowerSeries.exp ℚ)

/-- Theorem 32: for `r ≥ 1`, the exponential generating function of the `r`-associated
Stirling Eulerian numbers (all cycle lengths greater than `r`, by excedances) is
`A^r(x,u) = A(x,u) exp(-u - x ∑_{j=1}^{r-1} A_j(x) u^{j+1}/(j+1)!)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 32 (`jis-2025-25.5.7-thm-32`). -/
public theorem_wanted rAssociatedPermEGF_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (r : ℕ) (hr : 1 ≤ r) :
    permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1 =
      permExcedanceCycleEGF (fun _ _ => True) x 1 *
        PowerSeries.subst
          (-(PowerSeries.X + ∑ j ∈ Finset.Icc 1 (r - 1),
            PowerSeries.C ((((j + 1).factorial : ℚ)⁻¹) •
              (x * ∑ σ : Equiv.Perm (Fin j), x ^ excedanceCount j σ)) *
              PowerSeries.X ^ (j + 1)))
          (PowerSeries.exp R)

/-- Corollary 33: for every `r ≥ 0`, `C^{r+}(x,u) = ln A^r(x,u)`, stated as
`exp C^{r+}(x,u) = A^r(x,u)`, with `C^{r+}(x,u) = ∑_{n ≥ r+1} C_n(x) u^n/n!` (Theorem 9)
and `A^r` the generating function of permutations with all cycle lengths greater
than `r`. The record states no bound on `r`; at `r = 0` this is Theorem 6.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 33 (`jis-2025-25.5.7-cor-33`). -/
public theorem_wanted exp_circularRPlusPermEGF_eq_rAssociatedPermEGF {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (r : ℕ) :
    PowerSeries.subst
        (permExcedanceCycleEGF (fun n σ => (0 < n ∧ ∀ i j, σ.SameCycle i j) ∧ r + 1 ≤ n) x 1)
        (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1

/-- Theorem 34: for every `r ≥ 0` and `k ≥ 0`, the excedance generating function over
permutations with all cycle lengths greater than `r` and exactly `k` cycles is
`A^r_k(x,u) = (ln A^r(x,u))^k/k!`, the logarithm read as any `L` with `L(0) = 0` and
`exp L = A^r(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 34 (`jis-2025-25.5.7-thm-34`). -/
public theorem_wanted rAssociatedPermEGF_cycleCount_eq {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (r k : ℕ) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1) :
    permExcedanceCycleEGF (fun n σ => IsRAssociatedCyclePerm r n σ ∧ cycleQuotientCount σ = k) x 1 =
      ((k.factorial : ℚ)⁻¹) • L ^ k

/-- Theorem 35: for every `r ≥ 0`, `A^r(q,x,u) = (A^r(x,u))^q` (`q` marking cycles),
with the power read as `exp(q ln A^r(x,u))`: for every `L` with `L(0) = 0` and
`exp L = A^r(x,u)`, `A^r(q,x,u) = exp(q L)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 35 (`jis-2025-25.5.7-thm-35`). -/
public theorem_wanted rAssociatedPermEGF_q_eq_pow {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) (r : ℕ) (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1) :
    permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x q =
      PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- Corollary 39: over involutions (all cycle lengths at most `2`), the `q`-analogue
excedance generating function is `A^{2-}(q,x,u) = exp(q(u + x u^2/2))`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 39 (`jis-2025-25.5.7-cor-39`). -/
public theorem_wanted involutionEGF_q_eq_exp {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) :
    permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm 2) x q =
      PowerSeries.subst
        (PowerSeries.C q * (PowerSeries.X + PowerSeries.C ((2 : ℚ)⁻¹ • x) * PowerSeries.X ^ 2))
        (PowerSeries.exp R)

/-- Corollary 41: over fixed-point-free involutions (all cycle lengths equal to `2`),
the `q`-analogue excedance generating function is `A^{(2)}(q,x,u) = exp(q x u^2/2)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 41 (`jis-2025-25.5.7-cor-41`). -/
public theorem_wanted fixedPointFreeInvolutionEGF_q_eq_exp {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) :
    permExcedanceCycleEGF (IsRCyclePerm 2) x q =
      PowerSeries.subst (PowerSeries.C ((2 : ℚ)⁻¹ • (q * x)) * PowerSeries.X ^ 2)
        (PowerSeries.exp R)

/-- Corollary 43: for every `k ≥ 0`, the excedance generating function over permutations
with exactly `k` cycles is `A_k(x,u) = (ln A(x,u))^k/k!`, the logarithm read as any `L`
with `L(0) = 0` and `exp L = A(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 43 (`jis-2025-25.5.7-cor-43`). -/
public theorem_wanted permEGF_cycleCount_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x : R) (k : ℕ) (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    permExcedanceCycleEGF (fun _ σ => cycleQuotientCount σ = k) x 1 = ((k.factorial : ℚ)⁻¹) • L ^ k

/-- Corollary 44 (Brenti): the `q`-analogue (`q` marking cycles) of the excedance
generating function over all permutations is `A(q,x,u) = (A(x,u))^q`, the power read as
`exp(q ln A(x,u))`: for every `L` with `L(0) = 0` and `exp L = A(x,u)`,
`A(q,x,u) = exp(q L)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 44 (`jis-2025-25.5.7-cor-44`). -/
public theorem_wanted permEGF_q_eq_pow {R : Type*} [CommRing R] [Algebra ℚ R] (x q : R)
    (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    permExcedanceCycleEGF (fun _ _ => True) x q =
      PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-! ### First `s` points in distinct cycles (Theorems 17-38, 57-66, Corollaries 40-61)

The paper's bracket `[F]_s` is the generating function `F` restricted to permutations
whose first `s` points (`0, …, s-1` in `Fin n`) lie in distinct cycles, and
`∂^s [F]_s/∂u^s` is the `s`-th iterated `u`-derivative, written
`(PowerSeries.derivative (R := R))^[s]`. Logarithms and `q`-th powers are read as in the
section above. -/

/-- The first `s` points of `Fin n` lie in pairwise distinct cycles of `σ`: two points
`i, j < s` in the same cycle are equal. This is the side condition of the paper's
`(r^-,k,s)`-, `(r^+,⋆,s)`-, `((r),k,s)`-cycle and `s`-fixed-points permutations. When
`n < s`, only the points below `n` are constrained.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Section 1 (definitions of `(r^-,k,s)`-cycle and
`s`-fixed-points permutations). -/
public def FirstPointsInDistinctCycles (s n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, (i : ℕ) < s → (j : ℕ) < s → σ.SameCycle i j → i = j

public instance (s n : ℕ) : DecidablePred (FirstPointsInDistinctCycles s n) :=
  fun σ => by unfold FirstPointsInDistinctCycles; infer_instance

/-- For `s = 0` the condition is vacuous.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Section 1. -/
public theorem firstPointsInDistinctCycles_zero (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    FirstPointsInDistinctCycles 0 n σ :=
  fun _ _ hi => absurd hi (Nat.not_lt_zero _)

/-- The identity permutation puts every point in its own cycle.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Section 1. -/
public theorem firstPointsInDistinctCycles_one (s n : ℕ) : FirstPointsInDistinctCycles s n 1 :=
  fun _ _ _ _ h => Equiv.Perm.sameCycle_one.mp h

/-- Characteristic values: the transposition `(0 1)` of `Fin 3` keeps the first point
alone in its cycle but puts the first two points in one cycle.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Section 1. -/
public theorem firstPointsInDistinctCycles_swap :
    FirstPointsInDistinctCycles 1 3 (Equiv.swap 0 1) ∧
      ¬ FirstPointsInDistinctCycles 2 3 (Equiv.swap 0 1) := by
  decide

/-- Theorem 17: for `r ≥ 1`, over permutations with all cycle lengths at most `r` whose
first `s` points lie in distinct cycles,
`∂^s [A^{r-}(x,u)]_s/∂u^s = (1 + x ∑_{i=1}^{r-1} A_i(x) u^i/i!)^s A^{r-}(x,u)`.
The paper states `r ≥ 2`; `r = 1` also holds (both sides are `exp u`). At `r = 0` it
fails (`s = 1`: the left side is `0`, the right side `1`).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 17 (`jis-2025-25.5.7-thm-17`). -/
public theorem_wanted rMinusAssociatedPermEGF_firstPoints_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (r s : ℕ) (hr : 1 ≤ r) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRMinusAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ)
          x 1) =
      (1 + ∑ i ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C (((i.factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin i), x ^ excedanceCount i σ)) * PowerSeries.X ^ i) ^ s *
        permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1

/-- Theorem 18: for `r ≥ 1` and `k ≥ s`, over permutations with all cycle lengths at most
`r`, exactly `k` cycles, and the first `s` points in distinct cycles,
`∂^s [A^{r-}_k(x,u)]_s/∂u^s = (1 + x ∑_{i=1}^{r-1} A_i(x) u^i/i!)^s
(ln A^{r-}(x,u))^{k-s}/(k-s)!`, the logarithm read as any `L` with `L(0) = 0` and
`exp L = A^{r-}(x,u)`. The record states no bounds; `k ≥ s` makes `(k-s)!` defined (for
`k < s` the class is empty), and `r = 0` fails (`s = k = 1`: left side `0`, right side
`1`).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 18 (`jis-2025-25.5.7-thm-18`). -/
public theorem_wanted rMinusAssociatedPermEGF_firstPoints_cycleCount_iterate_derivative
    {R : Type*} [CommRing R] [Algebra ℚ R] (x : R) (r s k : ℕ) (hr : 1 ≤ r) (hk : s ≤ k)
    (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (IsRMinusAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) ∧
            cycleQuotientCount σ = k) x 1) =
      (1 + ∑ i ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C (((i.factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin i), x ^ excedanceCount i σ)) * PowerSeries.X ^ i) ^ s *
        ((((k - s).factorial : ℚ)⁻¹) • L ^ (k - s))

/-- Theorem 19: for `r ≥ 1`, the `q`-analogue (`q` marking cycles) over permutations with
all cycle lengths at most `r` and the first `s` points in distinct cycles satisfies
`∂^s [A^{r-}(q,x,u)]_s/∂u^s = q^s (1 + x ∑_{i=1}^{r-1} A_i(x) u^i/i!)^s (A^{r-}(x,u))^q`,
the power read as `exp(q L)` for any `L` with `L(0) = 0` and `exp L = A^{r-}(x,u)`. The
record states no bound on `r`; `r = 0` fails as in Theorem 17.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 19 (`jis-2025-25.5.7-thm-19`). -/
public theorem_wanted rMinusAssociatedPermEGF_firstPoints_q_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x q : R) (r s : ℕ) (hr : 1 ≤ r) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRMinusAssociatedCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRMinusAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ)
          x q) =
      PowerSeries.C (q ^ s) *
        (1 + ∑ i ∈ Finset.Icc 1 (r - 1),
          PowerSeries.C (((i.factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin i), x ^ excedanceCount i σ)) * PowerSeries.X ^ i) ^ s *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- Theorem 27: for `r ≥ 2`, over permutations with all cycle lengths equal to `r` and the
first `s` points in distinct cycles,
`∂^s [A^{(r)}(x,u)]_s/∂u^s = x^s (A_{r-1}(x) u^{r-1}/(r-1)!)^s A^{(r)}(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 27 (`jis-2025-25.5.7-thm-27`). -/
public theorem_wanted rCyclePermEGF_firstPoints_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (r s : ℕ) (hr : 2 ≤ r) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) x 1) =
      PowerSeries.C (x ^ s) *
        (PowerSeries.C ((((r - 1).factorial : ℚ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ) *
          PowerSeries.X ^ (r - 1)) ^ s *
        permExcedanceCycleEGF (IsRCyclePerm r) x 1

/-- Theorem 28: for `r ≥ 2` and `k ≥ s`, over permutations with all cycle lengths equal to
`r`, exactly `k` cycles, and the first `s` points in distinct cycles,
`∂^s [A^{(r)}_k(x,u)]_s/∂u^s = x^s (A_{r-1}(x) u^{r-1}/(r-1)!)^s
(ln A^{(r)}(x,u))^{k-s}/(k-s)!`, the logarithm read as any `L` with `L(0) = 0` and
`exp L = A^{(r)}(x,u)`; `k ≥ s` makes `(k-s)!` defined.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 28 (`jis-2025-25.5.7-thm-28`). -/
public theorem_wanted rCyclePermEGF_firstPoints_cycleCount_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (r s k : ℕ) (hr : 2 ≤ r) (hk : s ≤ k)
    (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) = permExcedanceCycleEGF (IsRCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (IsRCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) ∧
            cycleQuotientCount σ = k) x 1) =
      PowerSeries.C (x ^ s) *
        (PowerSeries.C ((((r - 1).factorial : ℚ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ) *
          PowerSeries.X ^ (r - 1)) ^ s *
        ((((k - s).factorial : ℚ)⁻¹) • L ^ (k - s))

/-- Theorem 29: for `r ≥ 2`, the `q`-analogue over permutations with all cycle lengths
equal to `r` and the first `s` points in distinct cycles satisfies
`∂^s [A^{(r)}(q,x,u)]_s/∂u^s = q^s x^s (A_{r-1}(x) u^{r-1}/(r-1)!)^s (A^{(r)}(x,u))^q`,
the power read as `exp(q L)` for any `L` with `L(0) = 0` and `exp L = A^{(r)}(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 29 (`jis-2025-25.5.7-thm-29`). -/
public theorem_wanted rCyclePermEGF_firstPoints_q_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (r s : ℕ) (hr : 2 ≤ r) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) = permExcedanceCycleEGF (IsRCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) x q) =
      PowerSeries.C (q ^ s * x ^ s) *
        (PowerSeries.C ((((r - 1).factorial : ℚ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ) *
          PowerSeries.X ^ (r - 1)) ^ s *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- Theorem 36: for `r ≥ 1`, over permutations with all cycle lengths greater than `r` and
the first `s` points in distinct cycles,
`∂^s [A^r(x,u)]_s/∂u^s = x^s (A(x,u) - ∑_{n=0}^{r-1} A_n(x) u^n/n!)^s A^r(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 36 (`jis-2025-25.5.7-thm-36`). -/
public theorem_wanted rAssociatedPermEGF_firstPoints_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (r s : ℕ) (hr : 1 ≤ r) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) x 1) =
      PowerSeries.C (x ^ s) *
        (permExcedanceCycleEGF (fun _ _ => True) x 1 - ∑ n ∈ Finset.range r,
          PowerSeries.C (((n.factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin n), x ^ excedanceCount n σ) * PowerSeries.X ^ n) ^ s *
        permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1

/-- Theorem 37: for `r ≥ 1` and `k ≥ s`, over permutations with all cycle lengths greater
than `r`, exactly `k` cycles, and the first `s` points in distinct cycles,
`∂^s [A^r_k(x,u)]_s/∂u^s = x^s (A(x,u) - ∑_{n=0}^{r-1} A_n(x) u^n/n!)^s
(ln A^r(x,u))^{k-s}/(k-s)!`, the logarithm read as any `L` with `L(0) = 0` and
`exp L = A^r(x,u)`; `k ≥ s` makes `(k-s)!` defined.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 37 (`jis-2025-25.5.7-thm-37`). -/
public theorem_wanted rAssociatedPermEGF_firstPoints_cycleCount_iterate_derivative
    {R : Type*} [CommRing R] [Algebra ℚ R] (x : R) (r s k : ℕ) (hr : 1 ≤ r) (hk : s ≤ k)
    (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (IsRAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) ∧
            cycleQuotientCount σ = k) x 1) =
      PowerSeries.C (x ^ s) *
        (permExcedanceCycleEGF (fun _ _ => True) x 1 - ∑ n ∈ Finset.range r,
          PowerSeries.C (((n.factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin n), x ^ excedanceCount n σ) * PowerSeries.X ^ n) ^ s *
        ((((k - s).factorial : ℚ)⁻¹) • L ^ (k - s))

/-- Theorem 38: for `r ≥ 1`, the `q`-analogue over permutations with all cycle lengths
greater than `r` and the first `s` points in distinct cycles satisfies
`∂^s [A^r(q,x,u)]_s/∂u^s = q^s x^s (A(x,u) - ∑_{n=0}^{r-1} A_n(x) u^n/n!)^s (A^r(x,u))^q`,
the power read as `exp(q L)` for any `L` with `L(0) = 0` and `exp L = A^r(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 38 (`jis-2025-25.5.7-thm-38`). -/
public theorem_wanted rAssociatedPermEGF_firstPoints_q_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x q : R) (r s : ℕ) (hr : 1 ≤ r) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (IsRAssociatedCyclePerm r) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRAssociatedCyclePerm r n σ ∧ FirstPointsInDistinctCycles s n σ) x q) =
      PowerSeries.C (q ^ s * x ^ s) *
        (permExcedanceCycleEGF (fun _ _ => True) x 1 - ∑ n ∈ Finset.range r,
          PowerSeries.C (((n.factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin n), x ^ excedanceCount n σ) * PowerSeries.X ^ n) ^ s *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- Corollary 40: over involutions of `2n` and `2n+1` objects,
`∑_{π ∈ I_{2n}} x^{e(π)} q^{c(π)} = ∑_{k=0}^{n} (2n)!/(2^{n-k}(2k)!(n-k)!) q^{n+k} x^{n-k}`
and `∑_{π ∈ I_{2n+1}} x^{e(π)} q^{c(π)} =
∑_{k=0}^{n} (2n+1)!/(2^{n-k}(2k+1)!(n-k)!) q^{n+k+1} x^{n-k}`. The record (and the paper)
print the summation index as `j` while the summands use `k`; the sums are read over `k`,
the reading forced by Corollary 39 (`exp(q(u + x u^2/2))`, `n - k` two-cycles and `2k`
or `2k+1` fixed points).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 40 (`jis-2025-25.5.7-cor-40`). -/
public theorem_wanted involution_excedance_cycle_sum {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) (n : ℕ) :
    (∑ σ ∈ Finset.univ.filter (IsRMinusAssociatedCyclePerm 2 (2 * n)),
        x ^ excedanceCount (2 * n) σ * q ^ cycleQuotientCount σ =
      ∑ k ∈ Finset.range (n + 1),
        (((2 * n).factorial : ℚ) / (2 ^ (n - k) * (2 * k).factorial * (n - k).factorial)) •
          (q ^ (n + k) * x ^ (n - k))) ∧
    ∑ σ ∈ Finset.univ.filter (IsRMinusAssociatedCyclePerm 2 (2 * n + 1)),
        x ^ excedanceCount (2 * n + 1) σ * q ^ cycleQuotientCount σ =
      ∑ k ∈ Finset.range (n + 1),
        (((2 * n + 1).factorial : ℚ) /
            (2 ^ (n - k) * (2 * k + 1).factorial * (n - k).factorial)) •
          (q ^ (n + k + 1) * x ^ (n - k))

/-- Corollary 42: over fixed-point-free involutions of `2n` objects,
`∑_{π ∈ I_{2n} ∩ D_{2n}} x^{e(π)} q^{c(π)} = (2n)!/(2^n n!) q^n x^n`. The record (and the
paper) print the right side as `∑_{j=0}^{n}` of a summand free of `j`, which is
`n + 1` times too large (`n = 1`: the only such involution `(1 2)` gives `q x`, the
printed sum `2 q x`); the single term is the reading forced by Corollary 41
(`exp(q x u^2/2)`).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 42 (`jis-2025-25.5.7-cor-42`). -/
public theorem_wanted fixedPointFreeInvolution_excedance_cycle_sum {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (n : ℕ) :
    ∑ σ ∈ Finset.univ.filter (IsRCyclePerm 2 (2 * n)),
        x ^ excedanceCount (2 * n) σ * q ^ cycleQuotientCount σ =
      (((2 * n).factorial : ℚ) / (2 ^ n * n.factorial)) • (q ^ n * x ^ n)

/-- Corollary 45: over permutations whose first `s` points lie in distinct cycles,
`∂^s [A(x,u)]_s/∂u^s = (A(x,u) exp(u(x-1)))^s A(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 45 (`jis-2025-25.5.7-cor-45`). -/
public theorem_wanted permEGF_firstPoints_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (s : ℕ) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF (FirstPointsInDistinctCycles s) x 1) =
      (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        permExcedanceCycleEGF (fun _ _ => True) x 1

/-- Corollary 46: for `k ≥ s`, over permutations with exactly `k` cycles whose first `s`
points lie in distinct cycles,
`∂^s [A_k(x,u)]_s/∂u^s = (A(x,u) exp(u(x-1)))^s (ln A(x,u))^{k-s}/(k-s)!`, the logarithm
read as any `L` with `L(0) = 0` and `exp L = A(x,u)`; `k ≥ s` makes `(k-s)!` defined.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 46 (`jis-2025-25.5.7-cor-46`). -/
public theorem_wanted permEGF_firstPoints_cycleCount_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (s k : ℕ) (hk : s ≤ k) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => FirstPointsInDistinctCycles s n σ ∧ cycleQuotientCount σ = k) x 1) =
      (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        ((((k - s).factorial : ℚ)⁻¹) • L ^ (k - s))

/-- Corollary 47: the `q`-analogue over permutations whose first `s` points lie in distinct
cycles satisfies `∂^s [A(q,x,u)]_s/∂u^s = q^s (A(x,u) exp(u(x-1)))^s (A(x,u))^q`, the power
read as `exp(q L)` for any `L` with `L(0) = 0` and `exp L = A(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 47 (`jis-2025-25.5.7-cor-47`). -/
public theorem_wanted permEGF_firstPoints_q_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (s : ℕ) (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF (FirstPointsInDistinctCycles s) x q) =
      PowerSeries.C (q ^ s) *
        (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- Corollary 48: summing over permutations of `n + s` objects whose first `s` points lie
in distinct cycles, `∑ x^{e(σ)} (-s)^{c(σ)} = (-1)^s s^{n+s} (x-1)^n`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 48 (`jis-2025-25.5.7-cor-48`). -/
public theorem_wanted firstPoints_excedance_cycle_sum_neg {R : Type*} [CommRing R] (x : R)
    (n s : ℕ) :
    ∑ σ ∈ Finset.univ.filter (FirstPointsInDistinctCycles s (n + s)),
        x ^ excedanceCount (n + s) σ * (-(s : R)) ^ cycleQuotientCount σ =
      (-1) ^ s * (s : R) ^ (n + s) * (x - 1) ^ n

/-- Corollary 49: for `n ≥ 1`, summing over permutations of `n + s` objects whose first `s`
points lie in distinct cycles,
`∑ x^{e(σ)} (-s-1)^{c(σ)} = (-1)^s (s+1)^s (x s^n - (s+1)^n) (x-1)^{n-1}`. Restricted to
`n ≥ 1`, where `(x-1)^{n-1}` is a polynomial.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 49 (`jis-2025-25.5.7-cor-49`). -/
public theorem_wanted firstPoints_excedance_cycle_sum_neg_succ {R : Type*} [CommRing R]
    (x : R) (n s : ℕ) (hn : 1 ≤ n) :
    ∑ σ ∈ Finset.univ.filter (FirstPointsInDistinctCycles s (n + s)),
        x ^ excedanceCount (n + s) σ * (-((s : R) + 1)) ^ cycleQuotientCount σ =
      (-1) ^ s * ((s : R) + 1) ^ s * (x * (s : R) ^ n - ((s : R) + 1) ^ n) * (x - 1) ^ (n - 1)

/-- Corollary 51: the `q`-analogue over derangements whose first `s` points lie in
distinct cycles satisfies
`∂^s [A^1(q,x,u)]_s/∂u^s = q^s x^s (A(x,u) - 1)^s (A(x,u) exp(-u))^q`, the power read as
`exp(q (L - u))` for any `L` with `L(0) = 0` and `exp L = A(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 51 (`jis-2025-25.5.7-cor-51`). -/
public theorem_wanted derangementEGF_firstPoints_q_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x q : R) (s : ℕ) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => IsRAssociatedCyclePerm 1 n σ ∧ FirstPointsInDistinctCycles s n σ) x q) =
      PowerSeries.C (q ^ s * x ^ s) * (permExcedanceCycleEGF (fun _ _ => True) x 1 - 1) ^ s *
        PowerSeries.subst (PowerSeries.C q * (L - PowerSeries.X)) (PowerSeries.exp R)

/-- Corollary 52: summing over derangements of `n + s` objects whose first `s` points lie
in distinct cycles,
`∑ x^{e(σ)} (-s)^{c(σ)} = (-1)^s (s x/(x-1))^s ∑_{i_1+⋯+i_s=n, i_j ≥ 1}
(i_1,…,i_s)! ∏_j (x^{i_j} - 1)`, stated in `ℤ[X]` with the denominator `(x-1)^s` cleared
(equivalent, since `ℤ[X]` is a domain).

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 52 (`jis-2025-25.5.7-cor-52`). -/
public theorem_wanted derangement_firstPoints_excedance_cycle_sum_neg (n s : ℕ) :
    (X - 1 : ℤ[X]) ^ s *
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + s)) =>
            IsRAssociatedCyclePerm 1 (n + s) σ ∧ FirstPointsInDistinctCycles s (n + s) σ),
          X ^ excedanceCount (n + s) σ * (-(s : ℤ[X])) ^ cycleQuotientCount σ =
      (-1) ^ s * ((s : ℤ[X]) * X) ^ s *
        ∑ i ∈ (Finset.Nat.antidiagonalTuple s n).filter (fun i => ∀ j, 1 ≤ i j),
          (Nat.multinomial Finset.univ i : ℤ[X]) * ∏ j, (X ^ i j - 1)

/-- Corollary 54 (corrected): summing over derangements of `n + s` objects whose first `s`
points lie in distinct cycles,
`∑ x^{e(σ)} (-s-1)^{c(σ)} = (-1)^s (s+1)^s x^s/(x-1)^s ∑_{ℓ=0}^{n} C(n,ℓ) (x - x^ℓ)/(x-1)
∑_{i_1+⋯+i_s=n-ℓ, i_j ≥ 1} (i_1,…,i_s)! ∏_j (x^{i_j} - 1)`, stated in `ℤ[X]` with the
denominator `(x-1)^{s+1}` cleared. The record omits the binomial `C(n,ℓ)` and is false as
printed (`s = 1`, `n = 3`, `x = 2`: the left side is `-4`, the printed right side `-20`);
the binomial comes from the paper's own proof, which extracts the coefficient of
`u^n/n!` from the product of the exponential generating functions
`(∑_{n ≥ 1} (x^n - 1) u^n/n!)^s` and `∑_{n ≥ 0} (x - x^n)/(x-1) u^n/n!`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 54 (`jis-2025-25.5.7-cor-54`). -/
public theorem_wanted derangement_firstPoints_excedance_cycle_sum_neg_succ (n s : ℕ) :
    (X - 1 : ℤ[X]) ^ (s + 1) *
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + s)) =>
            IsRAssociatedCyclePerm 1 (n + s) σ ∧ FirstPointsInDistinctCycles s (n + s) σ),
          X ^ excedanceCount (n + s) σ * (-((s : ℤ[X]) + 1)) ^ cycleQuotientCount σ =
      (-1) ^ s * ((s : ℤ[X]) + 1) ^ s * X ^ s *
        ∑ l ∈ Finset.range (n + 1), (n.choose l : ℤ[X]) * (X - X ^ l) *
          ∑ i ∈ (Finset.Nat.antidiagonalTuple s (n - l)).filter (fun i => ∀ j, 1 ≤ i j),
            (Nat.multinomial Finset.univ i : ℤ[X]) * ∏ j, (X ^ i j - 1)

/-- Theorem 57: over `s`-fixed-points-permutations (every fixed point lies among the first
`s` points, and the first `s` points lie in distinct cycles),
`∂^s [F(x,u)]_s/∂u^s = (A(x,u) exp(u(x-1)))^s A(x,u) exp(-u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 57 (`jis-2025-25.5.7-thm-57`). -/
public theorem_wanted fixedPointsPermEGF_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (s : ℕ) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (∀ i : Fin n, σ i = i → (i : ℕ) < s) ∧ FirstPointsInDistinctCycles s n σ)
          x 1) =
      (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        permExcedanceCycleEGF (fun _ _ => True) x 1 *
        PowerSeries.subst (-PowerSeries.X) (PowerSeries.exp R)

/-- Theorem 58: for `k ≥ s`, over `s`-fixed-points-permutations with exactly `k` cycles,
`∂^s [F_k(x,u)]_s/∂u^s = (A(x,u) exp(u(x-1)))^s (ln(A(x,u) exp(-u)))^{k-s}/(k-s)!`, with
`ln(A(x,u) exp(-u))` read as `L - u` for any `L` with `L(0) = 0` and `exp L = A(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 58 (`jis-2025-25.5.7-thm-58`). -/
public theorem_wanted fixedPointsPermEGF_cycleCount_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (s k : ℕ) (hk : s ≤ k) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => ((∀ i : Fin n, σ i = i → (i : ℕ) < s) ∧
            FirstPointsInDistinctCycles s n σ) ∧ cycleQuotientCount σ = k) x 1) =
      (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        ((((k - s).factorial : ℚ)⁻¹) • (L - PowerSeries.X) ^ (k - s))

/-- Theorem 59: the `q`-analogue over `s`-fixed-points-permutations satisfies
`∂^s [F(q,x,u)]_s/∂u^s = q^s (A(x,u) exp(u(x-1)))^s (A(x,u))^q exp(-qu)`, the power read as
`exp(q L)` for any `L` with `L(0) = 0` and `exp L = A(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 59 (`jis-2025-25.5.7-thm-59`). -/
public theorem_wanted fixedPointsPermEGF_q_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (s : ℕ) (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (∀ i : Fin n, σ i = i → (i : ℕ) < s) ∧ FirstPointsInDistinctCycles s n σ)
          x q) =
      PowerSeries.C (q ^ s) *
        (permExcedanceCycleEGF (fun _ _ => True) x 1 *
          PowerSeries.subst (PowerSeries.C (x - 1) * PowerSeries.X) (PowerSeries.exp R)) ^ s *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R) *
        PowerSeries.subst (-(PowerSeries.C q * PowerSeries.X)) (PowerSeries.exp R)

/-- Corollary 60: for `n ≥ s`, summing over the `s`-fixed-points-permutations `𝓕_n^s` of
`n` objects, `∑ x^{e(π)} (-s)^{c(π)} = (-1)^s s^n x^{n-s}`. Restricted to `n ≥ s`, where
`x^{n-s}` is a monomial.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 60 (`jis-2025-25.5.7-cor-60`). -/
public theorem_wanted fixedPointsPerm_excedance_cycle_sum_neg {R : Type*} [CommRing R] (x : R)
    (n s : ℕ) (hn : s ≤ n) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (∀ i : Fin n, σ i = i → (i : ℕ) < s) ∧ FirstPointsInDistinctCycles s n σ),
        x ^ excedanceCount n σ * (-(s : R)) ^ cycleQuotientCount σ =
      (-1) ^ s * (s : R) ^ n * x ^ (n - s)

/-- Corollary 61: for `n ≥ s`, summing over the `s`-fixed-points-permutations `𝓕_n^s` of
`n` objects,
`∑ x^{e(π)} (-s-1)^{c(π)} = (-1)^s (s+1)^s (x(sx+1)^{n-s} - (s+1)^{n-s} x^{n-s})/(x-1)`,
stated in `ℤ[X]` with the denominator `x - 1` cleared and restricted to `n ≥ s`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 61 (`jis-2025-25.5.7-cor-61`). -/
public theorem_wanted fixedPointsPerm_excedance_cycle_sum_neg_succ (n s : ℕ) (hn : s ≤ n) :
    (X - 1 : ℤ[X]) *
        ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            (∀ i : Fin n, σ i = i → (i : ℕ) < s) ∧ FirstPointsInDistinctCycles s n σ),
          X ^ excedanceCount n σ * (-((s : ℤ[X]) + 1)) ^ cycleQuotientCount σ =
      (-1) ^ s * ((s : ℤ[X]) + 1) ^ s *
        (X * ((s : ℤ[X]) * X + 1) ^ (n - s) - ((s : ℤ[X]) + 1) ^ (n - s) * X ^ (n - s))

/-- Theorem 62: for lengths `r_1, …, r_s ≥ 2`, over permutations whose first `s` points lie
in distinct cycles with the point `i` in a cycle of length `r_i` (other cycles arbitrary),
`∂^s [A^{r_1⋯r_s}(x,u)]_s/∂u^s = x^s ∏_{i=1}^{s} A_{r_i-1}(x) u^{r_i-1}/(r_i-1)! · A(x,u)`.
The lengths are indexed `r 0, …, r (s-1)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 62 (`jis-2025-25.5.7-thm-62`). -/
public theorem_wanted prescribedCyclePermEGF_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x : R) (s : ℕ) (r : ℕ → ℕ) (hr : ∀ i < s, 2 ≤ r i) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => FirstPointsInDistinctCycles s n σ ∧ ∀ i : Fin n, (i : ℕ) < s →
            (Finset.univ.filter (σ.SameCycle i)).card = r i) x 1) =
      PowerSeries.C (x ^ s) *
        (∏ i ∈ Finset.range s,
          PowerSeries.C ((((r i - 1).factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin (r i - 1)), x ^ excedanceCount (r i - 1) σ) *
            PowerSeries.X ^ (r i - 1)) *
        permExcedanceCycleEGF (fun _ _ => True) x 1

/-- Theorem 63: for lengths `r_1, …, r_s ≥ 2` and `k ≥ s`, over permutations with exactly
`k` cycles whose first `s` points lie in distinct cycles with the point `i` in a cycle of
length `r_i`,
`∂^s [A^{r_1⋯r_s}_k(x,u)]_s/∂u^s = x^s ∏_{i=1}^{s} A_{r_i-1}(x) u^{r_i-1}/(r_i-1)! ·
(ln A(x,u))^{k-s}/(k-s)!`, the logarithm read as any `L` with `L(0) = 0` and
`exp L = A(x,u)`; `k ≥ s` makes `(k-s)!` defined.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 63 (`jis-2025-25.5.7-thm-63`). -/
public theorem_wanted prescribedCyclePermEGF_cycleCount_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x : R) (s k : ℕ) (r : ℕ → ℕ) (hr : ∀ i < s, 2 ≤ r i)
    (hk : s ≤ k) (L : PowerSeries R) (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (FirstPointsInDistinctCycles s n σ ∧ ∀ i : Fin n, (i : ℕ) < s →
            (Finset.univ.filter (σ.SameCycle i)).card = r i) ∧ cycleQuotientCount σ = k)
          x 1) =
      PowerSeries.C (x ^ s) *
        (∏ i ∈ Finset.range s,
          PowerSeries.C ((((r i - 1).factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin (r i - 1)), x ^ excedanceCount (r i - 1) σ) *
            PowerSeries.X ^ (r i - 1)) *
        ((((k - s).factorial : ℚ)⁻¹) • L ^ (k - s))

/-- Theorem 64: for lengths `r_1, …, r_s ≥ 2`, the `q`-analogue over permutations whose
first `s` points lie in distinct cycles with the point `i` in a cycle of length `r_i`
satisfies `∂^s [A^{r_1⋯r_s}(q,x,u)]_s/∂u^s =
q^s x^s ∏_{i=1}^{s} A_{r_i-1}(x) u^{r_i-1}/(r_i-1)! · (A(x,u))^q`, the power read as
`exp(q L)` for any `L` with `L(0) = 0` and `exp L = A(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 64 (`jis-2025-25.5.7-thm-64`). -/
public theorem_wanted prescribedCyclePermEGF_q_iterate_derivative {R : Type*} [CommRing R]
    [Algebra ℚ R] (x q : R) (s : ℕ) (r : ℕ → ℕ) (hr : ∀ i < s, 2 ≤ r i) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF (fun _ _ => True) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => FirstPointsInDistinctCycles s n σ ∧ ∀ i : Fin n, (i : ℕ) < s →
            (Finset.univ.filter (σ.SameCycle i)).card = r i) x q) =
      PowerSeries.C (q ^ s * x ^ s) *
        (∏ i ∈ Finset.range s,
          PowerSeries.C ((((r i - 1).factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin (r i - 1)), x ^ excedanceCount (r i - 1) σ) *
            PowerSeries.X ^ (r i - 1)) *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- Theorem 65: for a finite set `ℛ = {r_1 < ⋯ < r_ℓ}` of lengths `r_i ≥ 2`, the
`q`-analogue over permutations all of whose cycle lengths lie in `ℛ` is
`A^{(r_1)⋯(r_ℓ)}(q,x,u) = exp(q x ∑_{r ∈ ℛ} A_{r-1}(x) u^r/r!)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 65 (`jis-2025-25.5.7-thm-65`). -/
public theorem_wanted cycleLengthsInEGF_q_eq_exp {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) (ℛ : Finset ℕ) (hℛ : ∀ r ∈ ℛ, 2 ≤ r) :
    permExcedanceCycleEGF
        (fun n σ => ∀ i : Fin n, (Finset.univ.filter (σ.SameCycle i)).card ∈ ℛ) x q =
      PowerSeries.subst
        (PowerSeries.C q * ∑ r ∈ ℛ,
          PowerSeries.C (((r.factorial : ℚ)⁻¹) •
            (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
            PowerSeries.X ^ r)
        (PowerSeries.exp R)

/-- Theorem 66: for lengths `r_1, …, r_s ≥ 2` and a finite set `ℛ = {r_{s+1} < ⋯ < r_ℓ}` of
lengths `≥ 2`, the `q`-analogue over permutations whose first `s` points lie in distinct
cycles with the point `i` in a cycle of length `r_i`, all other cycles having lengths in
`ℛ`, satisfies `∂^s [A^{r_1⋯r_s(r_{s+1})⋯(r_ℓ)}(q,x,u)]_s/∂u^s =
q^s x^s ∏_{i=1}^{s} A_{r_i-1}(x) u^{r_i-1}/(r_i-1)! · (A^{(r_{s+1})⋯(r_ℓ)}(x,u))^q`, the
power read as `exp(q L)` for any `L` with `L(0) = 0` and `exp L = A^{(r_{s+1})⋯(r_ℓ)}(x,u)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Theorem 66 (`jis-2025-25.5.7-thm-66`). -/
public theorem_wanted prescribedCycleLengthsInEGF_q_iterate_derivative {R : Type*}
    [CommRing R] [Algebra ℚ R] (x q : R) (s : ℕ) (r : ℕ → ℕ) (hr : ∀ i < s, 2 ≤ r i)
    (ℛ : Finset ℕ) (hℛ : ∀ m ∈ ℛ, 2 ≤ m) (L : PowerSeries R)
    (hL0 : PowerSeries.constantCoeff L = 0)
    (hL : PowerSeries.subst L (PowerSeries.exp R) =
      permExcedanceCycleEGF
        (fun n σ => ∀ i : Fin n, (Finset.univ.filter (σ.SameCycle i)).card ∈ ℛ) x 1) :
    (PowerSeries.derivative (R := R))^[s]
        (permExcedanceCycleEGF
          (fun n σ => (FirstPointsInDistinctCycles s n σ ∧ ∀ i : Fin n, (i : ℕ) < s →
            (Finset.univ.filter (σ.SameCycle i)).card = r i) ∧
            ∀ i : Fin n, (∀ j : Fin n, (j : ℕ) < s → ¬ σ.SameCycle i j) →
              (Finset.univ.filter (σ.SameCycle i)).card ∈ ℛ) x q) =
      PowerSeries.C (q ^ s * x ^ s) *
        (∏ i ∈ Finset.range s,
          PowerSeries.C ((((r i - 1).factorial : ℚ)⁻¹) •
            ∑ σ : Equiv.Perm (Fin (r i - 1)), x ^ excedanceCount (r i - 1) σ) *
            PowerSeries.X ^ (r i - 1)) *
        PowerSeries.subst (PowerSeries.C q * L) (PowerSeries.exp R)

/-- Corollary 67: for a finite set `ℛ = {r_1 < ⋯ < r_ℓ}` of lengths `r_i ≥ 2`, the
`q`-analogue over permutations with no cycle of length in `ℛ` is
`A^{r_1^⋆⋯r_ℓ^⋆}(q,x,u) = A(q,x,u) exp(-q x ∑_{r ∈ ℛ} A_{r-1}(x) u^r/r!)`.

Source: Imboa-Navalona Manjaka Rakotoson and Fanja Rakotondrajao, *Associated
Stirling Eulerian Numbers and Their q-Analogues*, Journal of Integer Sequences 28
(2025), Article 25.5.7, Corollary 67 (`jis-2025-25.5.7-cor-67`). -/
public theorem_wanted cycleLengthsNotInEGF_q_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (x q : R) (ℛ : Finset ℕ) (hℛ : ∀ r ∈ ℛ, 2 ≤ r) :
    permExcedanceCycleEGF
        (fun n σ => ∀ i : Fin n, (Finset.univ.filter (σ.SameCycle i)).card ∉ ℛ) x q =
      permExcedanceCycleEGF (fun _ _ => True) x q *
        PowerSeries.subst
          (-(PowerSeries.C q * ∑ r ∈ ℛ,
            PowerSeries.C (((r.factorial : ℚ)⁻¹) •
              (x * ∑ σ : Equiv.Perm (Fin (r - 1)), x ^ excedanceCount (r - 1) σ)) *
              PowerSeries.X ^ r))
          (PowerSeries.exp R)

end

end MetaMathlibExt
