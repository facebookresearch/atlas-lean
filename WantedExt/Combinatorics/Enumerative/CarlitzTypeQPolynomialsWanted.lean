/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli

namespace MetaMathlibExt

open Filter Finset Topology

@[expose] public section

/-- The `q`-analogue `[x] = (q^x - 1)/(q - 1)` of a real number `x` (real power `q^x`).

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 1. -/
public noncomputable def qBracket (q x : ℝ) : ℝ :=
  (q ^ x - 1) / (q - 1)

/-- `(T_n(x))_n` is a Carlitz-type `q`-polynomial sequence with associated real sequence `(a_k)`:
`T_n(x) = (q - 1)^{-n} ∑_{k=0}^{n} (-1)^{n-k} C(n,k) a_k q^{kx}` for all `n` and real `x`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Definition in
Section 2.1. -/
public def IsCarlitzTypeWith (q : ℝ) (T : ℕ → ℝ → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ n x, T n x = ((q - 1) ^ n)⁻¹ *
    ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * a k * q ^ ((k : ℝ) * x)

/-- Carlitz's `q`-polynomials `η_n(x)`: the Carlitz-type sequence with associated sequence
`k/[k]`, taken to be `1` at `k = 0`; `η_n = η_n(0)`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1
(examples after Theorem 2.1); after L. Carlitz (1948). -/
public noncomputable def carlitzEtaPoly (q : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((q - 1) ^ n)⁻¹ * ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) *
    (if k = 0 then 1 else (k : ℝ) / qBracket q k) * q ^ ((k : ℝ) * x)

/-- Carlitz's `q`-Bernoulli polynomials `β_n(x)`: the Carlitz-type sequence with associated
sequence `(k + 1)/[k + 1]`; `β_n = β_n(0)`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1
(examples after Theorem 2.1); after L. Carlitz (1948). -/
public noncomputable def carlitzBetaPoly (q : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((q - 1) ^ n)⁻¹ * ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) *
    (((k : ℝ) + 1) / qBracket q ((k : ℝ) + 1)) * q ^ ((k : ℝ) * x)

/-- `[0] = 0`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 1. -/
public theorem qBracket_zero (q : ℝ) : qBracket q 0 = 0 := by
  simp [qBracket]

/-- `[1] = 1` for `q ≠ 1`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 1. -/
public theorem qBracket_one {q : ℝ} (hq : q ≠ 1) : qBracket q 1 = 1 := by
  rw [qBracket, Real.rpow_one, div_self (sub_ne_zero.mpr hq)]

/-- A Carlitz-type sequence starts with the constant `T_0(x) = a_0`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Definition in
Section 2.1. -/
public theorem IsCarlitzTypeWith.apply_zero {q : ℝ} {T : ℕ → ℝ → ℝ} {a : ℕ → ℝ}
    (h : IsCarlitzTypeWith q T a) (x : ℝ) : T 0 x = a 0 := by
  simp [h 0 x]

/-- `η_0(x) = 1`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1. -/
public theorem carlitzEtaPoly_zero (q x : ℝ) : carlitzEtaPoly q 0 x = 1 := by
  simp [carlitzEtaPoly]

/-- `η_1 = η_1(0) = 0` for `q ≠ 1` (Carlitz's initial value).

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Sections 1
and 2.1. -/
public theorem carlitzEtaPoly_one_zero {q : ℝ} (hq : q ≠ 1) : carlitzEtaPoly q 1 0 = 0 := by
  simp [carlitzEtaPoly, Finset.sum_range_succ, qBracket_one hq]

/-- `β_0(x) = 1` for `q ≠ 1`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.1. -/
public theorem carlitzBetaPoly_zero {q : ℝ} (hq : q ≠ 1) (x : ℝ) : carlitzBetaPoly q 0 x = 1 := by
  simp [carlitzBetaPoly, qBracket_one hq]

/-- Characterization of Carlitz-type sequences (a `q`-analogue of Appell sequences): a sequence of
functions `T_n` is Carlitz-type iff `T_n(x) = ∑_{k=0}^{n} C(n,k) t_k q^{kx} [x]^{n-k}` for all
`n`, where `t_k = T_k(0)`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.1
(`integers-2026-A85-thm-2-1`). -/
public theorem_wanted isCarlitzType_iff_sum_choose (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (T : ℕ → ℝ → ℝ) :
    (∃ a, IsCarlitzTypeWith q T a) ↔
      ∀ n x, T n x = ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * T k 0 * q ^ ((k : ℝ) * x) * qBracket q x ^ (n - k)

/-- Binomial inversion: `u_n = ∑ C(n,k) v_k` for all `n` iff `v_n = ∑ (-1)^{n-k} C(n,k) u_k` for
all `n`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Lemma 2.2
(`integers-2026-A85-lem-2-2`). -/
public theorem_wanted binomial_inversion_iff (u v : ℕ → ℝ) :
    (∀ n, u n = ∑ k ∈ range (n + 1), (n.choose k : ℝ) * v k) ↔
      ∀ n, v n = ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) * u k

/-- `q`-power sums: for `r ≥ 1`, `∑_{k<N} q^{rk} [k]^n = q^{rN} S_n(N) - S_n(0)`, where `S` is the
Carlitz-type sequence with associated sequence `1/((q - 1)[k + r])`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.3
(`integers-2026-A85-thm-2-3`). -/
public theorem_wanted sum_qpow_mul_qBracket_pow (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r n N : ℕ) (hr : 0 < r) (S : ℕ → ℝ → ℝ)
    (hS : IsCarlitzTypeWith q S fun k => 1 / ((q - 1) * qBracket q ((k + r : ℕ) : ℝ))) :
    ∑ k ∈ range N, q ^ (r * k) * qBracket q k ^ n = q ^ (r * N) * S n N - S n 0

/-- Generalized `q`-power sums: for `1 ≤ r`, `d ≤ r` and `n ≥ d`,
`∑_{k<N} q^{rk} [k]^{n-d} = (q^{(r-d)N} T_n(N) - T_n(0)) / (n)_d`, where `T` is the Carlitz-type
sequence with associated sequence `(q - 1)^{d-1} (k)_d / [k + r - d]` (`(k)_d` falling factorial;
the terms `k < d` vanish).

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.4
(`integers-2026-A85-thm-2-4`). -/
public theorem_wanted sum_qpow_mul_qBracket_pow_sub (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r d n N : ℕ) (hr : 0 < r) (hdr : d ≤ r) (hdn : d ≤ n) (T : ℕ → ℝ → ℝ)
    (hT : IsCarlitzTypeWith q T fun k =>
      (q - 1) ^ ((d : ℤ) - 1) * (k.descFactorial d : ℝ) / qBracket q ((k + r - d : ℕ) : ℝ)) :
    ∑ k ∈ range N, q ^ (r * k) * qBracket q k ^ (n - d) =
      (q ^ ((r - d) * N) * T n N - T n 0) / (n.descFactorial d : ℝ)

/-- Symbolic recurrence: if `[k + r] a_k = P(k)` for a real polynomial `P` and `T` is Carlitz-type
with associated sequence `a`, then `t_n = T_n(0)` satisfies `q^r (q t + 1)^n = t^n`, i.e.
`q^r ∑_j C(n,j) q^j t_j = t_n`, for every `n > deg P`. The hypothesis `[k + r] a_k = P(k)` encodes
`a_k = P(k)/[k + r]`; for `r = 0` it forces `P(0) = 0` and leaves `a_0` free.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.5
(`integers-2026-A85-thm-2-5`). -/
public theorem_wanted carlitzType_symbolic_recurrence (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r : ℕ) (P : Polynomial ℝ) (a : ℕ → ℝ)
    (ha : ∀ k : ℕ, qBracket q ((k + r : ℕ) : ℝ) * a k = P.eval (k : ℝ))
    (T : ℕ → ℝ → ℝ) (hT : IsCarlitzTypeWith q T a) (n : ℕ) (hn : P.natDegree < n) :
    q ^ r * ∑ j ∈ range (n + 1), (n.choose j : ℝ) * q ^ j * T j 0 = T n 0

/-- Closure properties of Carlitz-type sequences with associated sequence `a`:
(i) `q^x n T_{n-1}(x)` has associated sequence `(q - 1) k a_{k-1}`;
(ii) if `a_0 = 0`, `q^{-x} T_{n+1}(x)/(n + 1)` has associated sequence `a_{k+1}/((q - 1)(k + 1))`;
(iii) `q^{-x}(T_n(x) + (q - 1) T_{n+1}(x))` has associated sequence `a_{k+1}`;
(iv) `n (T_{n-1}(x) + (q - 1) T_n(x))` has associated sequence `(q - 1) k a_k`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.6
(`integers-2026-A85-prop-2-6`). -/
public theorem_wanted isCarlitzTypeWith_closure (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (T : ℕ → ℝ → ℝ) (a : ℕ → ℝ) (hT : IsCarlitzTypeWith q T a) :
    IsCarlitzTypeWith q (fun n x => q ^ x * n * T (n - 1) x)
        (fun k => (q - 1) * k * a (k - 1)) ∧
      (a 0 = 0 → IsCarlitzTypeWith q (fun n x => q ^ (-x) * T (n + 1) x / (n + 1))
        (fun k => a (k + 1) / ((q - 1) * (k + 1)))) ∧
      IsCarlitzTypeWith q (fun n x => q ^ (-x) * (T n x + (q - 1) * T (n + 1) x))
        (fun k => a (k + 1)) ∧
      IsCarlitzTypeWith q (fun n x => n * (T (n - 1) x + (q - 1) * T n x))
        (fun k => (q - 1) * k * a k)

/-- `∑_{k<N} q^k [k]^{n-1} = (η_n(N) - η_n)/n` for `n ≥ 1`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.7
(`integers-2026-A85-cor-2-7`). -/
public theorem_wanted sum_qpow_mul_qBracket_pow_eq_carlitzEta (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) (n N : ℕ) (hn : 0 < n) :
    ∑ k ∈ range N, q ^ k * qBracket q k ^ (n - 1) =
      (carlitzEtaPoly q n N - carlitzEtaPoly q n 0) / n

/-- `n ∑_{k<N} q^{2k} [k]^{n-1} + (q - 1) ∑_{k<N} q^k [k]^n = q^N β_n(N) - β_n`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.8
(`integers-2026-A85-cor-2-8`). -/
public theorem_wanted sum_qpow_mul_qBracket_pow_eq_carlitzBeta (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) (n N : ℕ) :
    n * ∑ k ∈ range N, q ^ (2 * k) * qBracket q k ^ (n - 1) +
        (q - 1) * ∑ k ∈ range N, q ^ k * qBracket q k ^ n =
      q ^ N * carlitzBetaPoly q n N - carlitzBetaPoly q n 0

/-- The extended Carlitz `q`-Bernoulli polynomials `β_n^{(r)}(x)`: `β_n^{(0)}(x) = η_n(x)` and
`β_n^{(r+1)}(x) = q^{-x} (β_n^{(r)}(x) + (q - 1) β_{n+1}^{(r)}(x))`; the numbers are
`β_n^{(r)} = β_n^{(r)}(0)`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.2
(definition of the extended family). -/
public noncomputable def extendedCarlitzBetaPoly (q : ℝ) : ℕ → ℕ → ℝ → ℝ
  | 0, n, x => carlitzEtaPoly q n x
  | r + 1, n, x => q ^ (-x) *
      (extendedCarlitzBetaPoly q r n x + (q - 1) * extendedCarlitzBetaPoly q r (n + 1) x)

/-- `β_n^{(0)}(x) = η_n(x)`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.2. -/
public theorem extendedCarlitzBetaPoly_zero (q : ℝ) (n : ℕ) (x : ℝ) :
    extendedCarlitzBetaPoly q 0 n x = carlitzEtaPoly q n x := by
  simp [extendedCarlitzBetaPoly]

/-- The recurrence `β_n^{(r+1)}(x) = q^{-x} (β_n^{(r)}(x) + (q - 1) β_{n+1}^{(r)}(x))`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Section 2.2. -/
public theorem extendedCarlitzBetaPoly_succ (q : ℝ) (r n : ℕ) (x : ℝ) :
    extendedCarlitzBetaPoly q (r + 1) n x = q ^ (-x) *
      (extendedCarlitzBetaPoly q r n x + (q - 1) * extendedCarlitzBetaPoly q r (n + 1) x) := by
  simp [extendedCarlitzBetaPoly]

/-- Closed forms of the extended Carlitz `q`-Bernoulli polynomials: `β_n^{(r)}(x)` is Carlitz-type
with associated sequence `(k + r)/[k + r]` (`1` when `k + r = 0`), it satisfies
`β_n^{(r)}(x) = ∑ C(n,k) β_k^{(r)} q^{kx} [x]^{n-k}`, and `q^r (q β^{(r)} + 1)^n = (β^{(r)})^n` for
`n ≥ 2`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.9
(`integers-2026-A85-prop-2-9`). -/
public theorem_wanted extendedCarlitzBetaPoly_closed_forms (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r : ℕ) :
    (∀ n x, extendedCarlitzBetaPoly q r n x = ((q - 1) ^ n)⁻¹ *
        ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (n - k) * (n.choose k : ℝ) *
          (if k + r = 0 then 1 else ((k + r : ℕ) : ℝ) / qBracket q ((k + r : ℕ) : ℝ)) *
            q ^ ((k : ℝ) * x)) ∧
      (∀ n x, extendedCarlitzBetaPoly q r n x = ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) * extendedCarlitzBetaPoly q r k 0 * q ^ ((k : ℝ) * x) *
          qBracket q x ^ (n - k)) ∧
      ∀ n, 2 ≤ n → q ^ r * ∑ j ∈ range (n + 1),
        (n.choose j : ℝ) * q ^ j * extendedCarlitzBetaPoly q r j 0 =
          extendedCarlitzBetaPoly q r n 0

/-- `n ∑_{k<N} q^{(r+1)k} [k]^{n-1} + (q - 1) r ∑_{k<N} q^{rk} [k]^n = q^{rN} β_n^{(r)}(N) -
β_n^{(r)}`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.10
(`integers-2026-A85-thm-2-10`). -/
public theorem_wanted sum_qpow_mul_qBracket_pow_eq_extendedCarlitzBeta (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) (r n N : ℕ) :
    n * ∑ k ∈ range N, q ^ ((r + 1) * k) * qBracket q k ^ (n - 1) +
        (q - 1) * r * ∑ k ∈ range N, q ^ (r * k) * qBracket q k ^ n =
      q ^ (r * N) * extendedCarlitzBetaPoly q r n N - extendedCarlitzBetaPoly q r n 0

/-- Series for `β_n^{(r)}` when `0 < q < 1`: `β_n^{(0)} = -n ∑ q^k [k]^{n-1} + (1 - q)^{-n}` and,
for `r ≥ 1`, `β_n^{(r)} = -n ∑ q^{(r+1)k} [k]^{n-1} + r (1 - q) ∑ q^{rk} [k]^n` (`n ≥ 1`).

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.11
(`integers-2026-A85-thm-2-11`). -/
public theorem_wanted extendedCarlitzBeta_eq_tsum (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (r n : ℕ) (hn : 0 < n) :
    extendedCarlitzBetaPoly q r n 0 =
      if r = 0 then -n * ∑' k : ℕ, q ^ k * qBracket q k ^ (n - 1) + ((1 - q) ^ n)⁻¹
      else -n * ∑' k : ℕ, q ^ ((r + 1) * k) * qBracket q k ^ (n - 1) +
        r * (1 - q) * ∑' k : ℕ, q ^ (r * k) * qBracket q k ^ n

/-- For `r, n ≥ 1`, `B_n = lim_{q → 1⁻} ∑_{k ≥ 0} (r q^{rk} - (n + r) q^{(r+1)k}) [k]^{n-1}`, with
Mathlib's `bernoulli` (`B_1 = -1/2`).

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.12
(`integers-2026-A85-cor-2-12`). -/
public theorem_wanted tendsto_tsum_qBracket_bernoulli (r n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    Tendsto (fun q : ℝ => ∑' k : ℕ,
        ((r : ℝ) * q ^ (r * k) - ((n : ℝ) + r) * q ^ ((r + 1) * k)) * qBracket q k ^ (n - 1))
      (𝓝[<] 1) (𝓝 (bernoulli n : ℝ))

/-- `∑_{i<N} q^{ir} [i]_k = (∑_{ℓ<r} q^{(r-ℓ-1)N + (ℓ+1)k} [r-1]_ℓ / [k+r]_{ℓ+1}) [N]_{k+1}` for
`r ≥ 1`, where `[x]_m = [x][x-1]⋯[x-m+1]`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.14
(`integers-2026-A85-prop-2-14`). -/
public theorem_wanted sum_qpow_mul_qFalling (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1) (r k N : ℕ)
    (hr : 0 < r) :
    ∑ i ∈ range N, q ^ (i * r) * ∏ j ∈ range k, qBracket q ((i : ℝ) - j) =
      (∑ l ∈ range r, q ^ ((r - l - 1) * N + (l + 1) * k) *
          (∏ j ∈ range l, qBracket q ((r : ℝ) - 1 - j)) /
            ∏ j ∈ range (l + 1), qBracket q (((k + r : ℕ) : ℝ) - j)) *
        ∏ j ∈ range (k + 1), qBracket q ((N : ℝ) - j)

/-- First closed form of `g_r(q, k) = lim_{x→0} f_r(q,k,x)/[x]`, where `f_r(q,k,·)` is the
`q`-polynomial (a polynomial `P` in `q^x`) interpolating `q^{k(k-1)/2} ∑_{i<N} q^{ir} [i]_k` at the
positive integers `N`: `g_r(q,k) = (-1)^k [k]! ∑_{i<r} q^{ik} [r-1]_i / [k+r]_{i+1}`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.15
(`integers-2026-A85-cor-2-15`). -/
public theorem_wanted tendsto_qInterpolant_div_qBracket (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r k : ℕ) (hr : 0 < r) (P : Polynomial ℝ)
    (hP : ∀ N : ℕ, 0 < N → P.eval (q ^ N) = q ^ (k * (k - 1) / 2) *
      ∑ i ∈ range N, q ^ (i * r) * ∏ j ∈ range k, qBracket q ((i : ℝ) - j)) :
    Tendsto (fun x : ℝ => P.eval (q ^ x) / qBracket q x) (𝓝[≠] 0)
      (𝓝 ((-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) *
        ∑ i ∈ range r, q ^ (i * k) * (∏ j ∈ range i, qBracket q ((r : ℝ) - 1 - j)) /
          ∏ j ∈ range (i + 1), qBracket q (((k + r : ℕ) : ℝ) - j)))

/-- Partial fractions: for real `x ∉ {0, …, k}`,
`q^{kx}/[x]_{k+1} = (1/[k]!) ∑_{i=0}^{k} (-1)^{k-i} [k choose i]_q q^{(k²+k)/2 + (i²-i)/2} /
[x - i]`
(`[k choose i]_q = [k]!/([i]! [k-i]!)`).

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.16
(`integers-2026-A85-prop-2-16`). -/
public theorem_wanted qpow_div_qFalling_partial_fractions (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (k : ℕ) (x : ℝ) (hx : ∀ i : ℕ, i ≤ k → x ≠ i) :
    q ^ ((k : ℝ) * x) / ∏ j ∈ range (k + 1), qBracket q (x - j) =
      (∏ j ∈ range k, qBracket q ((j : ℝ) + 1))⁻¹ * ∑ i ∈ range (k + 1),
        (-1 : ℝ) ^ (k - i) *
          ((∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) /
            ((∏ j ∈ range i, qBracket q ((j : ℝ) + 1)) *
              ∏ j ∈ range (k - i), qBracket q ((j : ℝ) + 1))) *
          q ^ ((k ^ 2 + k) / 2 + (i ^ 2 - i) / 2) / qBracket q (x - i)

/-- Second closed form of `g_r(q, k)` (same interpolation setting as Corollary 2.15):
`g_r(q,k) = (-1)^k [k]! [r-1]! q^{1-r} ∑_{i<r} (q-1)^i q^{i(i+1)/2 - i(r-1)} / ([r-1-i]! [k+i+1])`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.17
(`integers-2026-A85-prop-2-17`). -/
public theorem_wanted tendsto_qInterpolant_div_qBracket' (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r k : ℕ) (hr : 0 < r) (P : Polynomial ℝ)
    (hP : ∀ N : ℕ, 0 < N → P.eval (q ^ N) = q ^ (k * (k - 1) / 2) *
      ∑ i ∈ range N, q ^ (i * r) * ∏ j ∈ range k, qBracket q ((i : ℝ) - j)) :
    Tendsto (fun x : ℝ => P.eval (q ^ x) / qBracket q x) (𝓝[≠] 0)
      (𝓝 ((-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) *
        (∏ j ∈ range (r - 1), qBracket q ((j : ℝ) + 1)) * q ^ (1 - (r : ℝ)) *
        ∑ i ∈ range r, (q - 1) ^ i *
          q ^ (((i * (i + 1) / 2 : ℕ) : ℝ) - ((i * (r - 1) : ℕ) : ℝ)) /
            ((∏ j ∈ range (r - 1 - i), qBracket q ((j : ℝ) + 1)) *
              qBracket q ((k + i + 1 : ℕ) : ℝ))))


/-- Expansion of `β_n^{(r)}` in Carlitz's `q`-Stirling numbers of the second kind: for `r ≥ 1`,
`β_n^{(r)} = ∑_{k=0}^{n} φ_r(q,k) S_q(n,k)` with
`φ_r(q,k) = (-1)^k [k]! ∑_{i<r} q^{ik} [r-1]_i / [k+r]_{i+1}`, and `φ_r(q,k)` also equals
`(-1)^k [k]! [r-1]! q^{1-r} ∑_{i<r} (q-1)^i q^{i(i+1)/2 - i(r-1)} / ([r-1-i]! [k+i+1])`.
Carlitz's `S_q(n,k)` enter through their defining identity
`[x]^n = ∑_{k=0}^{n} q^{k(k-1)/2} S_q(n,k) [x]_k` for all real `x` (which determines them).

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Theorem 2.13
(`integers-2026-A85-thm-2-13`). -/
public theorem_wanted extendedCarlitzBeta_eq_sum_qStirling (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1)
    (r n : ℕ) (hr : 0 < r) (S : ℕ → ℕ → ℝ)
    (hS : ∀ (m : ℕ) (x : ℝ), qBracket q x ^ m = ∑ k ∈ range (m + 1),
      q ^ (k * (k - 1) / 2) * S m k * ∏ j ∈ range k, qBracket q (x - j)) :
    extendedCarlitzBetaPoly q r n 0 = ∑ k ∈ range (n + 1),
        (-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) *
          (∑ i ∈ range r, q ^ (i * k) * (∏ j ∈ range i, qBracket q ((r : ℝ) - 1 - j)) /
            ∏ j ∈ range (i + 1), qBracket q (((k + r : ℕ) : ℝ) - j)) * S n k ∧
      ∀ k : ℕ, (-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) *
          (∑ i ∈ range r, q ^ (i * k) * (∏ j ∈ range i, qBracket q ((r : ℝ) - 1 - j)) /
            ∏ j ∈ range (i + 1), qBracket q (((k + r : ℕ) : ℝ) - j)) =
        (-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) *
          (∏ j ∈ range (r - 1), qBracket q ((j : ℝ) + 1)) * q ^ (1 - (r : ℝ)) *
          ∑ i ∈ range r, (q - 1) ^ i *
            q ^ (((i * (i + 1) / 2 : ℕ) : ℝ) - ((i * (r - 1) : ℕ) : ℝ)) /
              ((∏ j ∈ range (r - 1 - i), qBracket q ((j : ℝ) + 1)) *
                qBracket q ((k + i + 1 : ℕ) : ℝ))

/-- `β_n + q β_{n+1} = ∑_{k=0}^{n} (-1)^k [k]!/[k+2] S_q(n,k)` for Carlitz's `q`-Bernoulli numbers
`β_n = β_n(0)`, with Carlitz's `q`-Stirling numbers `S_q(n,k)` given by their defining identity
`[x]^n = ∑_{k=0}^{n} q^{k(k-1)/2} S_q(n,k) [x]_k`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.18
(`integers-2026-A85-cor-2-18`). -/
public theorem_wanted carlitzBeta_add_mul_succ_eq_sum_qStirling (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≠ 1) (n : ℕ) (S : ℕ → ℕ → ℝ)
    (hS : ∀ (m : ℕ) (x : ℝ), qBracket q x ^ m = ∑ k ∈ range (m + 1),
      q ^ (k * (k - 1) / 2) * S m k * ∏ j ∈ range k, qBracket q (x - j)) :
    carlitzBetaPoly q n 0 + q * carlitzBetaPoly q (n + 1) 0 = ∑ k ∈ range (n + 1),
      (-1 : ℝ) ^ k * (∏ j ∈ range k, qBracket q ((j : ℝ) + 1)) / qBracket q ((k : ℝ) + 2) * S n k

/-- `B_n + B_{n+1} = ∑_{k=0}^{n} (-1)^k k!/(k+2) S(n,k)`, with Mathlib's `bernoulli`
(`B_1 = -1/2`, the paper's convention `t/(e^t - 1)`) and `Nat.stirlingSecond`.

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Corollary 2.19
(`integers-2026-A85-cor-2-19`). -/
public theorem_wanted bernoulli_add_bernoulli_succ_eq_sum_stirlingSecond (n : ℕ) :
    bernoulli n + bernoulli (n + 1) = ∑ k ∈ range (n + 1),
      (-1 : ℚ) ^ k * (k.factorial : ℚ) / ((k : ℚ) + 2) * (Nat.stirlingSecond n k : ℚ)

end

end MetaMathlibExt
