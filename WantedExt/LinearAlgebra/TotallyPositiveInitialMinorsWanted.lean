/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.LinearAlgebra.Matrix.PositiveMinors
public import MathlibExt.NumberTheory.LucasSequence

/-!
# Totally positive matrices and initial minors

Statement-only targets from Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui,
*Total Positivity of Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal
of Integer Sequences 29 (2026), Article 26.2.5: the Gasca–Peña criterion it quotes, and its
results on Toeplitz matrices of generalized hyper-Fibonacci numbers.

A real `n × n` matrix is totally positive (`Matrix.HasPositiveMinors`) when every minor (rows
`r 0 < ⋯ < r (k-1)`, columns `c 0 < ⋯ < c (k-1)`) is positive. An initial minor uses
consecutive rows and consecutive columns, at least one of the two blocks starting at the first
index.

`W_{p,n}` is `generalizedPFibonacci p a b n` and `W_{p,n}^{(r)}` is
`generalizedHyperFibonacci p a b r n`; the hyper `p`-Fibonacci and hyper `p`-Lucas numbers are
the cases `(a, b) = (0, 1)` and `(2, p)` (bridges to `lucasU` and `lucasV`). The `m × m` Toeplitz
matrix `T_{m,n}^{(r)}` has entry `W_{p,n+i-j}^{(r)}` in row `i`, column `j` (`0 ≤ i, j < m`); all
statements about it are for large `n`, where every index is nonnegative, so natural subtraction
is harmless. `TP_k` (every minor of order at most `k` positive) is written out with the same
strictly increasing row and column maps as `Matrix.HasPositiveMinors`. The paper's standing
hypotheses are `p ≥ 1`, `a ≥ 0`, `b > 0`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Gasca–Peña criterion: a real square matrix is totally positive if and only if all its
initial minors are positive; an initial minor has rows `i₀, …, i₀ + k - 1` and columns
`j₀, …, j₀ + k - 1` with `i₀ = 0` or `j₀ = 0`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of Toeplitz
Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer Sequences 29 (2026),
Article 26.2.5, Theorem 3, quoting Gasca and Peña (`jis-2026-26.2.5-thm-3`). -/
public theorem_wanted hasPositiveMinors_iff_initial_minors_pos {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.HasPositiveMinors A ↔
      ∀ (k i₀ j₀ : ℕ) (hi : i₀ + k ≤ n) (hj : j₀ + k ≤ n), (i₀ = 0 ∨ j₀ = 0) →
        0 < (A.submatrix (fun r : Fin k => (⟨i₀ + r, by omega⟩ : Fin n))
          (fun c : Fin k => (⟨j₀ + c, by omega⟩ : Fin n))).det

/-- The generalized Fibonacci sequence `W_{p,n}`: `W_{p,0} = a`, `W_{p,1} = b`,
`W_{p,n} = p W_{p,n-1} + W_{p,n-2}` for `n ≥ 2`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, recurrence (1). -/
public def generalizedPFibonacci (p a b : ℤ) : ℕ → ℤ
  | 0 => a
  | 1 => b
  | n + 2 => p * generalizedPFibonacci p a b (n + 1) + generalizedPFibonacci p a b n

/-- The `p`-Fibonacci numbers (`(a, b) = (0, 1)`) are the Lucas sequence `U(p, -1)`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, remark after recurrence (1) (`p`-Fibonacci
numbers `F_{p,n}`). -/
public theorem generalizedPFibonacci_zero_one (p : ℤ) (n : ℕ) :
    generalizedPFibonacci p 0 1 n = lucasU ⟨p, -1, by decide⟩ n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    simp only [generalizedPFibonacci, lucasU, ih1, ih2]
    ring

/-- The `p`-Lucas numbers (`(a, b) = (2, p)`) are the companion Lucas sequence `V(p, -1)`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, remark after recurrence (1) (`p`-Lucas numbers
`L_{p,n}`). -/
public theorem generalizedPFibonacci_two_p (p : ℤ) (n : ℕ) :
    generalizedPFibonacci p 2 p n = lucasV ⟨p, -1, by decide⟩ n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    simp only [generalizedPFibonacci, lucasV, ih1, ih2]
    ring

/-- The generalized hyper-Fibonacci numbers `W_{p,n}^{(r)}`: `W_{p,n}^{(0)} = W_{p,n}` and
`W_{p,n}^{(r)} = ∑_{k=0}^{n} p^{n-k} W_{p,k}^{(r-1)}` for `r ≥ 1`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, definition (2). -/
public def generalizedHyperFibonacci (p a b : ℤ) : ℕ → ℕ → ℤ
  | 0 => generalizedPFibonacci p a b
  | r + 1 => fun n =>
      ∑ k ∈ Finset.range (n + 1), p ^ (n - k) * generalizedHyperFibonacci p a b r k

/-- Initial values `W_{p,0}^{(r)} = a` and `W_{p,1}^{(r)} = par + b`, as listed in the
definition.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Section 1, definition (2) (initial values). -/
public theorem generalizedHyperFibonacci_zero_one (p a b : ℤ) (r : ℕ) :
    generalizedHyperFibonacci p a b r 0 = a ∧
      generalizedHyperFibonacci p a b r 1 = p * a * r + b := by
  induction r with
  | zero => exact ⟨rfl, by simp [generalizedHyperFibonacci, generalizedPFibonacci]⟩
  | succ r ih =>
    refine ⟨?_, ?_⟩
    · simp [generalizedHyperFibonacci, ih.1]
    · simp only [generalizedHyperFibonacci, Finset.sum_range_succ, Finset.sum_range_zero,
        ih.1, ih.2]
      push_cast
      ring

/-- For `r ≥ 1` and `n ≥ 1`, `W_{p,n}^{(r)} = p W_{p,n-1}^{(r)} + W_{p,n}^{(r-1)}`, stated for
all integers `p`, `a`, `b`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Lemma 5, identity (3), quoting Ait-Amrane et al.
(`jis-2026-26.2.5-lem-5`). -/
public theorem_wanted generalizedHyperFibonacci_succ_succ (p a b : ℤ) (r n : ℕ) :
    generalizedHyperFibonacci p a b (r + 1) (n + 1) =
      p * generalizedHyperFibonacci p a b (r + 1) n + generalizedHyperFibonacci p a b r (n + 1)

/-- For `r ≥ 1` and `n ≥ r`, `W_{p,n-r}^{(r)} = W_{p,n+r} - S_r` with
`S_r = p^n ∑_{k=0}^{r-1} C(n-k-1, r-k-1) W_{p,2k+1} / p^{r-1}`; stated over `ℚ` for all
integers `a`, `b` and all `p ≠ 0`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Lemma 5, identity (4), quoting Ait-Amrane et al.
(`jis-2026-26.2.5-lem-5`). -/
public theorem_wanted generalizedHyperFibonacci_sub_eq_sub (p a b : ℤ) (hp : p ≠ 0) (r n : ℕ)
    (hr : 1 ≤ r) (hrn : r ≤ n) :
    (generalizedHyperFibonacci p a b r (n - r) : ℚ) =
      generalizedPFibonacci p a b (n + r) -
        (p : ℚ) ^ n * (∑ k ∈ Finset.range r,
          ((n - k - 1).choose (r - k - 1) : ℚ) * generalizedPFibonacci p a b (2 * k + 1)) /
          (p : ℚ) ^ (r - 1)

/-- For `r, n ≥ 0`, the Hankel matrix `H_{r,n} = (W_{p,n+i+j}^{(r)})_{0 ≤ i, j ≤ r+1}` of order
`r + 2` has `det H_{r,n} = (-1)^{n+1+⌊(r+3)/2⌋} p^{nr+r²} b^r Δ` with `Δ = a² + pab - b²`;
stated for all integers `p`, `a`, `b`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Proposition 7, quoting Ait-Amrane et al.
(`jis-2026-26.2.5-prop-7`). -/
public theorem_wanted generalizedHyperFibonacci_hankel_det (p a b : ℤ) (r n : ℕ) :
    (Matrix.of fun i j : Fin (r + 2) =>
        generalizedHyperFibonacci p a b r (n + i + j)).det =
      (-1) ^ (n + 1 + (r + 3) / 2) * p ^ (n * r + r ^ 2) * b ^ r * (a ^ 2 + p * a * b - b ^ 2)

/-- For `m ≥ 1`, `det T_{m,n}^{(m-1)} > 0` for all sufficiently large `n`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Theorem 8 (`jis-2026-26.2.5-thm-8`). -/
public theorem_wanted generalizedHyperFibonacci_toeplitz_det_eventually_pos (p a b : ℤ)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (m : ℕ) (hm : 1 ≤ m) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < (Matrix.of fun i j : Fin m =>
      generalizedHyperFibonacci p a b (m - 1) (n + i - j)).det

/-- For `r ≥ 1` and `1 ≤ m ≤ r + 1`, `det T_{m,n}^{(r)} > 0` for all sufficiently large `n`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 9 (`jis-2026-26.2.5-cor-9`). -/
public theorem_wanted generalizedHyperFibonacci_toeplitz_det_eventually_pos_of_le (p a b : ℤ)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hmr : m ≤ r + 1) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < (Matrix.of fun i j : Fin m =>
      generalizedHyperFibonacci p a b r (n + i - j)).det

/-- For `r ≥ 1`, `(W_{p,n}^{(r)})_n` is eventually log-concave: for all large `n` the terms
are positive and `W_{p,n}^{(r)} W_{p,n+2}^{(r)} ≤ (W_{p,n+1}^{(r)})²`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 10 (`jis-2026-26.2.5-cor-10`). -/
public theorem_wanted generalizedHyperFibonacci_eventually_logConcave (p a b : ℤ)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r : ℕ) (hr : 1 ≤ r) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < generalizedHyperFibonacci p a b r n ∧
      generalizedHyperFibonacci p a b r n * generalizedHyperFibonacci p a b r (n + 2) ≤
        generalizedHyperFibonacci p a b r (n + 1) ^ 2

/-- For `r ≥ 1` and `p ≥ 1`, the hyper `p`-Fibonacci numbers `F_{p,n}^{(r)}` (`(a, b) = (0, 1)`)
and the hyper `p`-Lucas numbers `L_{p,n}^{(r)}` (`(a, b) = (2, p)`) are eventually log-concave
(eventually positive, with `x_n x_{n+2} ≤ x_{n+1}²`).

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 11 (`jis-2026-26.2.5-cor-11`). -/
public theorem_wanted hyperPFibonacci_hyperPLucas_eventually_logConcave (p : ℤ) (hp : 1 ≤ p)
    (r : ℕ) (hr : 1 ≤ r) :
    (∃ N : ℕ, ∀ n ≥ N, 0 < generalizedHyperFibonacci p 0 1 r n ∧
      generalizedHyperFibonacci p 0 1 r n * generalizedHyperFibonacci p 0 1 r (n + 2) ≤
        generalizedHyperFibonacci p 0 1 r (n + 1) ^ 2) ∧
    (∃ N : ℕ, ∀ n ≥ N, 0 < generalizedHyperFibonacci p 2 p r n ∧
      generalizedHyperFibonacci p 2 p r n * generalizedHyperFibonacci p 2 p r (n + 2) ≤
        generalizedHyperFibonacci p 2 p r (n + 1) ^ 2)

/-- For `r ≥ 1` and `Δ = a² + pab - b²`: if `Δ > 0`, the Toeplitz matrix `T_{r+2,2n}^{(r)}` is
totally positive for all large `n`; if `Δ < 0`, so is `T_{r+2,2n+1}^{(r)}`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Theorem 12 (`jis-2026-26.2.5-thm-12`). -/
public theorem_wanted generalizedHyperFibonacci_toeplitz_hasPositiveMinors (p a b : ℤ)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r : ℕ) (hr : 1 ≤ r) :
    (0 < a ^ 2 + p * a * b - b ^ 2 → ∃ N : ℕ, ∀ n ≥ N,
      Matrix.HasPositiveMinors (Matrix.of fun i j : Fin (r + 2) =>
        (generalizedHyperFibonacci p a b r (2 * n + i - j) : ℝ))) ∧
    (a ^ 2 + p * a * b - b ^ 2 < 0 → ∃ N : ℕ, ∀ n ≥ N,
      Matrix.HasPositiveMinors (Matrix.of fun i j : Fin (r + 2) =>
        (generalizedHyperFibonacci p a b r (2 * n + 1 + i - j) : ℝ)))

/-- For `r ≥ 1`, `T_{r+2,n}^{(r)}` is `TP_{r+1}` (every minor of order at most `r + 1`
positive) for all large `n`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 13 (`jis-2026-26.2.5-cor-13`). -/
public theorem_wanted generalizedHyperFibonacci_toeplitz_positiveMinors_le (p a b : ℤ)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r : ℕ) (hr : 1 ≤ r) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ r + 1, ∀ (rows cols : Fin k → Fin (r + 2)),
      StrictMono rows → StrictMono cols →
        0 < ((Matrix.of fun i j : Fin (r + 2) =>
          (generalizedHyperFibonacci p a b r (n + i - j) : ℝ)).submatrix rows cols).det

/-- For `r ≥ 1` and `p ≥ 1`, with the hyper `p`-Fibonacci numbers `F_{p,n}^{(r)}`
(`(a, b) = (0, 1)`): the Toeplitz matrix `(F_{p,2n+1+i-j}^{(r)})` of order `r + 2` is totally
positive for all large `n`, and `(F_{p,n+i-j}^{(r)})` is `TP_{r+1}` for all large `n`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 14 (`jis-2026-26.2.5-cor-14`). -/
public theorem_wanted hyperPFibonacci_toeplitz_hasPositiveMinors (p : ℤ) (hp : 1 ≤ p) (r : ℕ)
    (hr : 1 ≤ r) :
    (∃ N : ℕ, ∀ n ≥ N, Matrix.HasPositiveMinors (Matrix.of fun i j : Fin (r + 2) =>
      (generalizedHyperFibonacci p 0 1 r (2 * n + 1 + i - j) : ℝ))) ∧
    (∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ r + 1, ∀ (rows cols : Fin k → Fin (r + 2)),
      StrictMono rows → StrictMono cols →
        0 < ((Matrix.of fun i j : Fin (r + 2) =>
          (generalizedHyperFibonacci p 0 1 r (n + i - j) : ℝ)).submatrix rows cols).det)

/-- For `r ≥ 1` and `p ≥ 1`, with the hyper `p`-Lucas numbers `L_{p,n}^{(r)}`
(`(a, b) = (2, p)`): the Toeplitz matrix `(L_{p,2n+i-j}^{(r)})` of order `r + 2` is totally
positive for all large `n`, and `(L_{p,n+i-j}^{(r)})` is `TP_{r+1}` for all large `n`.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 15 (`jis-2026-26.2.5-cor-15`). -/
public theorem_wanted hyperPLucas_toeplitz_hasPositiveMinors (p : ℤ) (hp : 1 ≤ p) (r : ℕ)
    (hr : 1 ≤ r) :
    (∃ N : ℕ, ∀ n ≥ N, Matrix.HasPositiveMinors (Matrix.of fun i j : Fin (r + 2) =>
      (generalizedHyperFibonacci p 2 p r (2 * n + i - j) : ℝ))) ∧
    (∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ r + 1, ∀ (rows cols : Fin k → Fin (r + 2)),
      StrictMono rows → StrictMono cols →
        0 < ((Matrix.of fun i j : Fin (r + 2) =>
          (generalizedHyperFibonacci p 2 p r (n + i - j) : ℝ)).submatrix rows cols).det)

end

end MetaMathlibExt
