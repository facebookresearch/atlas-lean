/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Probability.Distributions.Gamma

namespace MetaMathlibExt

@[expose] public section

open MeasureTheory ProbabilityTheory

/-- Generalized harmonic numbers `H_n^{(s)} = ∑_{k=1}^n 1 / k^s` for real `s`.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Section 1 (definition of
`H_n^{(s)}`). -/
noncomputable def generalizedHarmonic (s : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, ((k : ℝ) ^ s)⁻¹

/-- `H_0^{(s)} = 0`.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Section 1 (definition of
`H_n^{(s)}`). -/
@[simp]
theorem generalizedHarmonic_zero (s : ℝ) : generalizedHarmonic s 0 = 0 := by
  simp [generalizedHarmonic]

/-- Recurrence `H_{n+1}^{(s)} = H_n^{(s)} + 1 / (n+1)^s`.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Section 1 (definition of
`H_n^{(s)}`). -/
theorem generalizedHarmonic_succ (s : ℝ) (n : ℕ) :
    generalizedHarmonic s (n + 1) = generalizedHarmonic s n + (((n + 1 : ℕ) : ℝ) ^ s)⁻¹ := by
  simp [generalizedHarmonic, Finset.sum_Icc_succ_top (Nat.le_add_left 1 n)]

/-- Gamma representation of generalized harmonic numbers: if `X_s ∼ Gamma(s, 1)` with `s > 0`,
then `H_n^{(s)} = ∑_{k=0}^{n-1} E[e^{-k X_s}] = E[(1 - e^{-n X_s}) / (1 - e^{-X_s})]`.

`Gamma(s, 1)` is Mathlib's `gammaMeasure s 1` (shape `s`, rate `1`); expectations are integrals
against it.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Lemma 1, Equation (5)
(`integers-2026-A124-lem-1`). -/
public theorem_wanted generalizedHarmonic_eq_gamma_expectation (s : ℝ) (hs : 0 < s) (n : ℕ) :
    generalizedHarmonic s n =
        ∑ k ∈ Finset.range n, ∫ x, Real.exp (-(k * x)) ∂gammaMeasure s 1 ∧
      generalizedHarmonic s n =
        ∫ x, (1 - Real.exp (-(n * x))) / (1 - Real.exp (-x)) ∂gammaMeasure s 1

/-- Shifted Gamma representation: if `X_s ∼ Gamma(s, 1)` with `s > 0`, then for every real `u`,
`H_n^{(s-u)} = ∑_{k=0}^{n-1} (k+1)^u E[e^{-k X_s}]`. The source assumes `0 < u < s`; the
identity holds for every real `u`.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Lemma 2, Equation (7)
(`integers-2026-A124-lem-2`). -/
public theorem_wanted generalizedHarmonic_sub_eq_gamma_expectation (s : ℝ) (hs : 0 < s) (u : ℝ)
    (n : ℕ) :
    generalizedHarmonic (s - u) n =
      ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) ^ u * ∫ x, Real.exp (-(k * x)) ∂gammaMeasure s 1

/-- Sums of generalized harmonic numbers weighted by binomial coefficients: for every integer
`m ≥ 0` and real `α`,
`∑_{j=1}^{n-1} C(j, m) H_j^{(α)} = C(n, m+1) H_n^{(α)} - (1/(m+1)!) ∑_{r=0}^{m+1}
[m+1, r] (-1)^{m+1-r} H_n^{(α-r)}`, with `[m+1, r]` the unsigned Stirling numbers of the first
kind (`Nat.stirlingFirst`).

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Proposition 1, Equation (3)
(`integers-2026-A124-prop-1`). -/
public theorem_wanted sum_choose_mul_generalizedHarmonic (m n : ℕ) (α : ℝ) :
    ∑ j ∈ Finset.Ico 1 n, (j.choose m : ℝ) * generalizedHarmonic α j =
      (n.choose (m + 1) : ℝ) * generalizedHarmonic α n -
        ((m + 1).factorial : ℝ)⁻¹ * ∑ r ∈ Finset.range (m + 2),
          (Nat.stirlingFirst (m + 1) r : ℝ) * (-1) ^ (m + 1 - r) *
            generalizedHarmonic (α - r) n

/-- Gamma representation of the Stirling combination in Proposition 1: if
`X_s ∼ Gamma(s, 1)` with `s > 0`, then for every integer `m ≥ 0`,
`(1/(m+1)!) ∑_{j=0}^{m+1} [m+1, j] (-1)^{m+1-j} H_n^{(s-j)} =
∑_{k=0}^{n-1} C(k+1, m+1) E[e^{-k X_s}]`. The source assumes `s > m + 1`; the identity holds
for every `s > 0`.

Source: Toshio Nakata, *A Probabilistic Representation of Generalized Harmonic Numbers and an
Identity for Their Sums*, INTEGERS 26 (2026), Article A124, Corollary 1, Equation (8)
(`integers-2026-A124-cor-1`). -/
public theorem_wanted stirlingFirst_generalizedHarmonic_eq_gamma_expectation (m : ℕ) (s : ℝ)
    (hs : 0 < s) (n : ℕ) :
    ((m + 1).factorial : ℝ)⁻¹ * ∑ j ∈ Finset.range (m + 2),
        (Nat.stirlingFirst (m + 1) j : ℝ) * (-1) ^ (m + 1 - j) * generalizedHarmonic (s - j) n =
      ∑ k ∈ Finset.range n,
        ((k + 1).choose (m + 1) : ℝ) * ∫ x, Real.exp (-(k * x)) ∂gammaMeasure s 1

end

end MetaMathlibExt
