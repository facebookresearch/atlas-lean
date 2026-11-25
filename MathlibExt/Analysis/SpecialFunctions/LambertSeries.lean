/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic

namespace MetaMathlibExt

@[expose] public section

/-!
# Lambert series from the Journal of Integer Sequences

Sources:

* Ž. Tomovski and S. Gerhold, *Mathieu-Fibonacci Series*, Journal of Integer Sequences 25
  (2022),
  [`gerhold6.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL25/Gerhold/gerhold6.tex).
* C. Vignat and M. Milgram, *Curious Multisection Identities by Index Factorization*,
  Journal of Integer Sequences 27 (2024),
  [`milgram5.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL27/Milgram/milgram5.tex).

All series are indexed by `k : ℕ`, with the papers' index `n = k + 1`.
-/

/-- **Lambert series summand.** For a complex number $q$ with $|q| < 1$ and a natural number $k$,
the $k$-th summand of the basic Lambert series is $q^{k+1} / (1 - q^{k+1})$, that is, the term
$q^n / (1 - q^n)$ with $n = k + 1$. -/
public noncomputable def lambertSeriesSummand (q : {q : ℂ // ‖q‖ < 1}) (k : ℕ) : ℂ :=
  (q : ℂ) ^ (k + 1) / (1 - (q : ℂ) ^ (k + 1))

/-- **Lambert series.** For a complex number $q$ with $|q| < 1$, the basic Lambert series is
$L(q) = \sum_{n \ge 1} q^n / (1 - q^n)$. -/
public noncomputable def lambertSeries (q : {q : ℂ // ‖q‖ < 1}) : ℂ :=
  ∑' k, lambertSeriesSummand q k

/-- **Terms of the weighted Lambert series $f$.** For a complex number $q$ with $|q| < 1$ and a
natural number $k$, the term of index $k$ is $n q^n / (1 - q^n)$ with $n = k + 1$. These are the
terms of the weighted Lambert series $f(q) = \sum_{n \ge 1} n q^n / (1 - q^n)$. -/
public noncomputable def lambertFSummand (q : {q : ℂ // ‖q‖ < 1}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) * (q : ℂ) ^ (k + 1) / (1 - (q : ℂ) ^ (k + 1))

/-- **The weighted Lambert series $f$.** For a complex number $q$ with $|q| < 1$, the weighted
Lambert series is $f(q) = \sum_{n \ge 1} n q^n / (1 - q^n)$. -/
public noncomputable def lambertF (q : {q : ℂ // ‖q‖ < 1}) : ℂ :=
  ∑' k, lambertFSummand q k

/-- **Terms of the weighted Lambert series $g$.** For a complex number $q$ with $|q| < 1$ and a
natural number $k$, the term of index $k$ is $n q^n / (1 + q^n)$ with $n = k + 1$. These are the
terms of the weighted Lambert series $g(q) = \sum_{n \ge 1} n q^n / (1 + q^n)$. -/
public noncomputable def lambertGSummand (q : {q : ℂ // ‖q‖ < 1}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) * (q : ℂ) ^ (k + 1) / (1 + (q : ℂ) ^ (k + 1))

/-- **The weighted Lambert series $g$.** For a complex number $q$ with $|q| < 1$, the weighted
Lambert series is $g(q) = \sum_{n \ge 1} n q^n / (1 + q^n)$. -/
public noncomputable def lambertG (q : {q : ℂ // ‖q‖ < 1}) : ℂ :=
  ∑' k, lambertGSummand q k

/-- **Terms of the power-weighted Lambert series $f_\mu$.** For a complex number $q$ with
$|q| < 1$, an integer $\mu \ge 1$ and a natural number $k$, the term of index $k$ is
$n^\mu q^n / (1 - q^n)$ with $n = k + 1$. These are the terms of the power-weighted Lambert series
$f_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 - q^n)$. -/
public noncomputable def lambertFMuSummand (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) ^ (μ : ℕ) * (q : ℂ) ^ (k + 1) / (1 - (q : ℂ) ^ (k + 1))

/-- **The power-weighted Lambert series $f_\mu$.** For a complex number $q$ with $|q| < 1$ and an
integer $\mu \ge 1$, the power-weighted Lambert series is
$f_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 - q^n)$. -/
public noncomputable def lambertFMu (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) : ℂ :=
  ∑' k, lambertFMuSummand q μ k

/-- **Terms of the power-weighted Lambert series $g_\mu$.** For a complex number $q$ with
$|q| < 1$, an integer $\mu \ge 1$ and a natural number $k$, the term of index $k$ is
$n^\mu q^n / (1 + q^n)$ with $n = k + 1$. These are the terms of the power-weighted Lambert series
$g_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 + q^n)$. -/
public noncomputable def lambertGMuSummand (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) ^ (μ : ℕ) * (q : ℂ) ^ (k + 1) / (1 + (q : ℂ) ^ (k + 1))

/-- **The power-weighted Lambert series $g_\mu$.** For a complex number $q$ with $|q| < 1$ and an
integer $\mu \ge 1$, the power-weighted Lambert series is
$g_\mu(q) = \sum_{n \ge 1} n^\mu q^n / (1 + q^n)$. -/
public noncomputable def lambertGMu (q : {q : ℂ // ‖q‖ < 1})
    (μ : {μ : ℕ // 1 ≤ μ}) : ℂ :=
  ∑' k, lambertGMuSummand q μ k

/-- **Terms of the Lambert family $L_m$.** For a complex number $q$ with $|q| < 1$, an integer
$m \ge 1$ and a natural number $k$, the term of index $k$ is $q^{mn} / (1 - q^{2n})^m$ with
$n = k + 1$. These are the terms of $L_m(q) = \sum_{n \ge 1} q^{mn} / (1 - q^{2n})^m$. -/
public noncomputable def lambertLmSummand (q : {q : ℂ // ‖q‖ < 1})
    (m : {m : ℕ // 1 ≤ m}) (k : ℕ) : ℂ :=
  (q : ℂ) ^ ((m : ℕ) * (k + 1)) /
    (1 - (q : ℂ) ^ (2 * (k + 1))) ^ (m : ℕ)

/-- **The Lambert family $L_m$.** For a complex number $q$ with $|q| < 1$ and an integer $m \ge 1$,
the Lambert family is $L_m(q) = \sum_{n \ge 1} q^{mn} / (1 - q^{2n})^m$. -/
public noncomputable def lambertLm (q : {q : ℂ // ‖q‖ < 1})
    (m : {m : ℕ // 1 ≤ m}) : ℂ :=
  ∑' k, lambertLmSummand q m k

end

end MetaMathlibExt
