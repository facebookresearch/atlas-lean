/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LurothConsecutiveDigitsIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import MathlibExt.NumberTheory.LurothConsecutiveDigitsLeVolumeLurothDigitsGe
public import MathlibExt.NumberTheory.LurothConsecutiveDigitsVolumeLurothCylinder
public import MathlibExt.NumberTheory.LurothConsecutiveDigits

/-!
# Functions of consecutive digits in Lüroth series

Statements from Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67.

The first Lüroth digit of `x ∈ (0, 1]` is `d₁(x) = ⌊1 / x⌋ + 1 ≥ 2` and the Lüroth map is
`L(x) = d₁(x) (d₁(x) - 1) x - (d₁(x) - 1)` (with `L(0) = 0`, which the formula gives in
Lean since `1 / 0 = 0`); the `n`-th digit is `d_n(x) = d₁(L^{n-1}(x))`. In Lean the digits
are indexed from `0`: `lurothDigitSeq x k = d_{k+1}(x)`. Sequences `Ψ` are indexed from `0`
as well; the paper's sums over `n ≥ 1` and "infinitely many `n`" are shift-invariant.

Theorems 1 and 2 are quoted in the paper from its references [3] and [2]. Not stated (see
the source audit table): the endpoint formula of Proposition 1 (the paper's `⟨c₁, …, cₙ⟩` is
not defined in the extracted text).
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MetaMathlibExt

@[expose] public section

/-- **First Lüroth digit of 1.** The first Lüroth digit of $1$ is $d_1(1) = 2$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `d₁`). -/
theorem lurothDigit_one : lurothDigit 1 = 2 := by
  simp [lurothDigit]

/-- **First Lüroth digit of 1/2.** The first Lüroth digit of $1/2$ is $d_1(1/2) = 3$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `d₁`). -/
theorem lurothDigit_half : lurothDigit (1 / 2) = 3 := by
  norm_num [lurothDigit]

/-- **The Lüroth map fixes 1.** The Lüroth map $L$ satisfies $L(1) = 1$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `L`). -/
theorem lurothMap_one : lurothMap 1 = 1 := by
  norm_num [lurothMap, lurothDigit_one]

/-- **The Lüroth map at 1/2.** The Lüroth map $L$ sends $1/2$ to $1$: $L(1/2) = 1$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `L`). -/
theorem lurothMap_half : lurothMap (1 / 2) = 1 := by
  norm_num [lurothMap, lurothDigit_half]

/-- **The Lüroth map fixes 0.** The Lüroth map $L$ satisfies $L(0) = 0$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `L`). -/
theorem lurothMap_zero : lurothMap 0 = 0 := by
  simp [lurothMap, lurothDigit]

/-- **The Lüroth map shifts the digits.** For every real number $x$ and every $n \ge 1$, the
$n$-th Lüroth digit of $L(x)$, where $L$ is the Lüroth map, is the $(n+1)$-st Lüroth digit of
$x$: $d_n(L(x)) = d_{n+1}(x)$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Section 2
(definition of `d_n`). -/
theorem lurothDigitSeq_succ (x : ℝ) (k : ℕ) :
    lurothDigitSeq x (k + 1) = lurothDigitSeq (lurothMap x) k := by
  simp [lurothDigitSeq, Function.iterate_succ_apply]

/-- **Zero-one law for weighted products of consecutive Lüroth digits.** Let $m \ge 1$, let
$t_0, \dots, t_{m-1}$ be positive reals, let $T = \max_i t_i$ and let $\ell$ be the number of
indices $j$ with $t_j = T$. Let $(\Psi(n))_{n \ge 0}$ be a sequence of positive reals for which
there is $c > 1$ with $\Psi(n) \ge c$ for all sufficiently large $n$ (equivalently,
$\liminf_n \Psi(n) > 1$). Write $d_k(x)$ for the $k$-th Lüroth digit of $x$ and let $E$ be the
set of $x \in (0, 1]$ such that $\prod_{i=0}^{m-1} d_{n+i+1}(x)^{t_i} \ge \Psi(n)$ for
infinitely many $n$. If the series $\sum_{n \ge 0} (\log \Psi(n))^{\ell - 1} / \Psi(n)^{1/T}$
converges then $E$ has Lebesgue measure $0$, and if it diverges then $E$ has Lebesgue
measure $1$.

The paper quotes this result from Brown-Sarre, Robert and Hussain (its reference [2]).

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 2, with `T` and
`ℓ(t)` from (2) (`integers-2024-A67-thm-2`). -/
public theorem_wanted volume_lurothWeightedProduct_ge_zero_one {m : ℕ} (hm : 0 < m)
    (t : Fin m → ℝ) (ht : ∀ i, 0 < t i) (Ψ : ℕ → ℝ) (hΨ : ∀ n, 0 < Ψ n)
    (hlim : ∃ c : ℝ, 1 < c ∧ ∀ᶠ n in atTop, c ≤ Ψ n) :
    let T := ⨆ i, t i
    let ℓ := (Finset.univ.filter fun j => t j = T).card
    let E := {x ∈ Set.Ioc (0 : ℝ) 1 |
      ∃ᶠ n in atTop, Ψ n ≤ ∏ i : Fin m, (lurothDigitSeq x (n + i) : ℝ) ^ t i}
    (Summable (fun n => Real.log (Ψ n) ^ (ℓ - 1) / Ψ n ^ (1 / T)) → volume E = 0) ∧
      (¬ Summable (fun n => Real.log (Ψ n) ^ (ℓ - 1) / Ψ n ^ (1 / T)) → volume E = 1)

/-- **Zero-one law for functions of consecutive Lüroth digits.** Let $m \in \mathbb{N}$, let $F$
be a real-valued function on $m$-tuples of natural numbers and let $(\Psi(n))_{n \ge 0}$ be a
real sequence. For $y \in \mathbb{R}$ put
$$H(y) = \sum_{a} \prod_{i=1}^{m} \frac{1}{a_i (a_i - 1)} \in [0, \infty],$$
the sum running over the $a = (a_1, \dots, a_m) \in \mathbb{N}^m$ with every $a_i \ge 2$ and
$F(a) \ge y$. Write $d_k(x)$ for the $k$-th Lüroth digit of $x$ and let $E$ be the set of
$x \in (0, 1]$ such that $F(d_{n+1}(x), \dots, d_{n+m}(x)) \ge \Psi(n)$ for infinitely many
$n$. If $\sum_{n \ge 0} H(\Psi(n)) < \infty$ then $E$ has Lebesgue measure $0$, and if
$\sum_{n \ge 0} H(\Psi(n)) = \infty$ then $E$ has Lebesgue measure $1$.

Unlike the paper, $F$ and $\Psi$ need not be positive.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 3, with
`H` from (4) (`integers-2024-A67-thm-3`). -/
public theorem_wanted volume_lurothConsecutiveDigits_zero_one {m : ℕ}
    (F : (Fin m → ℕ) → ℝ) (Ψ : ℕ → ℝ) :
    let H : ℝ → ℝ≥0∞ := fun y => ∑' d : Fin m → ℕ,
      if (∀ i, 2 ≤ d i) ∧ y ≤ F d then ∏ i, ENNReal.ofReal (1 / ((d i : ℝ) * ((d i : ℝ) - 1)))
      else 0
    let E := {x ∈ Set.Ioc (0 : ℝ) 1 |
      ∃ᶠ n in atTop, Ψ n ≤ F (fun i => lurothDigitSeq x (n + i))}
    (∑' n, H (Ψ n) < ∞ → volume E = 0) ∧ (∑' n, H (Ψ n) = ∞ → volume E = 1)

/-- **Borel–Cantelli dichotomy for Lüroth cylinder events.** Let $m \in \mathbb{N}$, let
$(S_n)_{n \ge 0}$ be a sequence of sets of $m$-tuples of natural numbers, write $d_k(x)$ for
the $k$-th Lüroth digit of $x$ and $\lambda$ for Lebesgue measure. Put
$A_n = \{x \in (0, 1] : (d_1(x), \dots, d_m(x)) \in S_n\}$ (a union of cylinders of level $m$)
and let $E$ be the set of $x \in (0, 1]$ such that $(d_{n+1}(x), \dots, d_{n+m}(x)) \in S_n$
for infinitely many $n$. If $\sum_{n \ge 0} \lambda(A_n) < \infty$ then $\lambda(E) = 0$, and
if $\sum_{n \ge 0} \lambda(A_n) = \infty$ then $\lambda(E) = 1$.

Source: Dmitry Kleinbock and Yuqing Zhang, *Metrical Properties of Functions of
Consecutive Digits in Lüroth Series*, INTEGERS 24 (2024), Article A67, Theorem 5
(`integers-2024-A67-thm-5`). -/
public theorem_wanted volume_limsup_lurothPreimage_zero_one {m : ℕ}
    (S : ℕ → Set (Fin m → ℕ)) :
    let A : ℕ → Set ℝ := fun n =>
      {x ∈ Set.Ioc (0 : ℝ) 1 | (fun i : Fin m => lurothDigitSeq x i) ∈ S n}
    let E := {x ∈ Set.Ioc (0 : ℝ) 1 |
      ∃ᶠ n in atTop, (fun i : Fin m => lurothDigitSeq x (n + i)) ∈ S n}
    (∑' n, volume (A n) < ∞ → volume E = 0) ∧ (∑' n, volume (A n) = ∞ → volume E = 1)

end

end MetaMathlibExt
