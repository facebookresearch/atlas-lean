/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.CyclicExcedanceEGF
public import MathlibExt.Combinatorics.Enumerative.GeneralizedEulerianUnimodal

/-!
# Generalized Eulerian polynomials with a nonnegative gamma vector

Statements from Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5.

The paper treats `q, t, x, y` as indeterminates over `ℚ`; here they are rational numbers
(a polynomial identity over `ℚ` is equivalent to the identity at all rational points), and
the generating function `((x - y) / (x e^(yz) - y e^(xz)))^q e^((x+y)qtz)` is formed for
`x ≠ y`, where its denominator has nonzero constant term. Permutations of `Fin n` are
zero-indexed; excedances `w(i) > i` are `MetaMathlibExt.excedanceCount`, and the
`n`-cycles (all points in one cycle, so the identity of `Fin 1` counts) are those counted by
`MetaMathlibExt.circularEulerian`. The cycle count `cyc(w)` (fixed points included) is
`MetaMathlibExt.cycleQuotientCount` and `fix(w)` is `Fintype.card (Function.fixedPoints w)`.
-/

namespace MetaMathlibExt

open PowerSeries

@[expose] public section

/-- **The gamma coefficients of the generalized Eulerian polynomials count permutations.** Fix
$n \ge 0$ and let $P_n(q, t; x, y)$ be the generalized Eulerian polynomial. For a permutation $w$
of $\{0, 1, \dots, n-1\}$ write $\mathrm{cyc}(w)$ for its number of cycles (fixed points counted
as cycles), $\mathrm{fix}(w)$ for its number of fixed points, $\mathrm{exc}(w)$ for its number of
excedances (points $i$ with $w(i) > i$) and $\mathrm{dexc}(w)$ for its number of double
excedances. For $k \ge 0$ and rational $q, t$ let $\gamma_{n,k}(q, t)$ be the sum of
$q^{\mathrm{cyc}(w)} t^{\mathrm{fix}(w)}$ over the permutations $w$ of $\{0, 1, \dots, n-1\}$
with $\mathrm{exc}(w) = k$ and $\mathrm{dexc}(w) = 0$. Then for all rational $q, t, x, y$ with
$x \ne y$,
$$
P_n(q, t; x, y) = \sum_{k=0}^{\lfloor n/2 \rfloor} \gamma_{n,k}(q, t) x^k y^k (x + y)^{n - 2k},
$$
and for every $k \ge 0$ and all rational $q, t$,
$\gamma_{n,k}(q, t) = \sum_{i=0}^{n} \sum_{j=0}^{n} \gamma_{n,k,i,j} q^i t^j$, where
$\gamma_{n,k,i,j}$ is the number of permutations $w$ of $\{0, 1, \dots, n-1\}$ with
$\mathrm{exc}(w) = k$, $\mathrm{dexc}(w) = 0$, $\mathrm{cyc}(w) = i$ and $\mathrm{fix}(w) = j$.

Source: Pasquale Petrullo and Domenico Senato, *Generalized Eulerian Polynomials with a
Nonnegative Gamma Vector*, Journal of Integer Sequences 27 (2024), Article 24.1.5, Theorem 7
(`jis-2024-24.1.5-thm-7`). -/
public theorem_wanted generalizedEulerianP_gamma_eq (n : ℕ) :
    (∀ q t x y : ℚ, x ≠ y →
      generalizedEulerianP q t x y n =
        ∑ k ∈ Finset.range (n / 2 + 1),
          (∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) ↦
              excedanceCount n w = k ∧ doubleExcedanceCount w = 0),
            q ^ cycleQuotientCount w * t ^ Fintype.card (Function.fixedPoints w)) *
          x ^ k * y ^ k * (x + y) ^ (n - 2 * k)) ∧
    ∀ (k : ℕ) (q t : ℚ),
      ∑ w ∈ Finset.univ.filter (fun w : Equiv.Perm (Fin n) ↦
          excedanceCount n w = k ∧ doubleExcedanceCount w = 0),
        q ^ cycleQuotientCount w * t ^ Fintype.card (Function.fixedPoints w) =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        ((Finset.univ.filter (fun w : Equiv.Perm (Fin n) ↦ excedanceCount n w = k ∧
            doubleExcedanceCount w = 0 ∧
              cycleQuotientCount w = i ∧ Fintype.card (Function.fixedPoints w) = j)).card : ℚ) *
          q ^ i * t ^ j

end

end MetaMathlibExt
