/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.PermutationStatistics
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import WantedExt.Combinatorics.Enumerative.OddFibonacciWanted

/-!
# Permutations avoiding two patterns of length three

The enumeration of `S_n(τ, ρ)` for pairs of length-`3` patterns (Simion and
Schmidt), as recalled in Han, *Joint Distributions of 10 Classical Statistics
over Permutations Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article
A18, Theorem 1. Patterns are permutations of `Fin 3` built from zero-based
one-line values by `pattern3` (e.g. `pattern3 ![0, 1, 2]` is `123`); containment is
the classical `HasPattern` of `OddFibonacciWanted`.

The joint distribution of the ten statistics `asc`, `des`, `lrmax`, `rlmax`, `lrmin`, `rlmin`,
`dasc`, `ddes`, `pk`, `vl` (Section 1 of the source) is the power series `classicalStatGF` over
`MvPolynomial (Fin 10) ℚ`; its rational closed forms (Theorems 2, 3, 5) are stated after clearing
denominators. Theorems 4 and 6 and Corollary 5 are false as printed and are not stated.
-/

namespace MetaMathlibExt

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

@[expose] public section

/-- **Length-three pattern from one-line values.** Given a bijection $v$ from $\{0, 1, 2\}$ to
itself, this is the permutation of $\{0, 1, 2\}$ that sends $i$ to $v(i)$. The values are listed
zero-based, so $v = (0, 2, 1)$ gives the pattern $132$ in the usual one-based one-line notation.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1. -/
public def pattern3 (v : Fin 3 → Fin 3) (hv : Function.Bijective v := by decide) :
    Equiv.Perm (Fin 3) where
  toFun := v
  invFun := Fintype.bijInv hv
  left_inv := Fintype.leftInverse_bijInv hv
  right_inv := Fintype.rightInverse_bijInv hv

/-- Classical pattern containment `HasPattern σ π` is decidable.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1. -/
public instance {n k : ℕ} (σ : Equiv.Perm (Fin n)) (π : Fin k → Fin k) :
    Decidable (HasPattern σ π) := by
  unfold HasPattern
  infer_instance

/-- **Number of permutations avoiding two patterns of length three.** For a natural number $n$
and permutations $\tau$ and $\rho$ of $\{0, 1, 2\}$, $A_n(\tau, \rho)$ is the number of
permutations of $\{0, 1, \dots, n - 1\}$ that contain neither $\tau$ nor $\rho$ as a classical
pattern.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 1. -/
public def twoPatternAvoiderCount (n : ℕ) (τ ρ : Equiv.Perm (Fin 3)) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ¬ HasPattern σ τ ∧ ¬ HasPattern σ ρ).card

/-- **Permutations of length three avoiding $123$ and $132$.** Exactly $4$ permutations of
$\{0, 1, 2\}$ avoid both patterns $123$ and $132$, that is, $A_3(123, 132) = 4$: of the six
permutations of length $3$, only $123$ and $132$ themselves are excluded.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 1. -/
public theorem twoPatternAvoiderCount_three_123_132 :
    twoPatternAvoiderCount 3 (pattern3 ![0, 1, 2]) (pattern3 ![0, 2, 1]) = 4 := by
  decide +kernel

/-- **Permutations of length four avoiding $132$ and $321$.** Exactly $7$ permutations of
$\{0, 1, 2, 3\}$ avoid both patterns $132$ and $321$, that is,
$A_4(132, 321) = 7 = 1 + \binom{4}{2}$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 1. -/
public theorem twoPatternAvoiderCount_four_132_321 :
    twoPatternAvoiderCount 4 (pattern3 ![0, 2, 1]) (pattern3 ![2, 1, 0]) = 7 := by
  decide +kernel

/-- **Simion–Schmidt enumeration of permutations avoiding two patterns of length three.** For
every $n \ge 1$, writing $A_n(\tau, \rho)$ for the number of permutations of
$\{0, 1, \dots, n - 1\}$ avoiding both patterns $\tau$ and $\rho$:
(a) $A_n(123, 132) = A_n(123, 213) = A_n(321, 231) = A_n(321, 312) = 2^{n-1}$;
(b) $A_n(231, 312) = A_n(132, 213) = 2^{n-1}$;
(c) $A_n(213, 312) = A_n(132, 231) = 2^{n-1}$;
(d) $A_n(213, 231) = A_n(132, 312) = 2^{n-1}$;
(e) $A_n(132, 321) = A_n(123, 231) = A_n(123, 312) = A_n(213, 321) = 1 + \binom{n}{2}$;
(f) $A_n(123, 321)$ equals $n$ if $n \le 2$, equals $4$ if $n \in \{3, 4\}$, and equals $0$ if
$n \ge 5$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 1
(`integers-2026-A18-thm-1`), citing Simion and Schmidt. -/
public theorem_wanted twoPatternAvoiderCount_length_three {n : ℕ} (hn : 1 ≤ n) :
    (twoPatternAvoiderCount n (pattern3 ![0, 1, 2]) (pattern3 ![0, 2, 1]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![0, 1, 2]) (pattern3 ![1, 0, 2]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![2, 1, 0]) (pattern3 ![1, 2, 0]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![2, 1, 0]) (pattern3 ![2, 0, 1]) = 2 ^ (n - 1)) ∧
    (twoPatternAvoiderCount n (pattern3 ![1, 2, 0]) (pattern3 ![2, 0, 1]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![0, 2, 1]) (pattern3 ![1, 0, 2]) = 2 ^ (n - 1)) ∧
    (twoPatternAvoiderCount n (pattern3 ![1, 0, 2]) (pattern3 ![2, 0, 1]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![0, 2, 1]) (pattern3 ![1, 2, 0]) = 2 ^ (n - 1)) ∧
    (twoPatternAvoiderCount n (pattern3 ![1, 0, 2]) (pattern3 ![1, 2, 0]) = 2 ^ (n - 1) ∧
      twoPatternAvoiderCount n (pattern3 ![0, 2, 1]) (pattern3 ![2, 0, 1]) = 2 ^ (n - 1)) ∧
    (twoPatternAvoiderCount n (pattern3 ![0, 2, 1]) (pattern3 ![2, 1, 0]) = 1 + n.choose 2 ∧
      twoPatternAvoiderCount n (pattern3 ![0, 1, 2]) (pattern3 ![1, 2, 0]) = 1 + n.choose 2 ∧
      twoPatternAvoiderCount n (pattern3 ![0, 1, 2]) (pattern3 ![2, 0, 1]) = 1 + n.choose 2 ∧
      twoPatternAvoiderCount n (pattern3 ![1, 0, 2]) (pattern3 ![2, 1, 0]) = 1 + n.choose 2) ∧
    twoPatternAvoiderCount n (pattern3 ![0, 1, 2]) (pattern3 ![2, 1, 0]) =
      if n ≤ 2 then n else if n ≤ 4 then 4 else 0

/-- **Ascent number of a permutation.** For a permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$,
$\operatorname{asc}(\sigma)$ is the number of positions $i$ with $i + 1 < n$ and
$\sigma(i) < \sigma(i + 1)$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`asc`, `des`). -/
public def permAscents {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∃ h : i.val + 1 < n, σ i < σ ⟨i.val + 1, h⟩).card

/-- **Descent number of a permutation.** For a permutation $\sigma$ of $\{0, 1, \dots, n - 1\}$,
$\operatorname{des}(\sigma)$ is the number of positions $i$ with $i + 1 < n$ and
$\sigma(i + 1) < \sigma(i)$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`asc`, `des`). -/
public def permDescents {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => ∃ h : i.val + 1 < n, σ ⟨i.val + 1, h⟩ < σ i).card

/-- **Ascents and descents of $123$ and $132$.** Writing permutations of $\{0, 1, 2\}$ in
one-based one-line notation, the identity $123$ has two ascents and no descents,
$\operatorname{asc}(123) = 2$ and $\operatorname{des}(123) = 0$, and $132$ has one of each,
$\operatorname{asc}(132) = \operatorname{des}(132) = 1$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`asc`, `des`). -/
public theorem permAscents_permDescents_small :
    permAscents (1 : Equiv.Perm (Fin 3)) = 2 ∧ permDescents (1 : Equiv.Perm (Fin 3)) = 0 ∧
      permAscents (pattern3 ![0, 2, 1]) = 1 ∧ permDescents (pattern3 ![0, 2, 1]) = 1 := by
  decide +kernel

/-- **Ascent–descent generating function of a pair of patterns.** For permutations $\tau$ and
$\rho$ of $\{0, 1, 2\}$, let $S_n(\tau, \rho)$ be the set of permutations of
$\{0, 1, \dots, n-1\}$ that contain neither $\tau$ nor $\rho$ as a classical pattern. The
ascent–descent generating function of $(\tau, \rho)$ is the formal power series
$$\sum_{n \ge 0} \sum_{\sigma \in S_n(\tau, \rho)}
x^n p^{\mathrm{asc}(\sigma)} q^{\mathrm{des}(\sigma)}$$
in $x$ with coefficients in the polynomial ring $\mathbb{Q}[p, q]$, where $\mathrm{asc}(\sigma)$
and $\mathrm{des}(\sigma)$ are the numbers of ascents and descents of $\sigma$. The empty
permutation ($n = 0$) contributes the constant term $1$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`asc`, `des`). -/
public noncomputable def ascDesGF (τ ρ : Equiv.Perm (Fin 3)) :
    PowerSeries (MvPolynomial (Fin 2) ℚ) :=
  PowerSeries.mk fun n => ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ¬ HasPattern σ τ ∧ ¬ HasPattern σ ρ),
      MvPolynomial.X 0 ^ permAscents σ * MvPolynomial.X 1 ^ permDescents σ

/-- **Ascents and descents over permutations avoiding $123$ and $132$.** Let
$$G = \sum_{n \ge 0} \sum_{\sigma} x^n p^{\mathrm{asc}(\sigma)} q^{\mathrm{des}(\sigma)},$$
where $\sigma$ runs over the permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$123$ and $132$, and $\mathrm{asc}(\sigma)$ and $\mathrm{des}(\sigma)$ are the numbers of ascents
and descents of $\sigma$; $G$ is a formal power series in $x$ with coefficients in
$\mathbb{Q}[p, q]$. Then
$$(1 - 2qx - pqx^2 + q^2x^2)\, G = 1 + x - 2qx + px^2 - qx^2 - pqx^2 + q^2x^2.$$

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 1
(`integers-2026-A18-cor-1`). -/
public theorem_wanted ascDesGF_123_132 :
    let p : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - 2 * q * PowerSeries.X - p * q * PowerSeries.X ^ 2 + q ^ 2 * PowerSeries.X ^ 2) *
        ascDesGF (pattern3 ![0, 1, 2]) (pattern3 ![0, 2, 1]) =
      1 + PowerSeries.X - 2 * q * PowerSeries.X + p * PowerSeries.X ^ 2 -
        q * PowerSeries.X ^ 2 - p * q * PowerSeries.X ^ 2 + q ^ 2 * PowerSeries.X ^ 2

/-- **Ascents and descents over permutations avoiding $132$ and $321$.** Let
$$G = \sum_{n \ge 0} \sum_{\sigma} x^n p^{\mathrm{asc}(\sigma)} q^{\mathrm{des}(\sigma)},$$
where $\sigma$ runs over the permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$132$ and $321$, and $\mathrm{asc}(\sigma)$ and $\mathrm{des}(\sigma)$ are the numbers of ascents
and descents of $\sigma$; $G$ is a formal power series in $x$ with coefficients in
$\mathbb{Q}[p, q]$. Then
$$(1 - px)^3\, G = 1 + x - 3px - 2px^2 + 3p^2x^2 + qx^2 + p^2x^3 - p^3x^3.$$

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 2
(`integers-2026-A18-cor-2`). -/
public theorem_wanted ascDesGF_132_321 :
    let p : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - p * PowerSeries.X) ^ 3 * ascDesGF (pattern3 ![0, 2, 1]) (pattern3 ![2, 1, 0]) =
      1 + PowerSeries.X - 3 * p * PowerSeries.X - 2 * p * PowerSeries.X ^ 2 +
        3 * p ^ 2 * PowerSeries.X ^ 2 + q * PowerSeries.X ^ 2 + p ^ 2 * PowerSeries.X ^ 3 -
        p ^ 3 * PowerSeries.X ^ 3

/-- **Ascents and descents over permutations avoiding $213$ and $231$.** Let
$$G = \sum_{n \ge 0} \sum_{\sigma} x^n p^{\mathrm{asc}(\sigma)} q^{\mathrm{des}(\sigma)},$$
where $\sigma$ runs over the permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$213$ and $231$, and $\mathrm{asc}(\sigma)$ and $\mathrm{des}(\sigma)$ are the numbers of ascents
and descents of $\sigma$; $G$ is a formal power series in $x$ with coefficients in
$\mathbb{Q}[p, q]$. Then
$$(1 - px - qx)\, G = 1 + x - px - qx.$$

The lead-in of the source's Corollary 4 names the permutations avoiding $213$ and $312$ instead;
both classes have this distribution of ascents and descents.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 4
(`integers-2026-A18-cor-4`). -/
public theorem_wanted ascDesGF_213_231 :
    let p : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - p * PowerSeries.X - q * PowerSeries.X) *
        ascDesGF (pattern3 ![1, 0, 2]) (pattern3 ![1, 2, 0]) =
      1 + PowerSeries.X - p * PowerSeries.X - q * PowerSeries.X

/-- **Left-to-right and right-to-left extrema of $132$ and $213$.** Writing permutations of
$\{0, 1, 2\}$ in one-based one-line notation, $132$ has $2$ left-to-right maxima, $2$
right-to-left maxima, $1$ left-to-right minimum and $2$ right-to-left minima, and $213$ has $2$
left-to-right maxima, $1$ right-to-left maximum, $2$ left-to-right minima and $2$ right-to-left
minima.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1
(`lrmax`, `rlmax`, `lrmin`, `rlmin`). -/
public theorem permExtrema_small :
    permLeftToRightMaxCount (pattern3 ![0, 2, 1]) = 2 ∧
      permRightToLeftMaxCount (pattern3 ![0, 2, 1]) = 2 ∧
      permLeftToRightMinCount (pattern3 ![0, 2, 1]) = 1 ∧
      permRightToLeftMinCount (pattern3 ![0, 2, 1]) = 2 ∧
      permLeftToRightMaxCount (pattern3 ![1, 0, 2]) = 2 ∧
      permRightToLeftMaxCount (pattern3 ![1, 0, 2]) = 1 ∧
      permLeftToRightMinCount (pattern3 ![1, 0, 2]) = 2 ∧
      permRightToLeftMinCount (pattern3 ![1, 0, 2]) = 2 := by
  decide +kernel

/-- **Double ascents, double descents, peaks and valleys in length three.** Writing permutations
of $\{0, 1, 2\}$ in one-based one-line notation, and $\operatorname{dasc}$,
$\operatorname{ddes}$, $\operatorname{pk}$ and $\operatorname{vl}$ for the numbers of double
ascents, double descents, peaks and valleys, $\operatorname{dasc}(123) = 1$,
$\operatorname{ddes}(321) = 1$, $\operatorname{dasc}(132) = \operatorname{ddes}(132) = 0$,
$\operatorname{pk}(132) = 1$, $\operatorname{vl}(132) = 0$, $\operatorname{pk}(213) = 0$ and
$\operatorname{vl}(213) = 1$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1
(`dasc`, `ddes`, `pk`, `vl`). -/
public theorem permDoubleAscents_peaks_small :
    permDoubleAscents (pattern3 ![0, 1, 2]) = 1 ∧
      permDoubleDescents (pattern3 ![2, 1, 0]) = 1 ∧
      permDoubleAscents (pattern3 ![0, 2, 1]) = 0 ∧
      permDoubleDescents (pattern3 ![0, 2, 1]) = 0 ∧
      permPeaks (pattern3 ![0, 2, 1]) = 1 ∧ permValleys (pattern3 ![0, 2, 1]) = 0 ∧
      permPeaks (pattern3 ![1, 0, 2]) = 0 ∧ permValleys (pattern3 ![1, 0, 2]) = 1 := by
  decide +kernel

/-- **Generating function of ten classical statistics over a pair of patterns.** For
permutations $\tau$ and $\rho$ of $\{0, 1, 2\}$, let $S_n(\tau, \rho)$ be the set of permutations
of $\{0, 1, \dots, n-1\}$ that contain neither $\tau$ nor $\rho$ as a classical pattern. The
generating function $F_{(\tau, \rho)}$ is the formal power series
$$F_{(\tau, \rho)} = \sum_{n \ge 0} \sum_{\sigma \in S_n(\tau, \rho)} x^n
p^{\mathrm{asc}(\sigma)} q^{\mathrm{des}(\sigma)} u^{\mathrm{lrmax}(\sigma)}
v^{\mathrm{rlmax}(\sigma)} s^{\mathrm{lrmin}(\sigma)} t^{\mathrm{rlmin}(\sigma)}
y^{\mathrm{dasc}(\sigma)} z^{\mathrm{ddes}(\sigma)} \ell^{\mathrm{pk}(\sigma)}
m^{\mathrm{vl}(\sigma)}$$
in $x$ with coefficients in the polynomial ring $\mathbb{Q}[p, q, u, v, s, t, y, z, \ell, m]$.
Here $\mathrm{asc}$ and $\mathrm{des}$ count ascents and descents, $\mathrm{lrmax}$ and
$\mathrm{rlmax}$ left-to-right and right-to-left maxima, $\mathrm{lrmin}$ and $\mathrm{rlmin}$
left-to-right and right-to-left minima, $\mathrm{dasc}$ and $\mathrm{ddes}$ double ascents and
double descents, and $\mathrm{pk}$ and $\mathrm{vl}$ peaks and valleys. The empty permutation
($n = 0$) contributes the constant term $1$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1
(the g.f. `F_(τ,ρ)`). -/
public noncomputable def classicalStatGF (τ ρ : Equiv.Perm (Fin 3)) :
    PowerSeries (MvPolynomial (Fin 10) ℚ) :=
  PowerSeries.mk fun n => ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ¬ HasPattern σ τ ∧ ¬ HasPattern σ ρ),
      MvPolynomial.X 0 ^ permAscents σ * MvPolynomial.X 1 ^ permDescents σ *
        MvPolynomial.X 2 ^ permLeftToRightMaxCount σ *
        MvPolynomial.X 3 ^ permRightToLeftMaxCount σ *
        MvPolynomial.X 4 ^ permLeftToRightMinCount σ *
        MvPolynomial.X 5 ^ permRightToLeftMinCount σ *
        MvPolynomial.X 6 ^ permDoubleAscents σ * MvPolynomial.X 7 ^ permDoubleDescents σ *
        MvPolynomial.X 8 ^ permPeaks σ * MvPolynomial.X 9 ^ permValleys σ

/-- **Double ascent–double descent generating function of a pair of patterns.** For
permutations $\tau$ and $\rho$ of $\{0, 1, 2\}$, let $S_n(\tau, \rho)$ be the set of permutations
of $\{0, 1, \dots, n-1\}$ that contain neither $\tau$ nor $\rho$ as a classical pattern. The
double ascent–double descent generating function of $(\tau, \rho)$ is the formal power series
$$\sum_{n \ge 0} \sum_{\sigma \in S_n(\tau, \rho)}
x^n y^{\mathrm{dasc}(\sigma)} z^{\mathrm{ddes}(\sigma)}$$
in $x$ with coefficients in the polynomial ring $\mathbb{Q}[y, z]$, where $\mathrm{dasc}(\sigma)$
and $\mathrm{ddes}(\sigma)$ are the numbers of double ascents and double descents of $\sigma$.
The empty permutation ($n = 0$) contributes the constant term $1$.

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Section 1 (`dasc`, `ddes`). -/
public noncomputable def dascDdesGF (τ ρ : Equiv.Perm (Fin 3)) :
    PowerSeries (MvPolynomial (Fin 2) ℚ) :=
  PowerSeries.mk fun n => ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
    ¬ HasPattern σ τ ∧ ¬ HasPattern σ ρ),
      MvPolynomial.X 0 ^ permDoubleAscents σ * MvPolynomial.X 1 ^ permDoubleDescents σ

/-- **Ten classical statistics over permutations avoiding $123$ and $132$.** Let $F$ be the
joint generating function of the ten classical statistics over the permutations avoiding both
patterns $123$ and $132$: a formal power series in $x$ over
$\mathbb{Q}[p, q, u, v, s, t, y, z, \ell, m]$ in which $x$ marks the length and
$p, q, u, v, s, t, y, z, \ell, m$ mark the numbers of ascents, descents, left-to-right maxima,
right-to-left maxima, left-to-right minima, right-to-left minima, double ascents, double
descents, peaks and valleys, respectively. Then
$$
(1 - \ell m p q s v x^2 - q s x z - q s v x z + q^2 s^2 v x^2 z^2)\, F = 1 +
s x \bigl(t u v + p t^2 u^2 v x - q(\ell m p v x + z + v z)\bigr) +
q^2 s^3 t u v^2 x^3 \bigl(\ell p u x (m - z) + z(-1 - m p t u x + z + p t u x z)\bigr) +
q s^2 v x^2 \bigl(q z^2 + p t^2 u x \bigl(m(u + v) - u(1 + v) z\bigr) +
t u \bigl(-z - v(-1 + \ell p (m - u) x + z)\bigr)\bigr).
$$

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 2
(`integers-2026-A18-thm-2`). -/
public theorem_wanted classicalStatGF_123_132 :
    let x : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.X
    let p : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    let u : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 2)
    let v : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 3)
    let s : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 4)
    let t : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 5)
    let y : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 6)
    let z : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 7)
    let ℓ : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 8)
    let m : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 9)
    (1 - ℓ * m * p * q * s * v * x ^ 2 - q * s * x * z - q * s * v * x * z + q ^ 2 * s ^ 2 * v *
        x ^ 2 * z ^ 2) *
        classicalStatGF (pattern3 ![0, 1, 2]) (pattern3 ![0, 2, 1]) =
      1 + s * x * (t * u * v + p * t ^ 2 * u ^ 2 * v * x - q * (ℓ * m * p * v * x + z + v * z))
        + q ^ 2 * s ^ 3 * t * u * v ^ 2 * x ^ 3 * (ℓ * p * u * x * (m - z) + z * (-1 - m * p * t * u
        * x + z + p * t * u * x * z)) + q * s ^ 2 * v * x ^ 2 * (q * z ^ 2 + p * t ^ 2 * u * x * (m
        * (u + v) - u * (1 + v) * z) + t * u * (-z - v * (-1 + ℓ * p * (m - u) * x + z)))

set_option maxHeartbeats 400000 in
/-- **Ten classical statistics over permutations avoiding $132$ and $321$.** Let $F$ be the
joint generating function of the ten classical statistics over the permutations avoiding both
patterns $132$ and $321$: a formal power series in $x$ over
$\mathbb{Q}[p, q, u, v, s, t, y, z, \ell, m]$ in which $x$ marks the length and
$p, q, u, v, s, t, y, z, \ell, m$ mark the numbers of ascents, descents, left-to-right maxima,
right-to-left maxima, left-to-right minima, right-to-left minima, double ascents, double
descents, peaks and valleys, respectively. Then $(1 - ptxy)(1 - puxy)(1 - ptuxy)\, F$ equals
$$
1 + stuvx + pst^2u^2vx^2 + qs^2tuv^2x^2 + mpqs^2t^2u^2vx^3 + mpqs^2t^2uv^2x^3 +
\ell pqs^2tu^2v^2x^3 + \ell mp^2qs^2t^2u^3vx^4 + \ell mp^2qs^2t^2u^2v^2x^4 - ptxy - puxy -
pqs^2tu^2v^2x^3y - pst^2uvx^2y - pstu^2vx^2y - pst^2u^2vx^2y - p^2st^3u^2vx^3y -
p^2st^2u^3vx^3y - pqs^2t^2uv^2x^3y - ptuxy - pqs^2t^2u^2v^2x^3y - mp^2qs^2t^2u^3vx^4y -
\ell p^2qs^2t^2u^2v^2x^4y - mp^2qs^2t^2u^2v^2x^4y - mp^2qs^2t^3u^2v^2x^4y -
\ell p^2qs^2t^2u^3v^2x^4y - \ell mp^3qs^2t^3u^3v^2x^5y + p^2tux^2y^2 + p^2t^2ux^2y^2 +
p^2tu^2x^2y^2 + p^2st^2u^2vx^3y^2 + p^2st^3u^2vx^3y^2 + p^2st^2u^3vx^3y^2 +
p^3st^3u^3vx^4y^2 + p^2qs^2t^2u^2v^2x^4y^2 + p^2qs^2t^3u^2v^2x^4y^2 +
p^2qs^2t^2u^3v^2x^4y^2 + \ell p^3qs^2t^3u^3v^2x^5y^2 + mp^3qs^2t^3u^3v^2x^5y^2 -
p^3t^2u^2x^3y^3 - p^3st^3u^3vx^4y^3 - p^3qs^2t^3u^3v^2x^5y^3.
$$

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 3
(`integers-2026-A18-thm-3`). -/
public theorem_wanted classicalStatGF_132_321 :
    let x : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.X
    let p : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    let u : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 2)
    let v : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 3)
    let s : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 4)
    let t : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 5)
    let y : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 6)
    let z : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 7)
    let ℓ : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 8)
    let m : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 9)
    ((1 - p * t * x * y) * (1 - p * u * x * y) * (1 - p * t * u * x * y)) *
        classicalStatGF (pattern3 ![0, 2, 1]) (pattern3 ![2, 1, 0]) =
      1 + s * t * u * v * x + p * s * t ^ 2 * u ^ 2 * v * x ^ 2 + q * s ^ 2 * t * u * v ^ 2 * x ^ 2
        + m * p * q * s ^ 2 * t ^ 2 * u ^ 2 * v * x ^ 3 + m * p * q * s ^ 2 * t ^ 2 * u * v ^ 2 *
        x ^ 3 + ℓ * p * q * s ^ 2 * t * u ^ 2 * v ^ 2 * x ^ 3 + ℓ * m * p ^ 2 * q * s ^ 2 * t ^ 2 *
        u ^ 3 * v * x ^ 4 + ℓ * m * p ^ 2 * q * s ^ 2 * t ^ 2 * u ^ 2 * v ^ 2 * x ^ 4 - p * t * x *
        y - p * u * x * y - p * q * s ^ 2 * t * u ^ 2 * v ^ 2 * x ^ 3 * y - p * s * t ^ 2 * u * v *
        x ^ 2 * y - p * s * t * u ^ 2 * v * x ^ 2 * y - p * s * t ^ 2 * u ^ 2 * v * x ^ 2 * y
        - p ^ 2 * s * t ^ 3 * u ^ 2 * v * x ^ 3 * y - p ^ 2 * s * t ^ 2 * u ^ 3 * v * x ^ 3 * y - p
        * q * s ^ 2 * t ^ 2 * u * v ^ 2 * x ^ 3 * y - p * t * u * x * y - p * q * s ^ 2 * t ^ 2 *
        u ^ 2 * v ^ 2 * x ^ 3 * y - m * p ^ 2 * q * s ^ 2 * t ^ 2 * u ^ 3 * v * x ^ 4 * y - ℓ *
        p ^ 2 * q * s ^ 2 * t ^ 2 * u ^ 2 * v ^ 2 * x ^ 4 * y - m * p ^ 2 * q * s ^ 2 * t ^ 2 *
        u ^ 2 * v ^ 2 * x ^ 4 * y - m * p ^ 2 * q * s ^ 2 * t ^ 3 * u ^ 2 * v ^ 2 * x ^ 4 * y - ℓ *
        p ^ 2 * q * s ^ 2 * t ^ 2 * u ^ 3 * v ^ 2 * x ^ 4 * y - ℓ * m * p ^ 3 * q * s ^ 2 * t ^ 3 *
        u ^ 3 * v ^ 2 * x ^ 5 * y + p ^ 2 * t * u * x ^ 2 * y ^ 2 + p ^ 2 * t ^ 2 * u * x ^ 2 *
        y ^ 2 + p ^ 2 * t * u ^ 2 * x ^ 2 * y ^ 2 + p ^ 2 * s * t ^ 2 * u ^ 2 * v * x ^ 3 * y ^ 2
        + p ^ 2 * s * t ^ 3 * u ^ 2 * v * x ^ 3 * y ^ 2 + p ^ 2 * s * t ^ 2 * u ^ 3 * v * x ^ 3 *
        y ^ 2 + p ^ 3 * s * t ^ 3 * u ^ 3 * v * x ^ 4 * y ^ 2 + p ^ 2 * q * s ^ 2 * t ^ 2 * u ^ 2 *
        v ^ 2 * x ^ 4 * y ^ 2 + p ^ 2 * q * s ^ 2 * t ^ 3 * u ^ 2 * v ^ 2 * x ^ 4 * y ^ 2 + p ^ 2 *
        q * s ^ 2 * t ^ 2 * u ^ 3 * v ^ 2 * x ^ 4 * y ^ 2 + ℓ * p ^ 3 * q * s ^ 2 * t ^ 3 * u ^ 3 *
        v ^ 2 * x ^ 5 * y ^ 2 + m * p ^ 3 * q * s ^ 2 * t ^ 3 * u ^ 3 * v ^ 2 * x ^ 5 * y ^ 2
        - p ^ 3 * t ^ 2 * u ^ 2 * x ^ 3 * y ^ 3 - p ^ 3 * s * t ^ 3 * u ^ 3 * v * x ^ 4 * y ^ 3
        - p ^ 3 * q * s ^ 2 * t ^ 3 * u ^ 3 * v ^ 2 * x ^ 5 * y ^ 3

/-- **Ten classical statistics over permutations avoiding $213$ and $231$.** Let $F$ be the
joint generating function of the ten classical statistics over the permutations avoiding both
patterns $213$ and $231$: a formal power series in $x$ over
$\mathbb{Q}[p, q, u, v, s, t, y, z, \ell, m]$ in which $x$ marks the length and
$p, q, u, v, s, t, y, z, \ell, m$ mark the numbers of ascents, descents, left-to-right maxima,
right-to-left maxima, left-to-right minima, right-to-left minima, double ascents, double
descents, peaks and valleys, respectively. Then
$(1 - ptuxy)(1 - qsvxz)\bigl((1 - ptxy)(1 - qvxz) - \ell mpqtvx^2\bigr)\, F$ equals
$$
svx\Bigl(qz(qvxz - 1) + p^2t^3u^2x^2y\bigl(\ell(m - 1)qvx - (y - 1)(qvxz - 1)\bigr) +
t\bigl(u(1 - qvxz)(1 + pqxyz) + pqxz(\ell mqvx + y - qvxyz)\bigr) -
pt^2ux\bigl(-\ell quvx - u(y - 1)(qvxz - 1) + (1 + pqxyz)(\ell mqvx + y - qvxyz)\bigr)\Bigr) -
qs^2tuv^2x^2\Bigl(mptx(ptuxy - 1)\bigl(1 + (\ell - 1)qvxz\bigr) -
(ptxy - 1)\bigl((1 - z)(qvxz - 1) +
ptux\bigl(z(1 + \ell qvx - qvxz) + y(z - 1)(qvxz - 1)\bigr)\bigr)\Bigr) +
(ptuxy - 1)\bigl(\ell mpqtvx^2 - (1 - ptxy)(1 - qvxz)\bigr).
$$

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Theorem 5
(`integers-2026-A18-thm-5`). -/
public theorem_wanted classicalStatGF_213_231 :
    let x : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.X
    let p : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let q : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    let u : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 2)
    let v : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 3)
    let s : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 4)
    let t : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 5)
    let y : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 6)
    let z : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 7)
    let ℓ : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 8)
    let m : PowerSeries (MvPolynomial (Fin 10) ℚ) := PowerSeries.C (MvPolynomial.X 9)
    ((1 - p * t * u * x * y) * (1 - q * s * v * x * z) * ((1 - p * t * x * y) * (1 - q * v * x * z)
        - ℓ * m * p * q * t * v * x ^ 2)) *
        classicalStatGF (pattern3 ![1, 0, 2]) (pattern3 ![1, 2, 0]) =
      s * v * x * (q * z * (q * v * x * z - 1) + p ^ 2 * t ^ 3 * u ^ 2 * x ^ 2 * y * (ℓ * (m - 1) *
        q * v * x - (y - 1) * (q * v * x * z - 1)) + t * (u * (1 - q * v * x * z) * (1 + p * q * x *
        y * z) + p * q * x * z * (ℓ * m * q * v * x + y - q * v * x * y * z)) - p * t ^ 2 * u * x *
        (-ℓ * q * u * v * x - u * (y - 1) * (q * v * x * z - 1) + (1 + p * q * x * y * z) * (ℓ * m *
        q * v * x + y - q * v * x * y * z))) - q * s ^ 2 * t * u * v ^ 2 * x ^ 2 * (m * p * t * x *
        (p * t * u * x * y - 1) * (1 + (ℓ - 1) * q * v * x * z) - (p * t * x * y - 1) * ((1 - z) *
        (q * v * x * z - 1) + p * t * u * x * (z * (1 + ℓ * q * v * x - q * v * x * z) + y * (z - 1)
        * (q * v * x * z - 1)))) + (p * t * u * x * y - 1) * (ℓ * m * p * q * t * v * x ^ 2 - (1 - p
        * t * x * y) * (1 - q * v * x * z))

/-- **Double ascents and double descents over permutations avoiding $231$ and $312$.** Let
$$H = \sum_{n \ge 0} \sum_{\sigma} x^n y^{\mathrm{dasc}(\sigma)} z^{\mathrm{ddes}(\sigma)},$$
where $\sigma$ runs over the permutations of $\{0, 1, \dots, n-1\}$ that avoid both patterns
$231$ and $312$, and $\mathrm{dasc}(\sigma)$ and $\mathrm{ddes}(\sigma)$ are the numbers of
double ascents and double descents of $\sigma$; $H$ is a formal power series in $x$ with
coefficients in $\mathbb{Q}[y, z]$. Then
$$(1 - x(y + z) - x^2(1 - yz))\, H = 1 + x^2(1 + x)(1 - y)(1 - z) + x(1 - y - z).$$

The source's Corollary 3 also gives an identity (22) for ascents and descents, marked by $p$
and $q$, and an identity (24) for peaks and valleys, marked by $\ell$ and $m$, over this class;
both are false as printed (at $p = 2$, $q = 1$ the coefficient of $x^5$ in (22) is $75$, the true
value $81$; at $\ell = 2$, $m = 1$ the coefficient of $x^5$ in (24) is $28$, the true value
$29$).

Source: Han, *Joint Distributions of 10 Classical Statistics over Permutations
Avoiding Two Patterns of Length 3*, INTEGERS 26 (2026), Article A18, Corollary 3
(`integers-2026-A18-cor-3`). -/
public theorem_wanted dascDdesGF_231_312 :
    let x : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.X
    let y : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 0)
    let z : PowerSeries (MvPolynomial (Fin 2) ℚ) := PowerSeries.C (MvPolynomial.X 1)
    (1 - x * (y + z) - x ^ 2 * (1 - y * z)) *
        dascDdesGF (pattern3 ![1, 2, 0]) (pattern3 ![2, 0, 1]) =
      1 + x ^ 2 * (1 + x) * (1 - y) * (1 - z) + x * (1 - y - z)

end

end MetaMathlibExt
