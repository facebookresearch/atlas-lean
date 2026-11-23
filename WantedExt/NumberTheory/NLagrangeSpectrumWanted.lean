/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Order.LiminfLimsup

namespace MetaMathlibExt

@[expose] public section

open Filter Topology

/-- **$n$-Lagrange approximability.** For a natural number $n$ and a real number $\xi$, the
$n$-Lagrange approximability of $\xi$ is the element of the extended reals
$$\lambda_n(\xi) = \limsup_{s/t \to \xi} \frac{\gcd(t, n)}{t^2 \, |s/t - \xi|},$$
where the limsup is over rational numbers $s/t \ne \xi$, written in lowest terms with $t > 0$,
tending to $\xi$. For $n = 1$ this is the classical Lagrange approximability $\lambda(\xi)$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (3). -/
noncomputable def nLagrangeApproximability (n : ℕ) (ξ : ℝ) : EReal :=
  limsup (fun q : ℚ => (((Nat.gcd q.den n : ℝ) / ((q.den : ℝ) ^ 2 * |(q : ℝ) - ξ|) : ℝ) : EReal))
    (comap ((↑) : ℚ → ℝ) (𝓝[≠] ξ))

/-- **The $1$-Lagrange approximability is the classical one.** For every real number $\xi$, the
$1$-Lagrange approximability of $\xi$ is
$$\lambda_1(\xi) = \limsup_{s/t \to \xi} \frac{1}{t^2 \, |s/t - \xi|},$$
taken in the extended reals, where the limsup is over rational numbers $s/t \ne \xi$, written in
lowest terms with $t > 0$, tending to $\xi$. That is, the factor $\gcd(t, 1)$ in the definition
equals $1$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equations (1) and (3). -/
theorem nLagrangeApproximability_one (ξ : ℝ) :
    nLagrangeApproximability 1 ξ =
      limsup (fun q : ℚ => ((1 / ((q.den : ℝ) ^ 2 * |(q : ℝ) - ξ|) : ℝ) : EReal))
        (comap ((↑) : ℚ → ℝ) (𝓝[≠] ξ)) := by
  simp [nLagrangeApproximability]

/-- **$n$-Markoff approximability.** For a natural number $n$ and real numbers $\xi$ and $\xi'$, the
$n$-Markoff approximability is the supremum in the extended reals
$$\mu_n(\xi, \xi') = \sup_{(s,t) \ne 0} \frac{\gcd(t, n)\,|\xi - \xi'|}{|s - t\xi|\,|s - t\xi'|}$$
over all pairs of integers $(s, t) \ne (0, 0)$. A term whose denominator is $0$, which happens only
when $\xi$ or $\xi'$ is rational, counts as $0$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (4). -/
noncomputable def nMarkoffApproximability (n : ℕ) (ξ ξ' : ℝ) : EReal :=
  ⨆ st : {p : ℤ × ℤ // p ≠ 0},
    ((((Int.gcd st.1.2 n : ℝ) * |ξ - ξ'| /
      (|(st.1.1 : ℝ) - st.1.2 * ξ| * |(st.1.1 : ℝ) - st.1.2 * ξ'|) : ℝ)) : EReal)

/-- **Symmetry of the $n$-Markoff approximability.** For every natural number $n$ and all real
numbers $\xi$ and $\xi'$, the $n$-Markoff approximability satisfies
$\mu_n(\xi, \xi') = \mu_n(\xi', \xi)$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (4). -/
theorem nMarkoffApproximability_comm (n : ℕ) (ξ ξ' : ℝ) :
    nMarkoffApproximability n ξ ξ' = nMarkoffApproximability n ξ' ξ := by
  simp only [nMarkoffApproximability, abs_sub_comm ξ ξ', mul_comm |(_ : ℝ) - _ * ξ|]

/-- **$n$-Lagrange spectrum.** For a natural number $n$, the $n$-Lagrange spectrum $L_n$ is the set
of real numbers $\alpha$ such that $\lambda_n(\xi) = \alpha$ for some irrational real number
$\xi$, where $\lambda_n$ is the $n$-Lagrange approximability; only finite values of $\lambda_n$
count. For $n = 1$ this is the classical Lagrange spectrum $L$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (3). -/
def nLagrangeSpectrum (n : ℕ) : Set ℝ :=
  {α | ∃ ξ : ℝ, Irrational ξ ∧ nLagrangeApproximability n ξ = α}

/-- **Membership in the $n$-Lagrange spectrum.** For every natural number $n$ and real number
$\alpha$, $\alpha$ lies in the $n$-Lagrange spectrum $L_n$ if and only if $\alpha = \lambda_n(\xi)$
for some irrational real number $\xi$, where $\lambda_n$ is the $n$-Lagrange approximability.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (3). -/
theorem mem_nLagrangeSpectrum (n : ℕ) (α : ℝ) :
    α ∈ nLagrangeSpectrum n ↔ ∃ ξ : ℝ, Irrational ξ ∧ nLagrangeApproximability n ξ = α :=
  Iff.rfl

/-- **The $n$-Markoff spectrum.** For a natural number $n$ and irrational numbers $\xi \ne \xi'$,
the $n$-Markoff approximability $\mu_n(\xi, \xi')$ is the extended real number
$\sup_{(s, t) \in \mathbb{Z}^2 \setminus \{0\}}
\gcd(t, n) \, |\xi - \xi'| / (|s - t\xi| \, |s - t\xi'|)$. The $n$-Markoff spectrum $M_n$ is the
set of real numbers $\alpha$ such that $\mu_n(\xi, \xi') = \alpha$ for some irrational numbers
$\xi \ne \xi'$. For $n = 1$ this is the classical Markoff spectrum $M$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (4). -/
def nMarkoffSpectrum (n : ℕ) : Set ℝ :=
  {α | ∃ ξ ξ' : ℝ, Irrational ξ ∧ Irrational ξ' ∧ ξ ≠ ξ' ∧ nMarkoffApproximability n ξ ξ' = α}

/-- **Membership in the $n$-Markoff spectrum.** For every natural number $n$ and real number
$\alpha$, $\alpha$ lies in the $n$-Markoff spectrum $M_n$ if and only if $\alpha = \mu_n(\xi, \xi')$
for some distinct irrational real numbers $\xi$ and $\xi'$, where $\mu_n$ is the $n$-Markoff
approximability.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Introduction, equation (4). -/
theorem mem_nMarkoffSpectrum (n : ℕ) (α : ℝ) :
    α ∈ nMarkoffSpectrum n ↔
      ∃ ξ ξ' : ℝ, Irrational ξ ∧ Irrational ξ' ∧ ξ ≠ ξ' ∧ nMarkoffApproximability n ξ ξ' = α :=
  Iff.rfl

/-- **Convergents and the Lagrange approximability.** Let $\xi$ be an irrational real number,
with complete quotients $\xi_0 = \xi$ and $\xi_{k+1} = 1/\{\xi_k\}$, where $\{x\}$ is the
fractional part of $x$, and digits $a_k = \lfloor \xi_k \rfloor$, so that
$\xi = [a_0; a_1, a_2, \dots]$. For $k \ge 1$ let
$c_k = a_k + [0; a_{k-1}, \dots, a_1] + \{\xi_k\}$, where the middle term is $0$ when $k = 1$.
Then for every $k \ge 1$ the convergent $p/q = [a_0; a_1, \dots, a_{k-1}]$, written in lowest terms
with $q > 0$, satisfies $(-1)^k / (q^2 (p/q - \xi)) = c_k$. Moreover, the $1$-Lagrange
approximability $\lambda_1(\xi)$ equals $\limsup_{k \to \infty} c_k$, taken in the extended reals.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 4 (`integers-2025-A47-prop-4`), parts (a) and (c), quoted from Cusick and Flahive,
Appendix 1. -/
public theorem_wanted convergent_quality_and_lagrange_limsup (ξ : ℝ) (hξ : Irrational ξ) :
    let cq : ℕ → ℝ := fun k => (fun x : ℝ => (Int.fract x)⁻¹)^[k] ξ
    let a : ℕ → ℤ := fun k => ⌊cq k⌋
    let rev : ℕ → ℝ := fun k =>
      ((List.range (k - 1)).reverse.map (fun i => a (i + 1))).foldr
        (fun b acc => 1 / ((b : ℝ) + acc)) 0
    let cut : ℕ → ℝ := fun k => (a k : ℝ) + rev k + Int.fract (cq k)
    (∀ k : ℕ, 1 ≤ k →
        (-1 : ℝ) ^ k / (((ξ.convergent (k - 1)).den : ℝ) ^ 2 *
          ((ξ.convergent (k - 1) : ℝ) - ξ)) = cut k) ∧
      nLagrangeApproximability 1 ξ = limsup (fun k => ((cut k : ℝ) : EReal)) atTop

/-- **Real numbers with a common continued fraction prefix are close.** Let $\xi$ and $\xi'$ be
real numbers with continued fraction expansions $[a_0; a_1, a_2, \dots]$ and
$[a_0'; a_1', a_2', \dots]$, computed by $\xi_0 = \xi$, $a_i = \lfloor \xi_i \rfloor$ and
$\xi_{i+1} = 1/(\xi_i - a_i)$, stopping when $\xi_i = a_i$ (so an expansion is finite exactly when
the number is rational). Let $k \ge 0$ be an integer, and suppose that $a_0 = a_0'$ and that for
each $1 \le i \le k$ either both expansions have a digit of index $i$ and $a_i = a_i'$, or neither
has one. Then $|\xi - \xi'| \le 2^{1-k}$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Lemma 5 (`integers-2025-A47-lem-5`), quoted from Cusick and Flahive, Lemma 1. -/
public theorem_wanted abs_sub_le_of_contFrac_prefix_eq (ξ ξ' : ℝ) (k : ℕ)
    (h0 : (GenContFract.of ξ).h = (GenContFract.of ξ').h)
    (hk : ∀ i < k, (GenContFract.of ξ).partDens.get? i = (GenContFract.of ξ').partDens.get? i) :
    |ξ - ξ'| ≤ 2 ^ (1 - (k : ℤ))

/-- **The $n$-approximabilities as maxima over divisors.** Let $n \ge 1$, let $\lambda_n$ and
$\mu_n$ be the $n$-Lagrange and $n$-Markoff approximabilities, and let $\xi \ne \xi'$ be irrational
real numbers. Then $\lambda_n(\xi) = \max_{g \mid n} \lambda_1(g\xi)$ and
$\mu_n(\xi, \xi') = \max_{g \mid n} \mu_1(g\xi, g\xi')$, where $g$ runs over the positive divisors
of $n$ and the maxima are taken in the extended reals.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 6 (`integers-2025-A47-prop-6`). -/
public theorem_wanted nApproximability_eq_sup_divisors (n : ℕ) (hn : 1 ≤ n) (ξ ξ' : ℝ)
    (hξ : Irrational ξ) (hξ' : Irrational ξ') (hne : ξ ≠ ξ') :
    nLagrangeApproximability n ξ =
        n.divisors.sup (fun g => nLagrangeApproximability 1 (g * ξ)) ∧
      nMarkoffApproximability n ξ ξ' =
        n.divisors.sup (fun g => nMarkoffApproximability 1 (g * ξ) (g * ξ'))

/-- **Divisibility inclusions of the $n$-Lagrange and $n$-Markoff spectra.** Let $m$ and $n$
be natural numbers with $m \ge 1$, $n \ge 1$ and $m \mid n$, and write $L_k$ and $M_k$ for the
$k$-Lagrange and $k$-Markoff spectra. Then $L_n \subseteq L_m$ and $M_n \subseteq M_m$; in
particular $L_n \subseteq L_1$ and $M_n \subseteq M_1$, where $L_1$ and $M_1$ are the
classical Lagrange and Markoff spectra.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Corollary 7 (`integers-2025-A47-cor-7`), equations (8) and (9). -/
public theorem_wanted nSpectrum_subset_of_dvd (m n : ℕ) (hm : 1 ≤ m) (hmn : m ∣ n) (hn : 1 ≤ n) :
    (nLagrangeSpectrum n ⊆ nLagrangeSpectrum m ∧ nMarkoffSpectrum n ⊆ nMarkoffSpectrum m) ∧
      nLagrangeSpectrum n ⊆ nLagrangeSpectrum 1 ∧ nMarkoffSpectrum n ⊆ nMarkoffSpectrum 1

/-- **The $n$-Lagrange spectrum lies in the $n$-Markoff spectrum, with attained suprema.** Let
$n \ge 1$, let $L_n$ and $M_n$ be the $n$-Lagrange and $n$-Markoff spectra, and let $\mu_n$ be the
$n$-Markoff approximability. Then $L_n \subseteq M_n$. Moreover, for every $\alpha \in L_n$ there
are distinct irrational real numbers $\xi$ and $\xi'$ with $\mu_n(\xi, \xi') = \alpha$ at which the
supremum defining $\mu_n(\xi, \xi')$ is attained: some pair of integers $(s, t) \ne (0, 0)$
satisfies
$$\frac{\gcd(t, n)\,|\xi - \xi'|}{|s - t\xi|\,|s - t\xi'|} = \alpha.$$

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 9 (`integers-2025-A47-prop-9`). -/
public theorem_wanted nLagrangeSpectrum_subset_nMarkoffSpectrum_attained (n : ℕ) (hn : 1 ≤ n) :
    nLagrangeSpectrum n ⊆ nMarkoffSpectrum n ∧
      ∀ α ∈ nLagrangeSpectrum n, ∃ ξ ξ' : ℝ, Irrational ξ ∧ Irrational ξ' ∧ ξ ≠ ξ' ∧
        nMarkoffApproximability n ξ ξ' = α ∧
        ∃ s t : ℤ, (s, t) ≠ 0 ∧
          (((Int.gcd t n : ℝ) * |ξ - ξ'| / (|(s : ℝ) - t * ξ| * |(s : ℝ) - t * ξ'|) : ℝ) : EReal) = α

/-- **Attained suprema in the $n$-Markoff spectrum.** Let $n \ge 1$, let $M_n$ be the $n$-Markoff
spectrum, and let $\mu_n$ be the $n$-Markoff approximability. For every $\alpha \in M_n$ there are
distinct irrational real numbers $\xi$ and $\xi'$ with $\mu_n(\xi, \xi') = \alpha$ at which the
supremum defining $\mu_n(\xi, \xi')$ is attained: some pair of integers $(s, t) \ne (0, 0)$
satisfies
$$\frac{\gcd(t, n)\,|\xi - \xi'|}{|s - t\xi|\,|s - t\xi'|} = \alpha.$$

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 10 (`integers-2025-A47-prop-10`). -/
public theorem_wanted nMarkoffSpectrum_attained (n : ℕ) (hn : 1 ≤ n) :
    ∀ α ∈ nMarkoffSpectrum n, ∃ ξ ξ' : ℝ, Irrational ξ ∧ Irrational ξ' ∧ ξ ≠ ξ' ∧
      nMarkoffApproximability n ξ ξ' = α ∧
        ∃ s t : ℤ, (s, t) ≠ 0 ∧
          (((Int.gcd t n : ℝ) * |ξ - ξ'| / (|(s : ℝ) - t * ξ| * |(s : ℝ) - t * ξ'|) : ℝ) : EReal) = α

/-- **The $n$-Markoff spectrum is closed.** For every integer $n \ge 1$, the $n$-Markoff spectrum
$M_n$ is a closed subset of $\mathbb{R}$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 11 (`integers-2025-A47-prop-11`). -/
public theorem_wanted isClosed_nMarkoffSpectrum (n : ℕ) (hn : 1 ≤ n) :
    IsClosed (nMarkoffSpectrum n)

/-- **Common minimum of the $n$-Lagrange and $n$-Markoff spectra.** For every integer $n \ge 1$
there is a real number $\alpha$ that is the least element both of the $n$-Lagrange spectrum $L_n$
and of the $n$-Markoff spectrum $M_n$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 12 (`integers-2025-A47-prop-12`). -/
public theorem_wanted exists_isLeast_nLagrangeSpectrum_nMarkoffSpectrum (n : ℕ) (hn : 1 ≤ n) :
    ∃ α : ℝ, IsLeast (nLagrangeSpectrum n) α ∧ IsLeast (nMarkoffSpectrum n) α

/-- **Scaled classical spectra lie in the $n$-spectra.** Let $n \ge 1$ be a natural number and
write $L_k$ and $M_k$ for the $k$-Lagrange and $k$-Markoff spectra, so that $L_1$ and $M_1$
are the classical Lagrange and Markoff spectra. Then $n\alpha \in L_n$ for every
$\alpha \in L_1$ and $n\alpha \in M_n$ for every $\alpha \in M_1$; that is,
$n L_1 \subseteq L_n$ and $n M_1 \subseteq M_n$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 13 (`integers-2025-A47-prop-13`). -/
public theorem_wanted smul_spectrum_subset_nSpectrum (n : ℕ) (hn : 1 ≤ n) :
    (fun α => (n : ℝ) * α) '' nLagrangeSpectrum 1 ⊆ nLagrangeSpectrum n ∧
      (fun α => (n : ℝ) * α) '' nMarkoffSpectrum 1 ⊆ nMarkoffSpectrum n

/-- **Hall's ray in the $n$-Lagrange spectrum.** Let $L_1$ be the classical Lagrange spectrum and
let $F$ (Freĭman's constant) be the infimum of the real numbers $c$ with
$[c, \infty) \subseteq L_1$. Then for every integer $n \ge 1$,
$[nF, \infty) \subseteq L_n \subseteq M_n$, where $L_n$ is the $n$-Lagrange spectrum and
$M_n$ is the $n$-Markoff spectrum.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 14 (`integers-2025-A47-prop-14`). -/
public theorem_wanted hall_ray_nLagrangeSpectrum (n : ℕ) (hn : 1 ≤ n) :
    Set.Ici ((n : ℝ) * sInf {F : ℝ | Set.Ici F ⊆ nLagrangeSpectrum 1}) ⊆ nLagrangeSpectrum n ∧
      nLagrangeSpectrum n ⊆ nMarkoffSpectrum n

/-- **The $n$-Lagrange spectrum is closed.** For every integer $n \ge 1$, the $n$-Lagrange spectrum
$L_n$ is a closed subset of $\mathbb{R}$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 19 (`integers-2025-A47-prop-19`). -/
public theorem_wanted isClosed_nLagrangeSpectrum (n : ℕ) (hn : 1 ≤ n) :
    IsClosed (nLagrangeSpectrum n)

/-- **The $n$-Lagrange spectrum is the closure of its quadratic-irrational values.** Let $n \ge 1$,
let $\lambda_n$ be the $n$-Lagrange approximability, and let $P_n$ be the set of real numbers
$\alpha$ such that $\alpha = \lambda_n(\xi)$ for some quadratic irrational $\xi$, that is, an
irrational real number with $a\xi^2 + b\xi + c = 0$ for some integers $a \ne 0$, $b$, $c$. Then
the $n$-Lagrange spectrum $L_n$ is the closure of $P_n$ in $\mathbb{R}$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 20 (`integers-2025-A47-prop-20`). -/
public theorem_wanted nLagrangeSpectrum_eq_closure_quadratic (n : ℕ) (hn : 1 ≤ n) :
    nLagrangeSpectrum n = closure {α : ℝ | ∃ ξ : ℝ, Irrational ξ ∧
      (∃ a b c : ℤ, a ≠ 0 ∧ (a : ℝ) * ξ ^ 2 + b * ξ + c = 0) ∧
      nLagrangeApproximability n ξ = α}


/-- **Isolated minimum of the $p$-Lagrange spectrum for primes below 2000.** For every prime
$p < 2000$, the $p$-Lagrange spectrum $L_p$ has a least element $\alpha$ with the following
properties: $\alpha$ is an isolated point of $L_p$, that is, there is $\varepsilon > 0$ such that
every $\beta \in L_p$ with $|\beta - \alpha| < \varepsilon$ equals $\alpha$; $\alpha$ is
irrational; and $\alpha = \sqrt{r}$ for some rational number $r$.

This is Conjecture 1 of the source for primes below 2000.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Theorem 2 (`integers-2025-A47-thm-2`), with Conjecture 1. -/
public theorem_wanted min_nLagrangeSpectrum_isolated_sqrt_rat_of_prime_lt_2000 (p : ℕ)
    (hp : p.Prime) (hp2000 : p < 2000) :
    ∃ α : ℝ, IsLeast (nLagrangeSpectrum p) α ∧
      (∃ ε > 0, ∀ β ∈ nLagrangeSpectrum p, |β - α| < ε → β = α) ∧
      Irrational α ∧ ∃ r : ℚ, α = Real.sqrt r

/-- **The prime $67$ and continued fraction digits $1$ and $2$.** For an irrational real
number $\xi$, define its complete quotients by $\xi_0 = \xi$ and $\xi_{k+1} = 1/\{\xi_k\}$,
where $\{\cdot\}$ denotes the fractional part, and its continued fraction digits by
$a_k = \lfloor \xi_k \rfloor$. Let $p < 2000$ be a prime. Then there is no irrational $\xi$
such that the digits of both $\xi$ and $p\xi$ eventually all lie in $\{1, 2\}$ if and only
if $p = 67$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Theorem 3 (`integers-2025-A47-thm-3`). -/
public theorem_wanted no_eventually_one_two_contFrac_pair_iff_eq_67 (p : ℕ) (hp : p.Prime)
    (hp2000 : p < 2000) :
    (¬ ∃ ξ : ℝ, Irrational ξ ∧ ∀ᶠ k in atTop,
        ⌊(fun x : ℝ => (Int.fract x)⁻¹)^[k] ξ⌋ ∈ ({1, 2} : Set ℤ) ∧
          ⌊(fun x : ℝ => (Int.fract x)⁻¹)^[k] ((p : ℝ) * ξ)⌋ ∈ ({1, 2} : Set ℤ)) ↔
      p = 67

/-- **Markoff points in the $p$-Lagrange spectrum.** Let $x \le y \le z$ be positive integers with
$x^2 + y^2 + z^2 = 3xyz$ (a sorted Markoff triple), let $\lambda_z = \sqrt{9 - 4/z^2}$, let
$D = 9z^2 - 4$ if $z$ is odd and $D = (9z^2 - 4)/4$ if $z$ is even, and let $p$ be a prime.
Call $p$ a principal norm if $|u^2 + Duv + \frac{D^2 - D}{4} v^2| = p$ for some integers $u, v$,
that is, if some element $u + v \frac{D + \sqrt{D}}{2}$ of the quadratic order $\mathcal{O}_D$ has
norm $\pm p$. Then: (a) if $p$ is a principal norm, then $\lambda_z$ lies in the $p$-Lagrange
spectrum $L_p$; (b) if $\lambda_z \in L_p$ and, for every sorted Markoff triple
$(x', y', z') \ne (x, y, z)$ with $z' \le z$, the rational number $(9z^2 - 4)/(9z'^2 - 4)$ is not
a square in $\mathbb{Q}$, then $p$ is a principal norm.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Proposition 26 (`integers-2025-A47-prop-26`); the printed `λ_p ∈ L_p` is read as `λ_z ∈ L_p`, as in
the proof. -/
public theorem_wanted markoff_point_mem_nLagrangeSpectrum_iff_principal_norm (x y z p : ℕ)
    (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z) (hM : x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z)
    (hp : p.Prime) :
    let D : ℤ := if z % 2 = 1 then 9 * (z : ℤ) ^ 2 - 4 else (9 * (z : ℤ) ^ 2 - 4) / 4
    let principalNorm : Prop :=
      ∃ u v : ℤ, |u ^ 2 + D * u * v + (D ^ 2 - D) / 4 * v ^ 2| = (p : ℤ)
    (principalNorm → Real.sqrt (9 - 4 / (z : ℝ) ^ 2) ∈ nLagrangeSpectrum p) ∧
      (Real.sqrt (9 - 4 / (z : ℝ) ^ 2) ∈ nLagrangeSpectrum p →
        (∀ x' y' z' : ℕ, 0 < x' → x' ≤ y' → y' ≤ z' →
          x' ^ 2 + y' ^ 2 + z' ^ 2 = 3 * x' * y' * z' → z' ≤ z → (x', y', z') ≠ (x, y, z) →
          ¬ IsSquare ((9 * (z : ℚ) ^ 2 - 4) / (9 * (z' : ℚ) ^ 2 - 4))) →
        principalNorm)

/-- **Congruence conditions for Markoff points in the $p$-Lagrange spectrum.** Let $p$ be a prime
and let $L_p$ be the $p$-Lagrange spectrum. Then: (a) $\sqrt{5} \in L_p$ if and only if
$p \equiv 0, \pm 1 \pmod 5$; (b) $2\sqrt{2} \in L_p$ if and only if $p \equiv 2, \pm 1 \pmod 8$;
(c) $\sqrt{221}/5 \in L_p$ if and only if $p$ is a square modulo $13$ and modulo $17$;
(d) $\sqrt{1517}/13 \in L_p$ if and only if $p$ is a square modulo $37$ and modulo $41$;
(e) $\sqrt{7565}/29 \in L_p$ if and only if $p$ is a square modulo $5$, modulo $17$ and modulo
$89$. Here $p$ is a square modulo $m$ when $p \equiv a^2 \pmod m$ for some integer $a$; this
includes the case $p \equiv 0 \pmod m$.

Part (f) of the source, for $10\sqrt{26}/17$, is omitted: as printed it fails at $p = 17$.

Source: Brandon Dong, Soren Dupont, Evan M. O'Dorney and W. Theo Waitkus, *Raney Transducers and the
Lowest Point of the n-Lagrange Spectrum*, INTEGERS 25 (2025), Article A47,
Corollary 27 (`integers-2025-A47-cor-27`). -/
public theorem_wanted markoff_points_mem_nLagrangeSpectrum_iff (p : ℕ) (hp : p.Prime) :
    (Real.sqrt 5 ∈ nLagrangeSpectrum p ↔ p % 5 = 0 ∨ p % 5 = 1 ∨ p % 5 = 4) ∧
      (2 * Real.sqrt 2 ∈ nLagrangeSpectrum p ↔ p % 8 = 1 ∨ p % 8 = 2 ∨ p % 8 = 7) ∧
      (Real.sqrt 221 / 5 ∈ nLagrangeSpectrum p ↔
        IsSquare (p : ZMod 13) ∧ IsSquare (p : ZMod 17)) ∧
      (Real.sqrt 1517 / 13 ∈ nLagrangeSpectrum p ↔
        IsSquare (p : ZMod 37) ∧ IsSquare (p : ZMod 41)) ∧
      (Real.sqrt 7565 / 29 ∈ nLagrangeSpectrum p ↔
        IsSquare (p : ZMod 5) ∧ IsSquare (p : ZMod 17) ∧ IsSquare (p : ZMod 89))

end

end MetaMathlibExt
