/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Order.Filter.AtTopBot.Basic

namespace MetaMathlibExt

@[expose] public section

open Filter


/-- **Truncated logarithm.** For a real number $x$, the truncated logarithm is
$\operatorname{Log} x = \max(\log x, 1)$. Here $\log$ is extended to all reals by $\log 0 = 0$
and $\log x = \log |x|$ for $x < 0$, so the definition is total; the paper uses it only for
$x > 0$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def truncLog (x : ℝ) : ℝ :=
  max (Real.log x) 1

/-- **Second iterated truncated logarithm.** For a real number $x$, the second iterated truncated
logarithm is $\operatorname{Log}_2 x = \operatorname{Log}(\operatorname{Log} x)$, where
$\operatorname{Log}$ is the truncated logarithm.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def truncLog2 (x : ℝ) : ℝ :=
  truncLog (truncLog x)

/-- **Third iterated truncated logarithm.** For real $x$, let
$\operatorname{Log} x = \max(\log x, 1)$ be the truncated logarithm, where $\log$ is the natural
logarithm extended by $\log x = \log |x|$ for $x < 0$ and $\log 0 = 0$, and let
$\operatorname{Log}_2 x = \operatorname{Log}(\operatorname{Log} x)$. The third iterated truncated
logarithm is the function on all of $\mathbb{R}$ given by
$\operatorname{Log}_3 x = \operatorname{Log}(\operatorname{Log}_2 x)$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def truncLog3 (x : ℝ) : ℝ :=
  truncLog (truncLog2 x)

/-- **The truncated logarithm is at least one.** For every real number $x$, the truncated
logarithm $\operatorname{Log} x = \max(\log x, 1)$ satisfies $\operatorname{Log} x \ge 1$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public theorem one_le_truncLog (x : ℝ) : 1 ≤ truncLog x := by
  exact le_max_right _ _

/-- **Elements of a set up to a bound.** For a set $A$ of natural numbers and a real number $x$,
this is the finite set of positive integers $n \in A$ with $n \le x$; it is empty when $x < 1$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def naturalsInSetUpTo (A : Set ℕ) (x : ℝ) : Finset ℕ :=
  open Classical in (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n ∈ A)

/-- **The empty set has no elements up to any bound.** For every real number $x$, the finite set
of elements $n$ of the empty set with $1 \le n \le x$ is empty.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
@[simp] public theorem naturalsInSetUpTo_empty (x : ℝ) :
    naturalsInSetUpTo ∅ x = ∅ := by
  simp [naturalsInSetUpTo]

/-- **Harmonic sum of a set up to a bound.** For a set $A$ of natural numbers and a real number
$x$, this is the finite sum $\sum_{n \in A,\, 1 \le n \le x} 1/n$ of the reciprocals of the
positive integers in $A$ that are at most $x$; it is $0$ when $x < 1$.

The sum starts at $n = 1$, matching the paper's convention that natural numbers are positive.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
public noncomputable def recipSumUpTo (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ naturalsInSetUpTo A x, 1 / (n : ℝ)

/-- **The harmonic sum over the empty set vanishes.** For every real number $x$,
$\sum_{n \in \emptyset,\, n \le x} 1/n = 0$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Notation.
-/
@[simp] public theorem recipSumUpTo_empty (x : ℝ) : recipSumUpTo ∅ x = 0 := by
  simp [recipSumUpTo]

/-- **Double sum of reciprocal least common multiples.** For a set $A$ of natural numbers and a
real number $x$, the double sum of reciprocal least common multiples of $A$ up to $x$ is the
real number $\sum 1/\operatorname{lcm}(n, m)$, summed over all ordered pairs $(n, m)$ with
$n, m \in A$, $1 \le n \le x$ and $1 \le m \le x$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (12).
-/
public noncomputable def lcmReciprocalSum (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ naturalsInSetUpTo A x,
    ∑ m ∈ naturalsInSetUpTo A x, 1 / (Nat.lcm n m : ℝ)

/-- **Double reciprocal lcm sum of the empty set.** For every real number $x$, the double sum of
reciprocal least common multiples of the empty set up to $x$ is $0$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (12).
-/
@[simp] public theorem lcmReciprocalSum_empty (x : ℝ) : lcmReciprocalSum ∅ x = 0 := by
  simp [lcmReciprocalSum]

/-- **Logarithmic gcd moment.** For a set $A$ of natural numbers and a real number $x$, the
logarithmic gcd moment of $A$ up to $x$ is the sum of $\gcd(n, m)/(nm)$ over all ordered pairs
$(n, m)$ with $n, m \in A$, $1 \le n \le x$ and $1 \le m \le x$.

When $A \cap [1, x]$ is nonempty, dividing by $\big(\sum_{n \in A,\ 1 \le n \le x} 1/n\big)^2$
gives the expected value of $\gcd(n, m)$ for $n$ and $m$ drawn independently from $A \cap [1, x]$,
each with probability proportional to $1/n$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (9).
-/
public noncomputable def gcdLogarithmicMoment (A : Set ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ naturalsInSetUpTo A x,
    ∑ m ∈ naturalsInSetUpTo A x,
      (Nat.gcd n m : ℝ) / ((n : ℝ) * (m : ℝ))

/-- **Gcd defect.** For a set $A$ of natural numbers and a real number $x$, let
$S_A(x) = \sum_{n \in A,\ 1 \le n \le x} 1/n$ be the harmonic sum of $A$ up to $x$, and let
$G_A(x)$ be the sum of $\gcd(n, m)/(nm)$ over all ordered pairs $(n, m)$ with $n, m \in A$,
$1 \le n \le x$ and $1 \le m \le x$. The gcd defect of $A$ up to $x$ is
$\mathcal{E}_A(x) = G_A(x)/S_A(x)^2 - 1$, where division by $0$ gives $0$; in particular
$\mathcal{E}_A(x) = -1$ when $A$ has no element in $[1, x]$.

When $A$ has an element in $[1, x]$, $\mathcal{E}_A(x) + 1$ is the expected value of
$\gcd(n, m)$ for $n$ and $m$ drawn independently from $A \cap [1, x]$, each with probability
proportional to $1/n$, so $\mathcal{E}_A(x)$ is the quantity $\mathbb{E} \gcd(n, m) - 1$ of the
source.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (9).
-/
public noncomputable def lcmDefect (A : Set ℕ) (x : ℝ) : ℝ :=
  gcdLogarithmicMoment A x / recipSumUpTo A x ^ 2 - 1

/-- **The gcd defect of the empty set.** For every real number $x$, the gcd defect of the empty
set up to $x$ equals $-1$.

The harmonic sum of the empty set is $0$, and division by $0$ gives $0$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equation (9).
-/
@[simp] public theorem lcmDefect_empty (x : ℝ) : lcmDefect ∅ x = -1 := by
  simp [lcmDefect, gcdLogarithmicMoment]

/-- **Products of a fixed number of distinct primes.** For a set $\mathcal{P}$ of natural numbers
and $k \in \mathbb{N}$, $\mathcal{P}^{[k]}$ is the set of squarefree natural numbers $n$ whose prime
divisors all lie in $\mathcal{P}$ and which have exactly $k$ distinct prime divisors; that is, the
products of exactly $k$ distinct primes from $\mathcal{P}$. In particular,
$\mathcal{P}^{[0]} = \{1\}$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1 notation.
-/
public noncomputable def primeProductLayer (P : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | Squarefree n ∧
    (∀ p, p.Prime → p ∣ n → p ∈ P) ∧
    n.primeFactors.card = k}

/-- **Products of at most a fixed number of distinct primes.** For a set $\mathcal{P}$ of natural
numbers and $k \in \mathbb{N}$, $\mathcal{P}^{[\le k]}$ is the set of natural numbers that lie in
$\mathcal{P}^{[j]}$ for some $j \le k$, where $\mathcal{P}^{[j]}$ is the set of products of exactly
$j$ distinct primes from $\mathcal{P}$; that is,
$\mathcal{P}^{[\le k]} = \bigcup_{j \le k} \mathcal{P}^{[j]}$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1 notation.
-/
public noncomputable def primeProductsAtMost (P : Set ℕ) (k : ℕ) : Set ℕ :=
  {n | ∃ j ≤ k, n ∈ primeProductLayer P j}

/-- **At most zero primes means exactly zero primes.** For every set $\mathcal{P}$ of natural
numbers, $\mathcal{P}^{[\le 0]} = \mathcal{P}^{[0]}$, where $\mathcal{P}^{[\le k]}$ and
$\mathcal{P}^{[k]}$ are the products of at most, respectively exactly, $k$ distinct primes from
$\mathcal{P}$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1 notation.
-/
public theorem primeProductsAtMost_zero (P : Set ℕ) :
    primeProductsAtMost P 0 = primeProductLayer P 0 := by
  ext n
  simp [primeProductsAtMost]

/-- **Growth function of the dense-set construction.** Let $\operatorname{Log}_2$ be the second
iterated truncated logarithm. For real numbers $C_0$ and $x$, let $k$ be the natural number
$\max(\lceil C_0 \sqrt{\operatorname{Log}_2 x}\,\rceil - 1, 0)$, and set
$h = \operatorname{Log}_2 x - k^2/C_0^2 + 1$, $x' = \exp(\exp((k + 1)^2/C_0^2))$,
$h' = \operatorname{Log}_2 x' - k^2/C_0^2 + 1$ and $\psi = 1 + h^2/h'$. The growth function at
$(C_0, x)$ is $F_{C_0}(x) = \psi\, k^{2k} / (C_0^{2k}\, k!)$. Here division by $0$ gives $0$ and
$0^0 = 1$.

In the source, $h'$ is the value at $x_{k+1} = x'$ of the expression defining $h$, with $k$ kept
fixed, and $F_{C_0}(x)$ is written $\psi(x)\, k^{2k} C_0^{-2k}/k!$; the function is used only for
$C_0 > 0$ and sufficiently large $x$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Equations (13)--(15).
-/
public noncomputable def lcmDenseGrowthF (C₀ x : ℝ) : ℝ :=
  let k : ℕ := Nat.ceil (C₀ * Real.sqrt (truncLog2 x)) - 1
  let h : ℝ := truncLog2 x - (k : ℝ) ^ 2 / C₀ ^ 2 + 1
  let xNext : ℝ := Real.exp (Real.exp (((k + 1 : ℕ) : ℝ) ^ 2 / C₀ ^ 2))
  let hNext : ℝ := truncLog2 xNext - (k : ℝ) ^ 2 / C₀ ^ 2 + 1
  let ψ : ℝ := 1 + h ^ 2 / hNext
  ψ * (k : ℝ) ^ (2 * k) / C₀ ^ (2 * k) / (k.factorial : ℝ)

/-- **Harmonic sums over products of distinct primes.** There are constants $c > 0$ and $C > 0$
such that the following holds. Let $\mathcal{P}$ be a set of primes, let $k$ be a natural number,
let $x \ge 1$ be real, and put $S = \sum_{p \in \mathcal{P},\, p \le x} 1/p$,
$T_k = \sum_{n \in \mathcal{P}^{[k]},\, n \le x} 1/n$ and
$T_{\le k} = \sum_{n \in \mathcal{P}^{[\le k]},\, n \le x} 1/n$, where $\mathcal{P}^{[k]}$ and
$\mathcal{P}^{[\le k]}$ are the sets of products of exactly $k$, respectively at most $k$,
distinct primes from $\mathcal{P}$. If $k \le cS$, then
$S^k/(C\,k!) \le T_k \le C\,S^k/k!$ and $S^k/(C\,k!) \le T_{\le k} \le C\,S^k/k!$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Lemma 1.
-/
public theorem_wanted recipSum_primeProductLayer_asymp :
    ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
    ∀ (P : Set ℕ) (k : ℕ) (x : ℝ),
      (∀ p ∈ P, p.Prime) →
      1 ≤ x →
      let S := recipSumUpTo P x
      let Tk := recipSumUpTo (primeProductLayer P k) x
      let Tle := recipSumUpTo (primeProductsAtMost P k) x
      (k : ℝ) ≤ c * S →
        (S ^ k / (k.factorial : ℝ)) / C ≤ Tk ∧
        Tk ≤ C * (S ^ k / (k.factorial : ℝ)) ∧
        (S ^ k / (k.factorial : ℝ)) / C ≤ Tle ∧
        Tle ≤ C * (S ^ k / (k.factorial : ℝ))

/-- **Dense sets with unusually large least common multiples.** Let $\operatorname{Log}_2$ and
$\operatorname{Log}_3$ be the second and third iterated truncated logarithms. For a set $A$ of
natural numbers and real $x$, write $S_A(x) = \sum_{n \in A,\ 1 \le n \le x} 1/n$, and write
$L_A(x)$ for the sum of $1/\operatorname{lcm}(n, m)$ over all ordered pairs $(n, m)$ with
$n, m \in A$, $1 \le n \le x$ and $1 \le m \le x$. Then for every real $C_0 > 0$ there is a set
$A$ of natural numbers with the following two properties. First, there is a function
$\varepsilon : \mathbb{R} \to \mathbb{R}$ with $\varepsilon(x) \to 0$ as $x \to \infty$ such that
for all sufficiently large real $x$,
$S_A(x) = \exp((C_0/2 + \varepsilon(x))(\operatorname{Log}_2 x)^{1/2} \operatorname{Log}_3 x)$.
Second, there is a constant $K > 0$ such that $L_A(x) \le K\, S_A(x)^2$ for all sufficiently
large real $x$.

The source presents this as a negative answer to Erdős problem #442. Its accompanying claim that
the exponent is optimal is made precise by Theorem 2(ii) and is stated separately.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Theorem 1.
-/
public theorem_wanted exists_dense_set_large_lcm :
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ A : Set ℕ,
        (∃ e : ℝ → ℝ,
          Tendsto e atTop (nhds 0) ∧
          ∀ᶠ x in atTop,
            recipSumUpTo A x =
              Real.exp ((C₀ / 2 + e x) *
                truncLog2 x ^ (1 / 2 : ℝ) * truncLog3 x)) ∧
        ∃ K : ℝ, 0 < K ∧
          ∀ᶠ x in atTop,
            lcmReciprocalSum A x ≤ K * recipSumUpTo A x ^ 2

/-- **Dense sets with controlled gcd defect.** Let $e$ be Euler's number. There is an absolute
constant $C > 0$ with the following property. Let $C_0 > 0$ be real, and let $F_{C_0}$ be the
growth function of the dense-set construction. Then there is a set $A$ of natural numbers such
that, writing $S_A(x) = \sum_{n \in A,\ 1 \le n \le x} 1/n$ for its harmonic sum up to $x$ and
$\mathcal{E}_A(x)$ for its gcd defect up to $x$, the following two statements hold. First, there
is a constant $K > 0$ with $F_{C_0}(x)/K \le S_A(x) \le K\, F_{C_0}(x)$ for all sufficiently large
real $x$. Second, there is a function $\varepsilon : \mathbb{R} \to \mathbb{R}$ with
$\varepsilon(x) \to 0$ as $x \to \infty$ such that
$\mathcal{E}_A(x) \le C\,(\exp(e^2 C_0^2) - 1 + \varepsilon(x))$ for all sufficiently large
real $x$.

The factor $e^2$ follows the journal version of the source; the arXiv preprint prints
$\exp(C_0^2)$, but its proof, through the factor $e^\ell$ of (35), gives $e^2 C_0^2$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Theorem 2(i).
-/
public theorem_wanted exists_dense_set_controlled_defect :
    ∃ C : ℝ, 0 < C ∧
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ A : Set ℕ,
        (∃ K : ℝ, 0 < K ∧
          ∀ᶠ x in atTop,
            lcmDenseGrowthF C₀ x / K ≤ recipSumUpTo A x ∧
            recipSumUpTo A x ≤ K * lcmDenseGrowthF C₀ x) ∧
        ∃ e : ℝ → ℝ,
          Tendsto e atTop (nhds 0) ∧
          ∀ᶠ x in atTop,
            lcmDefect A x ≤ C * (Real.exp (Real.exp 2 * C₀ ^ 2) - 1 + e x)

/-- **Baby version of the dense-set construction.** Let $e$ be Euler's number, let
$\operatorname{Log}_2$ and $\operatorname{Log}_3$ be the second and third iterated truncated
logarithms, and for a set $B$ of natural numbers and real $x$ write
$S_B(x) = \sum_{n \in B,\ 1 \le n \le x} 1/n$ and $\mathcal{E}_B(x)$ for the gcd defect of $B$ up
to $x$. There is an absolute constant $C > 0$ such that for every real $C_0 > 0$ there are sets
$A_0, A_1, A_2, \dots$ of natural numbers with the following property: for every $\varepsilon > 0$
there are a real $\delta > 0$ and a natural number $k_0$ such that for every natural number
$k \ge k_0$ and every real $x$ with $|C_0 (\operatorname{Log}_2 x)^{1/2} - k| \le \delta k$, there
is a real $\eta$ with $|\eta| \le \varepsilon$ and
$S_{A_k}(x) = \exp((C_0/2 + \eta)(\operatorname{Log}_2 x)^{1/2} \operatorname{Log}_3 x)$, and
moreover $\mathcal{E}_{A_k}(x) \le C(\exp(e^2 C_0^2) - 1 + \varepsilon)$.

In the source this is Proposition 1, a simplified version of the construction for Theorem 2(i)
(its lead-in sentence refers to Theorem 2(ii)): the sets $A_k$ satisfy (31) and the bound (21)
in the range (32), with all $o(1)$ terms taken as $k \to \infty$. Above, these $o(1)$ terms are
written with $\varepsilon$, $\delta$ and $k_0$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Proposition 1, (31) and (32), with (21)
(`integers-2024-A100-prop-1`).
-/
public theorem_wanted exists_dense_sets_baby :
    ∃ C : ℝ, 0 < C ∧
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ A : ℕ → Set ℕ,
        ∀ ε : ℝ, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x : ℝ,
            |C₀ * truncLog2 x ^ (1 / 2 : ℝ) - k| ≤ δ * k →
              (∃ e : ℝ, |e| ≤ ε ∧
                recipSumUpTo (A k) x =
                  Real.exp ((C₀ / 2 + e) * truncLog2 x ^ (1 / 2 : ℝ) * truncLog3 x)) ∧
              lcmDefect (A k) x ≤ C * (Real.exp (Real.exp 2 * C₀ ^ 2) - 1 + ε)

/-- **Harmonic sums of sets with small gcd defect.** For a set $A$ of natural numbers and a real
number $x$, let $S_A(x)$ be the sum of $1/n$ over $n \in A$ with $1 \le n \le x$, and let the
defect of $A$ at $x$ be the sum of $\gcd(n, m)/(nm)$ over $n, m \in A$ with $1 \le n, m \le x$,
divided by $S_A(x)^2$, minus $1$ (the defect is $-1$ when $S_A(x) = 0$). Let
$\operatorname{Log} x = \max(\log x, 1)$ be the truncated logarithm, let
$\operatorname{Log}_2 x = \operatorname{Log}(\operatorname{Log} x)$ and let
$\operatorname{Log}_3 x = \operatorname{Log}(\operatorname{Log}_2 x)$. For every real
$C_0 > 0$ there are a function $e : \mathbb{R} \to \mathbb{R}$ with $e(x) \to 0$ as
$x \to \infty$ and a real $x_0$ such that for every real $x \ge x_0$ and every set $A$ of natural
numbers whose defect at $x$ is at most $C_0^2$,
$$S_A(x) \le \exp\bigl((C_0 + e(x)) (\operatorname{Log}_2 x)^{1/2} \operatorname{Log}_3 x\bigr).$$

The function $e$ and the threshold $x_0$ are chosen before $x$ and $A$, so the $o(1)$ error is
uniform in $A$.

Source: Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*,
INTEGERS 24 (2024), Article A100, Theorem 2(ii).
-/
public theorem_wanted uniform_harmonic_bound_of_defect :
    ∀ C₀ : ℝ, 0 < C₀ →
      ∃ e : ℝ → ℝ,
        Tendsto e atTop (nhds 0) ∧
        ∀ᶠ x in atTop,
          ∀ A : Set ℕ,
            lcmDefect A x ≤ C₀ ^ 2 →
            recipSumUpTo A x ≤
              Real.exp ((C₀ + e x) *
                truncLog2 x ^ (1 / 2 : ℝ) * truncLog3 x)

end

end MetaMathlibExt
