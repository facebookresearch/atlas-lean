/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem #690: unimodality of the k-th prime-factor density

For fixed `k ≥ 1`, is `dₖ(p)` (the density of integers whose `k`-th
smallest prime factor is `p`) unimodal in the prime `p`?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.PrimeFin
public import MathlibExt.Data.Set.Density
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem690Wanted

/-- **The $k$-th smallest prime factor.** For natural numbers $k$, $n$ and $p$, $p$ is the $k$-th
smallest prime factor of $n$ when $n \ne 0$, $p$ is a prime dividing $n$, and exactly $k - 1$
primes dividing $n$ are smaller than $p$.

For $k = 0$ the count $k - 1$ is read as $0$ (truncated subtraction), so $k = 0$ and $k = 1$
agree. -/
def IsKthSmallestPrimeFactor (k n p : ℕ) : Prop :=
  p ∈ Nat.primeFactors n ∧
    ((Nat.primeFactors n).filter (fun q => q < p)).card = k - 1

/-- **The $k$-th prime-factor density.** For natural numbers $k$ and $p$, let $S_{k,p}$ be the set
of natural numbers whose $k$-th smallest prime factor is $p$. The $k$-th prime-factor density
$d_k(p)$ is the natural density of $S_{k,p}$, that is, the limit of
$\lvert S_{k,p} \cap \{0, 1, \dots, N - 1\} \rvert / N$ as $N \to \infty$, when this limit
exists; otherwise $d_k(p)$ is an unspecified real number. -/
noncomputable def kthPrimeFactorDensity (k p : ℕ) : ℝ :=
  Classical.epsilon (fun d : ℝ =>
    Set.HasDensity {n : ℕ | IsKthSmallestPrimeFactor k n p} d)

/-- **Unimodality on the primes.** A function $f \colon \mathbb{N} \to \mathbb{R}$ is unimodal on
the primes if there is a prime $p_0$ such that $f(p) \le f(q)$ for all primes $p$ and $q$ with
$p \le q \le p_0$, and $f(q) \le f(p)$ for all primes $p$ and $q$ with $p_0 \le p \le q$. -/
def IsUnimodalOnPrimes (f : ℕ → ℝ) : Prop :=
  ∃ p₀ : ℕ, p₀.Prime ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p ≤ q → q ≤ p₀ → f p ≤ f q) ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p₀ ≤ p → p ≤ q → f q ≤ f p)

/-- **Erdős Problem 690.** The proposition that for every natural number $k \ge 1$ the $k$-th
prime-factor density $d_k$ is unimodal on the primes: there is a prime $p_0$ such that
$d_k(p) \le d_k(q)$ for all primes $p$ and $q$ with $p \le q \le p_0$, and $d_k(q) \le d_k(p)$ for
all primes $p$ and $q$ with $p_0 \le p \le q$. Here $d_k(p)$ is the natural density of the set of
natural numbers whose $k$-th smallest prime factor is $p$ (an unspecified real number if this
density does not exist). -/
def conjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → IsUnimodalOnPrimes (kthPrimeFactorDensity k)

/--
**Erdős Problem 690 is false.** There is a natural number $k \ge 1$ such that the $k$-th
prime-factor density $d_k$ is not unimodal on the primes, that is, there is no prime $p_0$ such
that $d_k(p) \le d_k(q)$ for all primes $p$ and $q$ with $p \le q \le p_0$ and
$d_k(q) \le d_k(p)$ for all primes $p$ and $q$ with $p_0 \le p \le q$. Here $d_k(p)$ is the
natural density of the set of natural numbers whose $k$-th smallest prime factor is $p$ (an
unspecified real number if this density does not exist).

Cambie (Theorem 5) proves that $d_k$ is unimodal for $k = 1, 2, 3$ and not unimodal for
$4 \le k \le 20$; for example $d_4(13) = 31/5005 > d_4(17) = 206/36465 < d_4(19) = 1308/230945$.

Source: S. Cambie, Resolution of Erdős' problems
about unimodularity, arXiv preprint (2025), arXiv:2501.10333, https://arxiv.org/abs/2501.10333.
Moved from `OpenConjectures/NumberTheory/ErdosProblem690`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosProblem690Wanted
