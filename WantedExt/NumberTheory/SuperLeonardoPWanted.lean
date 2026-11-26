/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Supergeneralized Leonardo `p`-numbers

Statements from Clemens Schütz and Kristian Kelly, *An Explicit Formula for
Supergeneralized Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025),
Article 25.8.2 (<https://cs.uwaterloo.ca/journals/JIS/VOL28/Schutz/schutz3.tex>).

The supergeneralized Leonardo `p`-numbers `𝓛_{p,k,x}` take the `p + 1` initial values
`x_0, …, x_p` freely and satisfy `𝓛(n) = 𝓛(n-1) + 𝓛(n-p-1) + k` for `n > p`; they are
`superLeonardoP`. With `x` constantly `1` they are the generalized Leonardo `p`-numbers
`MathlibExt.NumberTheory.LeonardoPWanted.leonardoPK`. The Fibonacci `p`-numbers are the
existing `MetaMathlibExt.fibonacciP`.

The paper's auxiliary vector `y` is printed as `(1, …, p)`, which has only `p` of the
`p + 1` entries a supergeneralized Leonardo `p`-sequence needs; the paper's table of
`q_{p+j}` (`q_{2p+1} = p + 1`) and Theorem 5 at `n = p` both force `y_p = p + 1`, so `y`
is read here as `(1, …, p + 1)`, i.e. `y_i = i + 1`.
-/
module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.Recurrences.SchutzKellyBinomialSum
public import MathlibExt.NumberTheory.Recurrences.SuperLeonardoPBinomial
public import MathlibExt.NumberTheory.Recurrences.SuperLeonardoPFibonacciSum

namespace MetaMathlibExt

@[expose] public section

/-- **Reduction of supergeneralized Leonardo p-numbers to the homogeneous case.** Let $p \ge 1$
and $k$ be natural numbers, $x$ a real sequence, $y$ the real sequence $y_i = i + 1$, and write
$\mathcal{L}_{p,k,x}(n)$ for the supergeneralized Leonardo $p$-numbers. For every natural number
$n$, $\mathcal{L}_{p,k,x}(n) = \mathcal{L}_{p,0,x}(n)$ if $n \le p$, and
$\mathcal{L}_{p,k,x}(n) = \mathcal{L}_{p,0,x}(n) + \mathcal{L}_{p,1,y}(n-(p+1)) \cdot k$ if $n > p$.

The paper writes the correction term as $\max\{0, \mathcal{L}_{p,1,y}(n-(p+1))\} \cdot k$ with
$y = (1, \dots, p + 1)$ and sets $\mathcal{L} \le 0$ at negative indices, so the correction term
is $0$ for $n \le p$; for $n > p$ the $\max$ is redundant since $\mathcal{L}_{p,1,y}$ is positive.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Theorem 3. -/
public theorem_wanted superLeonardoP_eq_add_mul (p k : ℕ) (hp : 1 ≤ p) (x : ℕ → ℝ) (n : ℕ) :
    superLeonardoP p k x n =
      superLeonardoP p 0 x n +
        (if p < n then superLeonardoP p 1 (fun i => (i : ℝ) + 1) (n - (p + 1)) else 0) *
          k

end

end MetaMathlibExt
