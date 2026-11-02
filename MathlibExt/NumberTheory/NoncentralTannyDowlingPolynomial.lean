/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic

namespace MetaMathlibExt

@[expose] public section

variable {R : Type*} [CommRing R]

/-- **Noncentral Whitney numbers of the second kind.** For elements $m$ and $a$ of a commutative
ring $R$, the noncentral Whitney numbers of the second kind $W_{m,a}(n, k) \in R$, for natural
numbers $n$ and $k$, are defined by $W_{m,a}(0, 0) = 1$, $W_{m,a}(0, k) = 0$ for $k \ge 1$,
$W_{m,a}(n + 1, 0) = (-a)^{n+1}$, and
$$W_{m,a}(n + 1, k + 1) = W_{m,a}(n, k) + ((k + 1) m - a) \, W_{m,a}(n, k + 1).$$

Source: concept `jis_term_6c385244500b53dde9d3f070`, source
`https://cs.uwaterloo.ca/journals/JIS/VOL24/Mangontarum/mang13.tex`, SHA-256
`e08f5454236c4aeb678d73ad15de5b19ce88cfbffc855ad2a25e45309b533cc5`, recurrence
underlying the Tanny-Dowling polynomial in equation (6). -/
public def noncentralWhitneySecond (m a : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => (-a) ^ (n + 1)
  | n + 1, k + 1 =>
    noncentralWhitneySecond m a n k +
      (m * ((k + 1 : ℕ) : R) - a) * noncentralWhitneySecond m a n (k + 1)

/-- **Noncentral Tanny–Dowling polynomials.** For elements $m$ and $a$ of a commutative ring $R$
and a natural number $n$, the noncentral Tanny–Dowling polynomial $D_{m,a,n}(x) \in R[x]$ is
$$D_{m,a,n}(x) = \sum_{k=0}^{n} k! \, W_{m,a}(n, k) \, x^k,$$
where $W_{m,a}(n, k)$ are the noncentral Whitney numbers of the second kind.

Source: equation (6), concept `jis_term_6c385244500b53dde9d3f070`, source
`https://cs.uwaterloo.ca/journals/JIS/VOL24/Mangontarum/mang13.tex`, SHA-256
`e08f5454236c4aeb678d73ad15de5b19ce88cfbffc855ad2a25e45309b533cc5`. -/
public noncomputable def noncentralTannyDowlingPolynomial (m a : R) (n : ℕ) : Polynomial R :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    Polynomial.C (((Nat.factorial k : ℕ) : R) * noncentralWhitneySecond m a n k) *
      Polynomial.X ^ k

end

end MetaMathlibExt
