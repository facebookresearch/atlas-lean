/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Polynomial.Pochhammer

namespace MetaMathlibExt

@[expose] public section

/-- **Unsigned Charlier polynomials of order 0.** For a semiring $R$ and a natural number $n$,
the $n$-th unsigned Charlier polynomial of order $0$ is
$$\sum_{k=0}^{n} \binom{n}{k}\, x^{\overline{k}} \in R[x],$$
where $x^{\overline{k}} = x(x+1)\cdots(x+k-1)$ is the rising factorial polynomial.

It is the terminating hypergeometric series ${}_2F_0(-n, x; ; -1)$, an unsigned version of the
Charlier polynomials of order 0, and its coefficient array is the exponential Riordan array
$[e^x, \ln(1/(1-x))]$.

Source: concept `jis_sem_533e904c33481f2f38f4d596`; sources `jis_5d9eb8b198dc383014683c4a`,
`jis_f192adf11c41568a1a8f6394`, `jis_9ce0e70844069456decf11dd`, `jis_540a5d48a1eb53d00b45a269`. -/
noncomputable def unsignedCharlierOrder0 (R : Type*) [Semiring R] (n : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k) • ascPochhammer R k

/-- **Unsigned Charlier coefficient.** For natural numbers $n$ and $m$, the unsigned Charlier
coefficient is the natural number
$$c(n, m) = \sum_{k=0}^{n} \binom{n}{k}\, [x^m]\, x^{\overline{k}},$$
where $x^{\overline{k}} = x(x+1)\cdots(x+k-1)$ is the rising factorial polynomial over
$\mathbb{N}$ and $[x^m]$ denotes the coefficient of $x^m$. -/
noncomputable def unsignedCharlierCoeff (n m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k) * (ascPochhammer ℕ k).coeff m

/-- **Coefficients of the unsigned Charlier polynomials.** For all natural numbers $n$ and $m$,
the coefficient of $x^m$ in the $n$-th unsigned Charlier polynomial of order $0$ over $\mathbb{N}$
equals the unsigned Charlier coefficient $c(n, m)$. -/
theorem unsignedCharlier_coeff_eq (n m : ℕ) :
    (unsignedCharlierOrder0 ℕ n).coeff m = unsignedCharlierCoeff n m := by
  simp [unsignedCharlierOrder0, unsignedCharlierCoeff]

end

end MetaMathlibExt
