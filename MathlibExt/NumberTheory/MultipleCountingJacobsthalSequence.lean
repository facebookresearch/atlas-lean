/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MetaMathlibExt

/-- **Multiple-counting Jacobsthal sequence.** For natural numbers $x$, $\rho$ and $n$, the
multiple-counting Jacobsthal sequence $J_{x,\rho}(n)$ is the number of multiples of $\rho$ strictly
between $x^n$ and $x^{n+1}$, that is, the number of natural numbers $k$ with $x^n < k < x^{n+1}$
and $\rho \mid k$.

The source studies $2 \le x$ and $2 \le \rho$; the count itself is useful without those
restrictions.

Source: concept `jis_sem_a69dabe897bb9ca4d746eba5`, statements `jis_590ab02a1ec2a505ee5b9b61`,
`jis_c5e526d097fecb5bdfc85583`.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL19/Cilasun/cila5.tex>. -/
def multipleCountingJacobsthalSequence (x rho n : ℕ) : ℕ :=
  ((Finset.Ioo (x ^ n) (x ^ (n + 1))).filter (fun k => rho ∣ k)).card

end MetaMathlibExt
