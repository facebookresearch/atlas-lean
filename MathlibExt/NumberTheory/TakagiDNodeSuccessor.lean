/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TakagiDyadicIdentities

/-!
# The successor formula for the divide-and-conquer D-node count

The successor formula is the Hamming-weight identity for consecutive D-node counts solved for
`dcDNodes (n + 1)`.

## References

* Laura Monroe, [*Takagi Function Identities on Dyadic Rationals*](https://cs.uwaterloo.ca/journals/JIS/VOL27/Monroe/monroe2.pdf),
  Journal of Integer Sequences 27 (2024), Article 24.2.7, pp. 1–14, Theorem 21 and Corollary 23.
* Tomás M. Coronado, Mareike Fischer, Lina Herbst, Francesc Rosselló, and Kristina Wicke,
  *On the minimum value of the Colless index and the bifurcating trees that achieve it*,
  Journal of Mathematical Biology 80 (2020), pp. 1993–2054, §3.1 (the underlying recurrence).
-/

namespace MetaMathlibExt

/-- **Successor formula for the divide-and-conquer D-node count.** Let $\delta$ be the
divide-and-conquer D-node count and $s_1(n)$ the number of ones in the binary expansion of $n$.
For every integer $n > 0$,
$\delta(n+1) = \delta(n) + \lfloor \log_2 n \rfloor - 2 s_1(n) + 2$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 21 (`jis-2024-24.2.7-thm-21`). -/
public theorem dcDNodes_succ (n : ℕ) (hn : 0 < n) :
    (dcDNodes (n + 1) : ℤ) = dcDNodes n + Nat.log 2 n - 2 * (Nat.digits 2 n).sum + 2 := by
  have h : (dcDNodes (n + 1) : ℚ) = dcDNodes n + Nat.log 2 n - 2 * (Nat.digits 2 n).sum + 2 := by
    linarith only [hammingWeight_eq_dcDNodes_diff n hn]
  exact_mod_cast h

end MetaMathlibExt
