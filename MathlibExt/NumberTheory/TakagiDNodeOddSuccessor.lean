/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TakagiDNodeSuccessor

/-!
# The D-node successor formula at odd arguments

Every odd natural number is positive, so the general successor formula
`MetaMathlibExt.dcDNodes_succ` applies.

## References

* Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences
  27 (2024), Article 24.2.7, pp. 1–14, Lemma 20 and Theorem 21.
  <https://cs.uwaterloo.ca/journals/JIS/VOL27/Monroe/monroe2.pdf>
* Tomás M. Coronado, Mareike Fischer, Lina Herbst, Francesc Rosselló, and Kristina Wicke,
  *On the minimum value of the Colless index and the bifurcating trees that achieve it*,
  Journal of Mathematical Biology 80 (2020), pp. 1993–2054, §3.1 (the underlying recurrence).
-/

namespace MetaMathlibExt

/-- **Successor formula for the D-node count at odd arguments.** Let $\delta$ be the
divide-and-conquer D-node count and $s_1(n)$ the number of ones in the binary expansion of $n$.
For every odd natural number $n$,
$\delta(n+1) = \delta(n) + \lfloor \log_2 n \rfloor - 2 s_1(n) + 2$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Lemma 20 (`jis-2024-24.2.7-lem-20`). -/
public theorem dcDNodes_succ_of_odd (n : ℕ) (hodd : Odd n) :
    (dcDNodes (n + 1) : ℤ) = dcDNodes n + Nat.log 2 n - 2 * (Nat.digits 2 n).sum + 2 := by
  have hn : 0 < n := by
    obtain ⟨k, hk⟩ := hodd
    omega
  exact dcDNodes_succ n hn

end MetaMathlibExt
