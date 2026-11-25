/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-!
# Domb-type sums and Zagier numbers

Source: G.-R. Zhang, *Realizability of Some Combinatorial Sequences*, Journal of Integer
Sequences 27 (2024),
[`zhang9.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL27/Zhang/zhang9.tex).
-/

/-- **Domb-type sums.** For natural numbers $n$, $r$, $s$ and $t$, the Domb-type sum is the
natural number

$$D(n, r, s, t) = \sum_{k=0}^{n} \binom{n}{k}^r \binom{2k}{k}^s \binom{2(n-k)}{n-k}^t.$$

The paper uses positive $r$; the same finite formula is meaningful at $r = 0$. -/
public def dombTypeSum (n r s t : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1),
    n.choose k ^ r * (2 * k).choose k ^ s *
      (2 * (n - k)).choose (n - k) ^ t

/-- **Zagier numbers.** For a natural number $n$, the Zagier number $Z(n)$ is the Domb-type sum
$D(n, 1, 1, 1)$, that is,

$$Z(n) = \sum_{k=0}^{n} \binom{n}{k} \binom{2k}{k} \binom{2(n-k)}{n-k}.$$

These are the numbers of OEIS A081085. -/
public def zagierNumber (n : ℕ) : ℕ :=
  dombTypeSum n 1 1 1

end

end MetaMathlibExt
