/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The Schütz–Kelly binomial sum identity

Pascal's rule separates the sum into two parts. The second part starts with
`Nat.choose_zero_right`; the remaining terms are the sum with the index shifted by one.
-/

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- **Schütz–Kelly binomial sum identity.** For all natural numbers $J$, $n$ and $p$,
$$1 + \sum_{i=0}^{J} \binom{\max(n-pi,\,0)}{i+1} + \sum_{i=0}^{J-1} \binom{\max(n-pi-p,\,0)}{i+1} =
\sum_{i=0}^{J} \binom{\max(n-pi,\,0)+1}{i+1}.$$

Truncating the upper indices at $0$ makes a negative upper index give $\binom{0}{i+1} = 0$,
matching the paper's binomials. The identity is stated for all natural $J$, $n$, $p$, which
includes the value $0$ beyond the paper's positive range.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Lemma 6. -/
public theorem one_add_sum_choose_add_sum_choose (J n p : ℕ) :
    1 + (∑ i ∈ Finset.range (J + 1), (n - p * i).choose (i + 1)) +
        ∑ i ∈ Finset.range J, (n - p * i - p).choose (i + 1) =
      ∑ i ∈ Finset.range (J + 1), (n - p * i + 1).choose (i + 1) := by
  have hshift : (∑ i ∈ Finset.range (J + 1), (n - p * i).choose i) =
      (∑ i ∈ Finset.range J, (n - p * i - p).choose (i + 1)) + 1 := by
    rw [Finset.sum_range_succ' (fun i => (n - p * i).choose i) J]
    simp only [Nat.choose_zero_right, Nat.mul_succ, Nat.sub_sub]
  simp only [Nat.choose_succ_succ', Finset.sum_add_distrib, hshift]
  ac_rfl

end

end MetaMathlibExt
