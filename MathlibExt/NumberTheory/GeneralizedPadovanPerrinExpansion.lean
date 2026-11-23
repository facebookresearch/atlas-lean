/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedPadovanPerrinCompanion

/-!
# Expansion in the Padovan–Perrin Fibonacci fundamental system

For `1 ≤ j ≤ s + p`, the `j`-th sequence `v^{(j)}` of the Fibonacci fundamental system of the
`([k]; p; s)`-generalized Padovan–Perrin recurrence is the solution whose first `s + p` values are
`0` except for the value `1` at index `j - 1`. This file shows that every solution `v` of the
recurrence is the combination of these sequences weighted by its initial values:
`v n = ∑_{j < s + p} v j * v^{(j+1)} n` for every `n` (`padovanPerrin_eq_sum_fundamental`).

## Proof outline

The right side is a linear combination of fundamental sequences, so it lies in the solution space
of the recurrence, and its first `s + p` values are those of `v`. Two solutions with the same first
`s + p` values are equal (`LinearRecurrence.eq_iff_eqOn_range_order`).

## Implementation notes

The theorem keeps the full name and statement it had as a wanted theorem in
`WantedExt.NumberTheory.GeneralizedPadovanPerrinModelWanted`. It assumes nothing about `p` and `s`:
for `s + p = 0` the recurrence forces every solution to vanish, and the sum is empty.

## References

* Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
  *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*,
  INTEGERS 24 (2024), Article A49.
-/

@[expose] public section

namespace MetaMathlibExt

variable {R : Type*}

/-- **Expansion in the Fibonacci fundamental system.** Let $R$ be a commutative ring, let
$k_1, k_2 \in R$ and $p, s \in \mathbb{N}$, and for $1 \le j \le s + p$ let $v^{(j)}$ be the
solution of the $([k]; p; s)$-Padovan–Perrin recurrence with $v^{(j)}(m) = 1$ if $m + 1 = j$ and
$v^{(j)}(m) = 0$ otherwise, for $0 \le m < s + p$. Then every solution $v \colon \mathbb{N} \to R$
of the recurrence satisfies, for every $n \ge 0$,
$$v(n) = \sum_{j=0}^{s+p-1} v(j)\, v^{(j+1)}(n).$$

Source: Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino,
*On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24
(2024), Article A49, Proposition 1 (`integers-2024-A49-prop-1`). -/
theorem padovanPerrin_eq_sum_fundamental [CommRing R] (k₁ k₂ : R) (p s : ℕ)
    (v : ℕ → R)
    (hv : (padovanPerrinRecurrence k₁ k₂ p s).IsSolution v) (n : ℕ) :
    v n = ∑ j ∈ Finset.range (s + p), v j * padovanPerrinFundamental k₁ k₂ p s (j + 1) n := by
  set E := padovanPerrinRecurrence k₁ k₂ p s
  -- The right side is a linear combination of fundamental sequences, hence a solution.
  have hw : E.IsSolution
      (∑ j ∈ Finset.range (s + p), v j • padovanPerrinFundamental k₁ k₂ p s (j + 1)) :=
    E.solSpace.sum_mem fun j _ =>
      E.solSpace.smul_mem _ (padovanPerrinFundamental_isSolution k₁ k₂ p s (j + 1))
  -- Both solutions have the same first `s + p` values, so they are equal.
  have heq := (E.eq_iff_eqOn_range_order _ _ hv hw).2 fun m hm => by
    have hm : m < s + p := Finset.mem_range.mp hm
    rw [Finset.sum_apply, Finset.sum_eq_single_of_mem m (Finset.mem_range.mpr hm)]
    · simp [padovanPerrinFundamental_of_lt _ _ _ _ _ _ hm]
    · intro j _ hj
      simp [padovanPerrinFundamental_of_lt _ _ _ _ _ _ hm, Ne.symm hj]
  simpa using congrFun heq n

end MetaMathlibExt
