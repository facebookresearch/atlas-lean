/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Series.BaseAdicMultiples

/-!
# Regrouping the multiples of three

In base three the finite sum over nonzero residues has two terms, with cofactors
`3 * n + 2` and `3 * n + 1`.
-/

namespace MetaMathlibExt

/-- **Regrouping the multiples of 3 by their 3-adic factorization.** Let $(b_m)_{m \ge 1}$ be a
sequence of complex numbers such that the family $(b_{3m})_{m \ge 1}$ is summable. Then
$$\sum_{j \ge 1,\, n \ge 1} \bigl( b_{(3n-1) 3^j} + b_{(3n-2) 3^j} \bigr) =
\sum_{m \ge 1} b_{3m},$$
where the sum on the left is an unconditional sum over the pairs $(j, n)$.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Corollary 6, deduced identity in sum form (`jis-2024-24.5.5-cor-6`). -/
public theorem tsum_threeAdic_multiples_regroup (b : ℕ → ℂ)
    (hb : Summable fun m : ℕ => b (3 * (m + 1))) :
    ∑' x : ℕ × ℕ, (b ((3 * x.2 + 2) * 3 ^ (x.1 + 1)) + b ((3 * x.2 + 1) * 3 ^ (x.1 + 1)))
      = ∑' m : ℕ, b (3 * (m + 1)) := by
  simpa [Fin.sum_univ_two, Nat.mul_succ] using
    tsum_baseAdic_multiples_regroup 3 (by decide) b hb

end MetaMathlibExt
