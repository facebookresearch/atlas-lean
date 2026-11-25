/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.NoncrossingPartition.Pairing
public import MathlibExt.Probability.Distributions.Semicircle

/-!
# The semicircle moments count noncrossing pair partitions

The `n`-th moment of the semicircle distribution `σ` is the number of noncrossing pair partitions
of `{1, …, n}`. This is the form in which the semicircle law enters both the moment method for
Wigner matrices (the Wigner words of length `n + 1` are indexed by noncrossing pair partitions,
Anderson, Guionnet and Zeitouni (manuscript numbering), Proposition 2.1.11) and the free central
limit theorem (the limit
moments are `♯{π ∈ NC(n) : π a pair partition}`, Anderson, Guionnet and Zeitouni (manuscript
numbering), Lemma 5.3.32).

## Main results

* `ProbabilityTheory.integral_pow_semicircleReal_eq_card_noncrossing_pairPartition`: for every
  `n`, `∫ xⁿ dσ` is the number of noncrossing pair partitions of `Fin n`.

## References

* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  Studies in Advanced Mathematics 118, Cambridge University Press, 2010 (numbering of the authors'
  pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), §2.1.1
  (equation (2.1.4)),
  Proposition 2.1.11 and the proof of Lemma 5.3.32.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- **The moments of the semicircle law count noncrossing pair partitions**: for every `n`,
`∫ xⁿ dσ(x) = ♯{π ∈ NC(n) : every block of π has two elements}`, which is `C_{n/2}` for `n` even and
`0` for `n` odd (Anderson, Guionnet and Zeitouni, *An Introduction to Random Matrices* (manuscript
numbering), §2.1.1,
equation (2.1.4) with Proposition 2.1.11; the same count is the limit in the proof of the free
central limit theorem, Lemma 5.3.32). -/
theorem integral_pow_semicircleReal_eq_card_noncrossing_pairPartition (n : ℕ) :
    ∫ x, x ^ n ∂semicircleReal =
      Fintype.card {P : NoncrossingPartition n // NoncrossingPartition.IsPairPartition P.val} := by
  rw [NoncrossingPartition.card_noncrossing_pairPartition]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [ite_eq_left (by omega), show 2 * k / 2 = k by omega, integral_pow_two_mul_semicircleReal]
  · rw [ite_eq_right (by omega), integral_pow_two_mul_add_one_semicircleReal, Nat.cast_zero]

end ProbabilityTheory
